/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 457341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell425341184 :
    ThetaLowerSegment 425341184 425406720 (42531736180899 / 100000) (21269210947067 / 50000) := by
  exact
    packedTile32768 425341184 425406720 13 3365 20623 29 _ _ (1986839 / 100000) (993421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425406720 :
    ThetaLowerSegment 425406720 425472256 (21269210947067 / 50000) (10636241151089 / 25000) := by
  exact
    packedTile32768 425406720 425472256 13 3293 20625 29 _ _ (993427 / 50000) (1986857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425472256 :
    ThetaLowerSegment 425472256 425537792 (10636241151089 / 25000) (2659461883871 / 6250) := by
  exact
    packedTile32768 425472256 425537792 13 3234 20626 29 _ _ (198687 / 10000) (1986873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425537792 :
    ThetaLowerSegment 425537792 425603328 (2659461883871 / 6250) (42558215091911 / 100000) := by
  exact
    packedTile32768 425537792 425603328 13 3435 20628 29 _ _ (397377 / 20000) (248361 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425603328 :
    ThetaLowerSegment 425603328 425668864 (42558215091911 / 100000) (42564797691611 / 100000) := by
  exact
    packedTile32768 425603328 425668864 13 3313 20630 29 _ _ (19869 / 1000) (1986903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425668864 :
    ThetaLowerSegment 425668864 425734400 (42564797691611 / 100000) (8514278453163 / 20000) := by
  exact
    packedTile32768 425668864 425734400 13 3319 20631 29 _ _ (496729 / 25000) (1986919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425734400 :
    ThetaLowerSegment 425734400 425799936 (8514278453163 / 20000) (4257787959553 / 10000) := by
  exact
    packedTile32768 425734400 425799936 13 3265 20633 29 _ _ (1986931 / 100000) (993467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425799936 :
    ThetaLowerSegment 425799936 425865472 (4257787959553 / 10000) (42584422612001 / 100000) := by
  exact
    packedTile32768 425799936 425865472 13 3293 20634 29 _ _ (1986947 / 100000) (39739 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425865472 :
    ThetaLowerSegment 425865472 425931008 (42584422612001 / 100000) (8518190751219 / 20000) := by
  exact
    packedTile32768 425865472 425931008 13 3287 20636 29 _ _ (993481 / 50000) (397393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425931008 :
    ThetaLowerSegment 425931008 425996544 (8518190751219 / 20000) (8519506129993 / 20000) := by
  exact
    packedTile32768 425931008 425996544 13 3310 20638 29 _ _ (1986977 / 100000) (99349 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell425996544 :
    ThetaLowerSegment 425996544 426062080 (8519506129993 / 20000) (10651023421961 / 25000) := by
  exact
    packedTile32768 425996544 426062080 13 3303 20639 29 _ _ (1986993 / 100000) (496749 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426062080 :
    ThetaLowerSegment 426062080 426127616 (10651023421961 / 25000) (10652642833481 / 25000) := by
  exact
    packedTile32768 426062080 426127616 13 3260 20641 29 _ _ (62094 / 3125) (1987011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426127616 :
    ThetaLowerSegment 426127616 426193152 (10652642833481 / 25000) (42617158315169 / 100000) := by
  exact
    packedTile32768 426127616 426193152 13 3315 20642 29 _ _ (1987023 / 100000) (993513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426193152 :
    ThetaLowerSegment 426193152 426258688 (42617158315169 / 100000) (10655943292 / 25) := by
  exact
    packedTile32768 426193152 426258688 13 3329 20644 29 _ _ (1987039 / 100000) (993521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426258688 :
    ThetaLowerSegment 426258688 426324224 (10655943292 / 25) (1332192610427 / 3125) := by
  exact
    packedTile32768 426258688 426324224 13 3216 20646 29 _ _ (993527 / 50000) (1987057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426324224 :
    ThetaLowerSegment 426324224 426389760 (1332192610427 / 3125) (21318423025037 / 50000) := by
  exact
    packedTile32768 426324224 426389760 13 3363 20647 29 _ _ (198707 / 10000) (1987073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426389760 :
    ThetaLowerSegment 426389760 426455296 (21318423025037 / 50000) (42643317985919 / 100000) := by
  exact
    packedTile32768 426389760 426455296 13 3257 20649 29 _ _ (397417 / 20000) (124193 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426455296 :
    ThetaLowerSegment 426455296 426520832 (42643317985919 / 100000) (42649811828719 / 100000) := by
  exact
    packedTile32768 426455296 426520832 13 3268 20650 29 _ _ (19871 / 1000) (1987103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426520832 :
    ThetaLowerSegment 426520832 426586368 (42649811828719 / 100000) (42656377259983 / 100000) := by
  exact
    packedTile32768 426520832 426586368 13 3304 20652 29 _ _ (496779 / 25000) (1987119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426586368 :
    ThetaLowerSegment 426586368 426651904 (42656377259983 / 100000) (42662966586379 / 100000) := by
  exact
    packedTile32768 426586368 426651904 13 3316 20653 29 _ _ (1987131 / 100000) (993567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426651904 :
    ThetaLowerSegment 426651904 426717440 (42662966586379 / 100000) (8533899269627 / 20000) := by
  exact
    packedTile32768 426651904 426717440 13 3286 20655 29 _ _ (993573 / 50000) (1987149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426717440 :
    ThetaLowerSegment 426717440 426782976 (8533899269627 / 20000) (42676061931383 / 100000) := by
  exact
    packedTile32768 426717440 426782976 13 3304 20657 29 _ _ (993581 / 50000) (397433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426782976 :
    ThetaLowerSegment 426782976 426848512 (42676061931383 / 100000) (42682488461801 / 100000) := by
  exact
    packedTile32768 426782976 426848512 13 3234 20658 29 _ _ (1987177 / 100000) (99359 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426848512 :
    ThetaLowerSegment 426848512 426914048 (42682488461801 / 100000) (42688922989497 / 100000) := by
  exact
    packedTile32768 426848512 426914048 13 3238 20660 29 _ _ (248399 / 12500) (397439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426914048 :
    ThetaLowerSegment 426914048 426979584 (42688922989497 / 100000) (42695534430513 / 100000) := by
  exact
    packedTile32768 426914048 426979584 13 3327 20661 29 _ _ (248401 / 12500) (1987211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell426979584 :
    ThetaLowerSegment 426979584 427045120 (42695534430513 / 100000) (42702092266413 / 100000) := by
  exact
    packedTile32768 426979584 427045120 13 3300 20663 29 _ _ (1987223 / 100000) (993613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427045120 :
    ThetaLowerSegment 427045120 427110656 (42702092266413 / 100000) (42708701823327 / 100000) := by
  exact
    packedTile32768 427045120 427110656 13 3326 20665 29 _ _ (1987239 / 100000) (993621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427110656 :
    ThetaLowerSegment 427110656 427176192 (42708701823327 / 100000) (42715152449811 / 100000) := by
  exact
    packedTile32768 427110656 427176192 13 3246 20666 29 _ _ (993627 / 50000) (1987257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427176192 :
    ThetaLowerSegment 427176192 427241728 (42715152449811 / 100000) (10680432080733 / 25000) := by
  exact
    packedTile32768 427176192 427241728 13 3309 20668 29 _ _ (1987269 / 100000) (248409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427241728 :
    ThetaLowerSegment 427241728 427307264 (10680432080733 / 25000) (21364121321581 / 50000) := by
  exact
    packedTile32768 427241728 427307264 13 3278 20669 29 _ _ (397457 / 20000) (248411 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427307264 :
    ThetaLowerSegment 427307264 427372800 (21364121321581 / 50000) (21367420239581 / 50000) := by
  exact
    packedTile32768 427307264 427372800 13 3320 20671 29 _ _ (19873 / 1000) (1987303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427372800 :
    ThetaLowerSegment 427372800 427438336 (21367420239581 / 50000) (10685338724433 / 25000) := by
  exact
    packedTile32768 427372800 427438336 13 3278 20672 29 _ _ (397463 / 20000) (993659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427438336 :
    ThetaLowerSegment 427438336 427503872 (10685338724433 / 25000) (21373970456333 / 50000) := by
  exact
    packedTile32768 427438336 427503872 13 3314 20674 29 _ _ (1987331 / 100000) (993667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427503872 :
    ThetaLowerSegment 427503872 427569408 (21373970456333 / 50000) (21377259513963 / 50000) := by
  exact
    packedTile32768 427503872 427569408 13 3310 20676 29 _ _ (993673 / 50000) (1987349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427569408 :
    ThetaLowerSegment 427569408 427634944 (21377259513963 / 50000) (21380506861837 / 50000) := by
  exact
    packedTile32768 427569408 427634944 13 3268 20677 29 _ _ (1987361 / 100000) (496841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427634944 :
    ThetaLowerSegment 427634944 427700480 (21380506861837 / 50000) (21383817831919 / 50000) := by
  exact
    packedTile32768 427634944 427700480 13 3332 20679 29 _ _ (1987377 / 100000) (99369 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427700480 :
    ThetaLowerSegment 427700480 427766016 (21383817831919 / 50000) (21387103984591 / 50000) := by
  exact
    packedTile32768 427700480 427766016 13 3307 20680 29 _ _ (62106 / 3125) (397479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427766016 :
    ThetaLowerSegment 427766016 427831552 (21387103984591 / 50000) (42780780324131 / 100000) := by
  exact
    packedTile32768 427766016 427831552 13 3307 20682 29 _ _ (1987407 / 100000) (198741 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427831552 :
    ThetaLowerSegment 427831552 427897088 (42780780324131 / 100000) (10696824271037 / 25000) := by
  exact
    packedTile32768 427831552 427897088 13 3279 20684 29 _ _ (1987423 / 100000) (993713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427897088 :
    ThetaLowerSegment 427897088 427962624 (10696824271037 / 25000) (21396918871303 / 50000) := by
  exact
    packedTile32768 427897088 427962624 13 3291 20685 29 _ _ (993719 / 50000) (1987441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell427962624 :
    ThetaLowerSegment 427962624 428028160 (21396918871303 / 50000) (21400194193847 / 50000) := by
  exact
    packedTile32768 427962624 428028160 13 3296 20687 29 _ _ (1987453 / 100000) (62108 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428028160 :
    ThetaLowerSegment 428028160 428093696 (21400194193847 / 50000) (21403487428323 / 50000) := by
  exact
    packedTile32768 428028160 428093696 13 3314 20688 29 _ _ (496867 / 25000) (1987471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428093696 :
    ThetaLowerSegment 428093696 428159232 (21403487428323 / 50000) (4281348585423 / 10000) := by
  exact
    packedTile32768 428093696 428159232 13 3276 20690 29 _ _ (496871 / 25000) (1987487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428159232 :
    ThetaLowerSegment 428159232 428224768 (4281348585423 / 10000) (8564006932687 / 20000) := by
  exact
    packedTile32768 428159232 428224768 13 3295 20692 29 _ _ (1987499 / 100000) (993751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428224768 :
    ThetaLowerSegment 428224768 428290304 (8564006932687 / 20000) (42826670972681 / 100000) := by
  exact
    packedTile32768 428224768 428290304 13 3339 20693 29 _ _ (993757 / 50000) (1987517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428290304 :
    ThetaLowerSegment 428290304 428355840 (42826670972681 / 100000) (42833384849021 / 100000) := by
  exact
    packedTile32768 428290304 428355840 13 3378 20695 29 _ _ (198753 / 10000) (1987533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428355840 :
    ThetaLowerSegment 428355840 428421376 (42833384849021 / 100000) (10709967552089 / 25000) := by
  exact
    packedTile32768 428355840 428421376 13 3263 20696 29 _ _ (397509 / 20000) (496887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428421376 :
    ThetaLowerSegment 428421376 428486912 (10709967552089 / 25000) (10711630146029 / 25000) := by
  exact
    packedTile32768 428421376 428486912 13 3346 20698 29 _ _ (49689 / 2500) (1987563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428486912 :
    ThetaLowerSegment 428486912 428552448 (10711630146029 / 25000) (10713280827897 / 25000) := by
  exact
    packedTile32768 428486912 428552448 13 3322 20699 29 _ _ (248447 / 12500) (1987579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428552448 :
    ThetaLowerSegment 428552448 428617984 (10713280827897 / 25000) (42859624721749 / 100000) := by
  exact
    packedTile32768 428552448 428617984 13 3271 20701 29 _ _ (1987591 / 100000) (993797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428617984 :
    ThetaLowerSegment 428617984 428683520 (42859624721749 / 100000) (42866144069429 / 100000) := by
  exact
    packedTile32768 428617984 428683520 13 3280 20703 29 _ _ (993803 / 50000) (1987609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428683520 :
    ThetaLowerSegment 428683520 428749056 (42866144069429 / 100000) (10718179283019 / 25000) := by
  exact
    packedTile32768 428683520 428749056 13 3307 20704 29 _ _ (1987621 / 100000) (248453 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428749056 :
    ThetaLowerSegment 428749056 428814592 (10718179283019 / 25000) (21439604377259 / 50000) := by
  exact
    packedTile32768 428749056 428814592 13 3266 20706 29 _ _ (1987637 / 100000) (49691 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428814592 :
    ThetaLowerSegment 428814592 428880128 (21439604377259 / 50000) (21442888972189 / 50000) := by
  exact
    packedTile32768 428814592 428880128 13 3305 20707 29 _ _ (496913 / 25000) (397531 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428880128 :
    ThetaLowerSegment 428880128 428945664 (21442888972189 / 50000) (21446132844733 / 50000) := by
  exact
    packedTile32768 428880128 428945664 13 3264 20709 29 _ _ (1987667 / 100000) (198767 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell428945664 :
    ThetaLowerSegment 428945664 429011200 (21446132844733 / 50000) (42898858833977 / 100000) := by
  exact
    packedTile32768 428945664 429011200 13 3317 20711 29 _ _ (1987683 / 100000) (993843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429011200 :
    ThetaLowerSegment 429011200 429076736 (42898858833977 / 100000) (1716216809003 / 4000) := by
  exact
    packedTile32768 429011200 429076736 13 3301 20712 29 _ _ (993849 / 50000) (1987701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429076736 :
    ThetaLowerSegment 429076736 429142272 (1716216809003 / 4000) (2681997860249 / 6250) := by
  exact
    packedTile32768 429076736 429142272 13 3293 20714 29 _ _ (1987713 / 100000) (496929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429142272 :
    ThetaLowerSegment 429142272 429207808 (2681997860249 / 6250) (536481118591 / 1250) := by
  exact
    packedTile32768 429142272 429207808 13 3282 20715 29 _ _ (124233 / 6250) (1987731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429207808 :
    ThetaLowerSegment 429207808 429273344 (536481118591 / 1250) (2682810471561 / 6250) := by
  exact
    packedTile32768 429207808 429273344 13 3259 20717 29 _ _ (62117 / 3125) (1987747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429273344 :
    ThetaLowerSegment 429273344 429338880 (2682810471561 / 6250) (42931453602593 / 100000) := by
  exact
    packedTile32768 429273344 429338880 13 3263 20718 29 _ _ (1987759 / 100000) (993881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429338880 :
    ThetaLowerSegment 429338880 429404416 (42931453602593 / 100000) (8587593905153 / 20000) := by
  exact
    packedTile32768 429338880 429404416 13 3278 20720 29 _ _ (993887 / 50000) (1987777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429404416 :
    ThetaLowerSegment 429404416 429469952 (8587593905153 / 20000) (1342016724776 / 3125) := by
  exact
    packedTile32768 429404416 429469952 13 3303 20722 29 _ _ (1987789 / 100000) (124237 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429469952 :
    ThetaLowerSegment 429469952 429535488 (1342016724776 / 3125) (42951061156647 / 100000) := by
  exact
    packedTile32768 429469952 429535488 13 3283 20723 29 _ _ (397561 / 20000) (62119 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429535488 :
    ThetaLowerSegment 429535488 429601024 (42951061156647 / 100000) (42957778000427 / 100000) := by
  exact
    packedTile32768 429535488 429601024 13 3379 20725 29 _ _ (99391 / 5000) (1987823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429601024 :
    ThetaLowerSegment 429601024 429666560 (42957778000427 / 100000) (42964310026237 / 100000) := by
  exact
    packedTile32768 429601024 429666560 13 3286 20726 29 _ _ (397567 / 20000) (993919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429666560 :
    ThetaLowerSegment 429666560 429732096 (42964310026237 / 100000) (268567601641 / 625) := by
  exact
    packedTile32768 429666560 429732096 13 3273 20728 29 _ _ (1987851 / 100000) (993927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429732096 :
    ThetaLowerSegment 429732096 429797632 (268567601641 / 625) (5372164076081 / 12500) := by
  exact
    packedTile32768 429732096 429797632 13 3268 20729 29 _ _ (993933 / 50000) (1987869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429797632 :
    ThetaLowerSegment 429797632 429863168 (5372164076081 / 12500) (21491954198903 / 50000) := by
  exact
    packedTile32768 429797632 429863168 13 3318 20731 29 _ _ (1987881 / 100000) (496971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429863168 :
    ThetaLowerSegment 429863168 429928704 (21491954198903 / 50000) (4299042670879 / 10000) := by
  exact
    packedTile32768 429863168 429928704 13 3279 20733 29 _ _ (248487 / 12500) (1987899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429928704 :
    ThetaLowerSegment 429928704 429994240 (4299042670879 / 10000) (21498545093231 / 50000) := by
  exact
    packedTile32768 429928704 429994240 13 3352 20734 29 _ _ (1987911 / 100000) (993957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell429994240 :
    ThetaLowerSegment 429994240 430059776 (21498545093231 / 50000) (8600729671527 / 20000) := by
  exact
    packedTile32768 429994240 430059776 13 3299 20736 29 _ _ (1987927 / 100000) (198793 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430059776 :
    ThetaLowerSegment 430059776 430125312 (8600729671527 / 20000) (43010125072671 / 100000) := by
  exact
    packedTile32768 430059776 430125312 13 3258 20737 29 _ _ (993971 / 50000) (397589 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430125312 :
    ThetaLowerSegment 430125312 430190848 (43010125072671 / 100000) (172067115059 / 400) := by
  exact
    packedTile32768 430125312 430190848 13 3347 20739 29 _ _ (1987957 / 100000) (49699 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430190848 :
    ThetaLowerSegment 430190848 430256384 (172067115059 / 400) (21511701343727 / 50000) := by
  exact
    packedTile32768 430190848 430256384 13 3332 20741 29 _ _ (496993 / 25000) (79519 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430256384 :
    ThetaLowerSegment 430256384 430321920 (21511701343727 / 50000) (21514905980383 / 50000) := by
  exact
    packedTile32768 430256384 430321920 13 3224 20742 29 _ _ (496997 / 25000) (1987991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430321920 :
    ThetaLowerSegment 430321920 430387456 (21514905980383 / 50000) (43036247126477 / 100000) := by
  exact
    packedTile32768 430321920 430387456 13 3237 20744 29 _ _ (1988003 / 100000) (994003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430387456 :
    ThetaLowerSegment 430387456 430452992 (43036247126477 / 100000) (43042853310291 / 100000) := by
  exact
    packedTile32768 430387456 430452992 13 3323 20745 29 _ _ (994009 / 50000) (1988021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430452992 :
    ThetaLowerSegment 430452992 430518528 (43042853310291 / 100000) (5381169023771 / 12500) := by
  exact
    packedTile32768 430452992 430518528 13 3269 20747 29 _ _ (1988033 / 100000) (497009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430518528 :
    ThetaLowerSegment 430518528 430584064 (5381169023771 / 12500) (8611183743203 / 20000) := by
  exact
    packedTile32768 430518528 430584064 13 3303 20748 29 _ _ (1988049 / 100000) (497013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430584064 :
    ThetaLowerSegment 430584064 430649600 (8611183743203 / 20000) (43062375947887 / 100000) := by
  exact
    packedTile32768 430584064 430649600 13 3248 20750 29 _ _ (62127 / 3125) (1988067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430649600 :
    ThetaLowerSegment 430649600 430715136 (43062375947887 / 100000) (43069032036379 / 100000) := by
  exact
    packedTile32768 430649600 430715136 13 3348 20752 29 _ _ (1988079 / 100000) (994041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430715136 :
    ThetaLowerSegment 430715136 430780672 (43069032036379 / 100000) (43075622567989 / 100000) := by
  exact
    packedTile32768 430715136 430780672 13 3315 20753 29 _ _ (994047 / 50000) (1988097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430780672 :
    ThetaLowerSegment 430780672 430846208 (43075622567989 / 100000) (2154105090761 / 5000) := by
  exact
    packedTile32768 430780672 430846208 13 3259 20755 29 _ _ (1988109 / 100000) (124257 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430846208 :
    ThetaLowerSegment 430846208 430911744 (2154105090761 / 5000) (8617761552169 / 20000) := by
  exact
    packedTile32768 430846208 430911744 13 3373 20756 29 _ _ (3181 / 160) (62129 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430911744 :
    ThetaLowerSegment 430911744 430977280 (8617761552169 / 20000) (8619069748289 / 20000) := by
  exact
    packedTile32768 430911744 430977280 13 3290 20758 29 _ _ (99407 / 5000) (1988143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell430977280 :
    ThetaLowerSegment 430977280 431042816 (8619069748289 / 20000) (8620395450043 / 20000) := by
  exact
    packedTile32768 430977280 431042816 13 3334 20759 29 _ _ (397631 / 20000) (994079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431042816 :
    ThetaLowerSegment 431042816 431108352 (8620395450043 / 20000) (8621697701393 / 20000) := by
  exact
    packedTile32768 431042816 431108352 13 3275 20761 29 _ _ (198817 / 10000) (1988173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431108352 :
    ThetaLowerSegment 431108352 431173888 (8621697701393 / 20000) (8623007915967 / 20000) := by
  exact
    packedTile32768 431108352 431173888 13 3295 20763 29 _ _ (994093 / 50000) (1988189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431173888 :
    ThetaLowerSegment 431173888 431239424 (8623007915967 / 20000) (21560803303869 / 50000) := by
  exact
    packedTile32768 431173888 431239424 13 3303 20764 29 _ _ (1988201 / 100000) (497051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431239424 :
    ThetaLowerSegment 431239424 431304960 (21560803303869 / 50000) (21564091813133 / 50000) := by
  exact
    packedTile32768 431239424 431304960 13 3308 20766 29 _ _ (248527 / 12500) (1988219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431304960 :
    ThetaLowerSegment 431304960 431370496 (21564091813133 / 50000) (1078365339133 / 2500) := by
  exact
    packedTile32768 431304960 431370496 13 3234 20767 29 _ _ (1988231 / 100000) (994117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431370496 :
    ThetaLowerSegment 431370496 431436032 (1078365339133 / 2500) (215705675061 / 500) := by
  exact
    packedTile32768 431370496 431436032 13 3280 20769 29 _ _ (994123 / 50000) (1988249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431436032 :
    ThetaLowerSegment 431436032 431501568 (215705675061 / 500) (43147678379151 / 100000) := by
  exact
    packedTile32768 431436032 431501568 13 3291 20771 29 _ _ (1988261 / 100000) (248533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431501568 :
    ThetaLowerSegment 431501568 431567104 (43147678379151 / 100000) (43154259576021 / 100000) := by
  exact
    packedTile32768 431501568 431567104 13 3310 20772 29 _ _ (1988277 / 100000) (49707 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431567104 :
    ThetaLowerSegment 431567104 431632640 (43154259576021 / 100000) (43160628075297 / 100000) := by
  exact
    packedTile32768 431567104 431632640 13 3203 20774 29 _ _ (497073 / 25000) (397659 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431632640 :
    ThetaLowerSegment 431632640 431698176 (43160628075297 / 100000) (8633455394781 / 20000) := by
  exact
    packedTile32768 431632640 431698176 13 3344 20775 29 _ _ (1988307 / 100000) (198831 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431698176 :
    ThetaLowerSegment 431698176 431763712 (8633455394781 / 20000) (43173941829249 / 100000) := by
  exact
    packedTile32768 431698176 431763712 13 3352 20777 29 _ _ (994161 / 50000) (79533 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431763712 :
    ThetaLowerSegment 431763712 431829248 (43173941829249 / 100000) (1727219974587 / 4000) := by
  exact
    packedTile32768 431763712 431829248 13 3298 20778 29 _ _ (1988337 / 100000) (99417 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431829248 :
    ThetaLowerSegment 431829248 431894784 (1727219974587 / 4000) (10796751811011 / 25000) := by
  exact
    packedTile32768 431829248 431894784 13 3273 20780 29 _ _ (1988353 / 100000) (497089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431894784 :
    ThetaLowerSegment 431894784 431960320 (10796751811011 / 25000) (10798364377459 / 25000) := by
  exact
    packedTile32768 431894784 431960320 13 3244 20782 29 _ _ (124273 / 6250) (1988371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell431960320 :
    ThetaLowerSegment 431960320 432025856 (10798364377459 / 25000) (5400002396717 / 12500) := by
  exact
    packedTile32768 431960320 432025856 13 3300 20783 29 _ _ (1988383 / 100000) (994193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432025856 :
    ThetaLowerSegment 432025856 432091392 (5400002396717 / 12500) (864131339367 / 2000) := by
  exact
    packedTile32768 432025856 432091392 13 3293 20785 29 _ _ (994199 / 50000) (1988401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432091392 :
    ThetaLowerSegment 432091392 432156928 (864131339367 / 2000) (43213067090447 / 100000) := by
  exact
    packedTile32768 432091392 432156928 13 3269 20786 29 _ _ (1988413 / 100000) (62138 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432156928 :
    ThetaLowerSegment 432156928 432222464 (43213067090447 / 100000) (43219559307867 / 100000) := by
  exact
    packedTile32768 432156928 432222464 13 3265 20788 29 _ _ (497107 / 25000) (1988431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432222464 :
    ThetaLowerSegment 432222464 432288000 (43219559307867 / 100000) (43226107253959 / 100000) := by
  exact
    packedTile32768 432222464 432288000 13 3293 20789 29 _ _ (497111 / 25000) (1988447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432288000 :
    ThetaLowerSegment 432288000 432353536 (43226107253959 / 100000) (43232625422561 / 100000) := by
  exact
    packedTile32768 432288000 432353536 13 3278 20791 29 _ _ (1988459 / 100000) (994231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432353536 :
    ThetaLowerSegment 432353536 432419072 (43232625422561 / 100000) (43239231133189 / 100000) := by
  exact
    packedTile32768 432353536 432419072 13 3322 20793 29 _ _ (994237 / 50000) (1988477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432419072 :
    ThetaLowerSegment 432419072 432484608 (43239231133189 / 100000) (5405725883289 / 12500) := by
  exact
    packedTile32768 432419072 432484608 13 3307 20794 29 _ _ (1988489 / 100000) (497123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432484608 :
    ThetaLowerSegment 432484608 432550144 (5405725883289 / 12500) (5406552106701 / 12500) := by
  exact
    packedTile32768 432484608 432550144 13 3324 20796 29 _ _ (248563 / 12500) (1988507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432550144 :
    ThetaLowerSegment 432550144 432615680 (5406552106701 / 12500) (21629463632407 / 50000) := by
  exact
    packedTile32768 432550144 432615680 13 3274 20797 29 _ _ (1988519 / 100000) (994261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432615680 :
    ThetaLowerSegment 432615680 432681216 (21629463632407 / 50000) (21632780508787 / 50000) := by
  exact
    packedTile32768 432615680 432681216 13 3336 20799 29 _ _ (397707 / 20000) (994269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432681216 :
    ThetaLowerSegment 432681216 432746752 (21632780508787 / 50000) (21636007925437 / 50000) := by
  exact
    packedTile32768 432681216 432746752 13 3246 20800 29 _ _ (39771 / 2000) (1988553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432746752 :
    ThetaLowerSegment 432746752 432812288 (21636007925437 / 50000) (2704910386499 / 6250) := by
  exact
    packedTile32768 432746752 432812288 13 3294 20802 29 _ _ (397713 / 20000) (248571 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432812288 :
    ThetaLowerSegment 432812288 432877824 (2704910386499 / 6250) (5410651502293 / 12500) := by
  exact
    packedTile32768 432812288 432877824 13 3342 20804 29 _ _ (99429 / 5000) (1988583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432877824 :
    ThetaLowerSegment 432877824 432943360 (5410651502293 / 12500) (43291688872259 / 100000) := by
  exact
    packedTile32768 432877824 432943360 13 3257 20805 29 _ _ (397719 / 20000) (994299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell432943360 :
    ThetaLowerSegment 432943360 433008896 (43291688872259 / 100000) (43298187649739 / 100000) := by
  exact
    packedTile32768 432943360 433008896 13 3268 20807 29 _ _ (198861 / 10000) (1988613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433008896 :
    ThetaLowerSegment 433008896 433074432 (43298187649739 / 100000) (21652354175557 / 50000) := by
  exact
    packedTile32768 433008896 433074432 13 3279 20808 29 _ _ (15909 / 800) (497157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433074432 :
    ThetaLowerSegment 433074432 433139968 (21652354175557 / 50000) (21655607592233 / 50000) := by
  exact
    packedTile32768 433074432 433139968 13 3272 20810 29 _ _ (1988641 / 100000) (497161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433139968 :
    ThetaLowerSegment 433139968 433205504 (21655607592233 / 50000) (4331784536357 / 10000) := by
  exact
    packedTile32768 433139968 433205504 13 3334 20812 29 _ _ (124291 / 6250) (1988659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433205504 :
    ThetaLowerSegment 433205504 433271040 (4331784536357 / 10000) (8664867674877 / 20000) := by
  exact
    packedTile32768 433205504 433271040 13 3265 20813 29 _ _ (1988671 / 100000) (994337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433271040 :
    ThetaLowerSegment 433271040 433336576 (8664867674877 / 20000) (43330922913731 / 100000) := by
  exact
    packedTile32768 433271040 433336576 13 3311 20815 29 _ _ (994343 / 50000) (1988689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433336576 :
    ThetaLowerSegment 433336576 433402112 (43330922913731 / 100000) (1354296239404 / 3125) := by
  exact
    packedTile32768 433336576 433402112 13 3297 20816 29 _ _ (1988701 / 100000) (62147 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433402112 :
    ThetaLowerSegment 433402112 433467648 (1354296239404 / 3125) (10835976300581 / 25000) := by
  exact
    packedTile32768 433402112 433467648 13 3231 20818 29 _ _ (497179 / 25000) (1988719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433467648 :
    ThetaLowerSegment 433467648 433533184 (10835976300581 / 25000) (43350422273811 / 100000) := by
  exact
    packedTile32768 433467648 433533184 13 3277 20819 29 _ _ (1988731 / 100000) (994367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433533184 :
    ThetaLowerSegment 433533184 433598720 (43350422273811 / 100000) (43356877743327 / 100000) := by
  exact
    packedTile32768 433533184 433598720 13 3246 20821 29 _ _ (994373 / 50000) (1988749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433598720 :
    ThetaLowerSegment 433598720 433664256 (43356877743327 / 100000) (43363384972591 / 100000) := by
  exact
    packedTile32768 433598720 433664256 13 3272 20823 29 _ _ (994381 / 50000) (397753 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433664256 :
    ThetaLowerSegment 433664256 433729792 (43363384972591 / 100000) (10842519301799 / 25000) := by
  exact
    packedTile32768 433664256 433729792 13 3365 20824 29 _ _ (1988777 / 100000) (99439 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433729792 :
    ThetaLowerSegment 433729792 433795328 (10842519301799 / 25000) (10844167015971 / 25000) := by
  exact
    packedTile32768 433729792 433795328 13 3314 20826 29 _ _ (248599 / 12500) (397759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433795328 :
    ThetaLowerSegment 433795328 433860864 (10844167015971 / 25000) (8676663329137 / 20000) := by
  exact
    packedTile32768 433795328 433860864 13 3343 20827 29 _ _ (1988807 / 100000) (198881 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433860864 :
    ThetaLowerSegment 433860864 433926400 (8676663329137 / 20000) (43389847937133 / 100000) := by
  exact
    packedTile32768 433860864 433926400 13 3284 20829 29 _ _ (994411 / 50000) (79553 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433926400 :
    ThetaLowerSegment 433926400 433991936 (43389847937133 / 100000) (43396315635057 / 100000) := by
  exact
    packedTile32768 433926400 433991936 13 3252 20830 29 _ _ (1988837 / 100000) (49721 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell433991936 :
    ThetaLowerSegment 433991936 434057472 (43396315635057 / 100000) (43402922601401 / 100000) := by
  exact
    packedTile32768 433991936 434057472 13 3322 20832 29 _ _ (497213 / 25000) (397771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434057472 :
    ThetaLowerSegment 434057472 434123008 (43402922601401 / 100000) (10852365996241 / 25000) := by
  exact
    packedTile32768 434057472 434123008 13 3289 20834 29 _ _ (1988867 / 100000) (198887 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434123008 :
    ThetaLowerSegment 434123008 434188544 (10852365996241 / 25000) (542700788693 / 1250) := by
  exact
    packedTile32768 434123008 434188544 13 3318 20835 29 _ _ (994441 / 50000) (397777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434188544 :
    ThetaLowerSegment 434188544 434254080 (542700788693 / 1250) (43422660266789 / 100000) := by
  exact
    packedTile32768 434188544 434254080 13 3317 20837 29 _ _ (1988897 / 100000) (19889 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434254080 :
    ThetaLowerSegment 434254080 434319616 (43422660266789 / 100000) (43429251524471 / 100000) := by
  exact
    packedTile32768 434254080 434319616 13 3314 20838 29 _ _ (1988913 / 100000) (497229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434319616 :
    ThetaLowerSegment 434319616 434385152 (43429251524471 / 100000) (43435775208311 / 100000) := by
  exact
    packedTile32768 434319616 434385152 13 3280 20840 29 _ _ (62154 / 3125) (1988931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434385152 :
    ThetaLowerSegment 434385152 434450688 (43435775208311 / 100000) (43442462034677 / 100000) := by
  exact
    packedTile32768 434385152 434450688 13 3362 20841 29 _ _ (1988943 / 100000) (994473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434450688 :
    ThetaLowerSegment 434450688 434516224 (43442462034677 / 100000) (43449125043977 / 100000) := by
  exact
    packedTile32768 434450688 434516224 13 3350 20843 29 _ _ (994479 / 50000) (1988961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434516224 :
    ThetaLowerSegment 434516224 434581760 (43449125043977 / 100000) (43455708544607 / 100000) := by
  exact
    packedTile32768 434516224 434581760 13 3310 20845 29 _ _ (1988973 / 100000) (124311 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434581760 :
    ThetaLowerSegment 434581760 434647296 (43455708544607 / 100000) (8692442904871 / 20000) := by
  exact
    packedTile32768 434581760 434647296 13 3271 20846 29 _ _ (497247 / 25000) (1988991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434647296 :
    ThetaLowerSegment 434647296 434712832 (8692442904871 / 20000) (869374172383 / 2000) := by
  exact
    packedTile32768 434647296 434712832 13 3265 20848 29 _ _ (1989003 / 100000) (994503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434712832 :
    ThetaLowerSegment 434712832 434778368 (869374172383 / 2000) (21737648123383 / 50000) := by
  exact
    packedTile32768 434712832 434778368 13 3312 20849 29 _ _ (994509 / 50000) (1989021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434778368 :
    ThetaLowerSegment 434778368 434843904 (21737648123383 / 50000) (43481838176303 / 100000) := by
  exact
    packedTile32768 434778368 434843904 13 3289 20851 29 _ _ (1989033 / 100000) (497259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434843904 :
    ThetaLowerSegment 434843904 434909440 (43481838176303 / 100000) (43488322472783 / 100000) := by
  exact
    packedTile32768 434843904 434909440 13 3260 20852 29 _ _ (248631 / 12500) (1989051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434909440 :
    ThetaLowerSegment 434909440 434974976 (43488322472783 / 100000) (1739798160353 / 4000) := by
  exact
    packedTile32768 434909440 434974976 13 3334 20854 29 _ _ (1989063 / 100000) (994533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell434974976 :
    ThetaLowerSegment 434974976 435040512 (1739798160353 / 4000) (43501531889771 / 100000) := by
  exact
    packedTile32768 434974976 435040512 13 3307 20856 29 _ _ (994539 / 50000) (1989081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435040512 :
    ThetaLowerSegment 435040512 435106048 (43501531889771 / 100000) (43507976551091 / 100000) := by
  exact
    packedTile32768 435040512 435106048 13 3240 20857 29 _ _ (1989093 / 100000) (248637 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435106048 :
    ThetaLowerSegment 435106048 435171584 (43507976551091 / 100000) (1359828710331 / 3125) := by
  exact
    packedTile32768 435106048 435171584 13 3289 20859 29 _ _ (1989109 / 100000) (248639 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435171584 :
    ThetaLowerSegment 435171584 435237120 (1359828710331 / 3125) (272006419652 / 625) := by
  exact
    packedTile32768 435171584 435237120 13 3272 20860 29 _ _ (497281 / 25000) (1989127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435237120 :
    ThetaLowerSegment 435237120 435302656 (272006419652 / 625) (43527517704877 / 100000) := by
  exact
    packedTile32768 435237120 435302656 13 3263 20862 29 _ _ (1989139 / 100000) (994571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435302656 :
    ThetaLowerSegment 435302656 435368192 (43527517704877 / 100000) (43534077934769 / 100000) := by
  exact
    packedTile32768 435302656 435368192 13 3298 20863 29 _ _ (994577 / 50000) (1989157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435368192 :
    ThetaLowerSegment 435368192 435433728 (43534077934769 / 100000) (43540514885653 / 100000) := by
  exact
    packedTile32768 435368192 435433728 13 3236 20865 29 _ _ (1989169 / 100000) (497293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435433728 :
    ThetaLowerSegment 435433728 435499264 (43540514885653 / 100000) (8709432945553 / 20000) := by
  exact
    packedTile32768 435433728 435499264 13 3343 20867 29 _ _ (62162 / 3125) (1989187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435499264 :
    ThetaLowerSegment 435499264 435564800 (8709432945553 / 20000) (43553701235679 / 100000) := by
  exact
    packedTile32768 435499264 435564800 13 3286 20868 29 _ _ (1989199 / 100000) (994601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435564800 :
    ThetaLowerSegment 435564800 435630336 (43553701235679 / 100000) (43560301447731 / 100000) := by
  exact
    packedTile32768 435564800 435630336 13 3318 20870 29 _ _ (994607 / 50000) (1989217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435630336 :
    ThetaLowerSegment 435630336 435695872 (43560301447731 / 100000) (8713383524677 / 20000) := by
  exact
    packedTile32768 435630336 435695872 13 3326 20871 29 _ _ (1989229 / 100000) (124327 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435695872 :
    ThetaLowerSegment 435695872 435761408 (8713383524677 / 20000) (43573478150097 / 100000) := by
  exact
    packedTile32768 435695872 435761408 13 3298 20873 29 _ _ (497311 / 25000) (1989247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435761408 :
    ThetaLowerSegment 435761408 435826944 (43573478150097 / 100000) (43579883564077 / 100000) := by
  exact
    packedTile32768 435761408 435826944 13 3220 20874 29 _ _ (1989259 / 100000) (994631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435826944 :
    ThetaLowerSegment 435826944 435892480 (43579883564077 / 100000) (43586495910853 / 100000) := by
  exact
    packedTile32768 435826944 435892480 13 3324 20876 29 _ _ (994637 / 50000) (1989277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435892480 :
    ThetaLowerSegment 435892480 435958016 (43586495910853 / 100000) (8718619274351 / 20000) := by
  exact
    packedTile32768 435892480 435958016 13 3318 20878 29 _ _ (1989289 / 100000) (497323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell435958016 :
    ThetaLowerSegment 435958016 436023552 (8718619274351 / 20000) (43599659085651 / 100000) := by
  exact
    packedTile32768 435958016 436023552 13 3299 20879 29 _ _ (248663 / 12500) (1989307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436023552 :
    ThetaLowerSegment 436023552 436089088 (43599659085651 / 100000) (21803057212903 / 50000) := by
  exact
    packedTile32768 436023552 436089088 13 3245 20881 29 _ _ (1989319 / 100000) (994661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436089088 :
    ThetaLowerSegment 436089088 436154624 (21803057212903 / 50000) (1362894671708 / 3125) := by
  exact
    packedTile32768 436089088 436154624 13 3275 20882 29 _ _ (994667 / 50000) (1989337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436154624 :
    ThetaLowerSegment 436154624 436220160 (1362894671708 / 3125) (1744766261949 / 4000) := by
  exact
    packedTile32768 436154624 436220160 13 3281 20884 29 _ _ (1989349 / 100000) (248669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436220160 :
    ThetaLowerSegment 436220160 436285696 (1744766261949 / 4000) (8725156226169 / 20000) := by
  exact
    packedTile32768 436220160 436285696 13 3330 20885 29 _ _ (497341 / 25000) (1989367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436285696 :
    ThetaLowerSegment 436285696 436351232 (8725156226169 / 20000) (43632457486769 / 100000) := by
  exact
    packedTile32768 436285696 436351232 13 3356 20887 29 _ _ (1989379 / 100000) (994691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436351232 :
    ThetaLowerSegment 436351232 436416768 (43632457486769 / 100000) (43639024476363 / 100000) := by
  exact
    packedTile32768 436351232 436416768 13 3301 20889 29 _ _ (994697 / 50000) (1989397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436416768 :
    ThetaLowerSegment 436416768 436482304 (43639024476363 / 100000) (21822781831873 / 50000) := by
  exact
    packedTile32768 436416768 436482304 13 3287 20890 29 _ _ (1989409 / 100000) (497353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436482304 :
    ThetaLowerSegment 436482304 436547840 (21822781831873 / 50000) (21826114117073 / 50000) := by
  exact
    packedTile32768 436482304 436547840 13 3350 20892 29 _ _ (124339 / 6250) (1989427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436547840 :
    ThetaLowerSegment 436547840 436613376 (21826114117073 / 50000) (8731739180067 / 20000) := by
  exact
    packedTile32768 436547840 436613376 13 3251 20893 29 _ _ (1989439 / 100000) (994721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436613376 :
    ThetaLowerSegment 436613376 436678912 (8731739180067 / 20000) (43665207383277 / 100000) := by
  exact
    packedTile32768 436613376 436678912 13 3273 20895 29 _ _ (994727 / 50000) (1989457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436678912 :
    ThetaLowerSegment 436678912 436744448 (43665207383277 / 100000) (43671728862659 / 100000) := by
  exact
    packedTile32768 436678912 436744448 13 3278 20896 29 _ _ (1989469 / 100000) (62171 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436744448 :
    ThetaLowerSegment 436744448 436809984 (43671728862659 / 100000) (43678369760251 / 100000) := by
  exact
    packedTile32768 436744448 436809984 13 3338 20898 29 _ _ (497371 / 25000) (1989487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436809984 :
    ThetaLowerSegment 436809984 436875520 (43678369760251 / 100000) (21842464569227 / 50000) := by
  exact
    packedTile32768 436809984 436875520 13 3297 20899 29 _ _ (1989499 / 100000) (994751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436875520 :
    ThetaLowerSegment 436875520 436941056 (21842464569227 / 50000) (21845725382673 / 50000) := by
  exact
    packedTile32768 436875520 436941056 13 3278 20901 29 _ _ (994757 / 50000) (1989517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell436941056 :
    ThetaLowerSegment 436941056 437006592 (21845725382673 / 50000) (8739579765767 / 20000) := by
  exact
    packedTile32768 436941056 437006592 13 3241 20903 29 _ _ (1989529 / 100000) (497383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437006592 :
    ThetaLowerSegment 437006592 437072128 (8739579765767 / 20000) (43704472282211 / 100000) := by
  exact
    packedTile32768 437006592 437072128 13 3304 20904 29 _ _ (248693 / 12500) (1989547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437072128 :
    ThetaLowerSegment 437072128 437137664 (43704472282211 / 100000) (1365968377748 / 3125) := by
  exact
    packedTile32768 437072128 437137664 13 3275 20906 29 _ _ (1989559 / 100000) (994781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437137664 :
    ThetaLowerSegment 437137664 437203200 (1365968377748 / 3125) (10929385436173 / 25000) := by
  exact
    packedTile32768 437137664 437203200 13 3294 20907 29 _ _ (994787 / 50000) (1989577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437203200 :
    ThetaLowerSegment 437203200 437268736 (10929385436173 / 25000) (43724033773599 / 100000) := by
  exact
    packedTile32768 437203200 437268736 13 3263 20909 29 _ _ (1989589 / 100000) (248699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437268736 :
    ThetaLowerSegment 437268736 437334272 (43724033773599 / 100000) (8746133422667 / 20000) := by
  exact
    packedTile32768 437268736 437334272 13 3334 20910 29 _ _ (497401 / 25000) (1989607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437334272 :
    ThetaLowerSegment 437334272 437399808 (8746133422667 / 20000) (21868629360541 / 50000) := by
  exact
    packedTile32768 437334272 437399808 13 3313 20912 29 _ _ (1989619 / 100000) (994811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437399808 :
    ThetaLowerSegment 437399808 437465344 (21868629360541 / 50000) (10935940708657 / 25000) := by
  exact
    packedTile32768 437399808 437465344 13 3269 20914 29 _ _ (994817 / 50000) (1989637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437465344 :
    ThetaLowerSegment 437465344 437530880 (10935940708657 / 25000) (21875138472727 / 50000) := by
  exact
    packedTile32768 437465344 437530880 13 3274 20915 29 _ _ (1989649 / 100000) (497413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437530880 :
    ThetaLowerSegment 437530880 437596416 (21875138472727 / 50000) (21878376650887 / 50000) := by
  exact
    packedTile32768 437530880 437596416 13 3255 20917 29 _ _ (62177 / 3125) (1989667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437596416 :
    ThetaLowerSegment 437596416 437661952 (21878376650887 / 50000) (109408268261 / 250) := by
  exact
    packedTile32768 437596416 437661952 13 3294 20918 29 _ _ (1989679 / 100000) (994841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437661952 :
    ThetaLowerSegment 437661952 437727488 (109408268261 / 250) (1094248822059 / 2500) := by
  exact
    packedTile32768 437661952 437727488 13 3340 20920 29 _ _ (994847 / 50000) (1989697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437727488 :
    ThetaLowerSegment 437727488 437793024 (1094248822059 / 2500) (10944173504113 / 25000) := by
  exact
    packedTile32768 437727488 437793024 13 3388 20921 29 _ _ (1989709 / 100000) (124357 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437793024 :
    ThetaLowerSegment 437793024 437858560 (10944173504113 / 25000) (10945765283313 / 25000) := by
  exact
    packedTile32768 437793024 437858560 13 3200 20923 29 _ _ (497431 / 25000) (1989727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437858560 :
    ThetaLowerSegment 437858560 437924096 (10945765283313 / 25000) (43789577528477 / 100000) := by
  exact
    packedTile32768 437858560 437924096 13 3275 20925 29 _ _ (1989739 / 100000) (994871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437924096 :
    ThetaLowerSegment 437924096 437989632 (43789577528477 / 100000) (43796185501511 / 100000) := by
  exact
    packedTile32768 437924096 437989632 13 3321 20926 29 _ _ (994877 / 50000) (1989757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell437989632 :
    ThetaLowerSegment 437989632 438055168 (43796185501511 / 100000) (5475337251931 / 12500) := by
  exact
    packedTile32768 437989632 438055168 13 3273 20928 29 _ _ (1989769 / 100000) (497443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438055168 :
    ThetaLowerSegment 438055168 438120704 (5475337251931 / 12500) (1095232502969 / 2500) := by
  exact
    packedTile32768 438055168 438120704 13 3318 20929 29 _ _ (248723 / 12500) (1989787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438120704 :
    ThetaLowerSegment 438120704 438186240 (1095232502969 / 2500) (43815880384053 / 100000) := by
  exact
    packedTile32768 438120704 438186240 13 3307 20931 29 _ _ (1989799 / 100000) (994901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438186240 :
    ThetaLowerSegment 438186240 438251776 (43815880384053 / 100000) (8764486568311 / 20000) := by
  exact
    packedTile32768 438186240 438251776 13 3293 20932 29 _ _ (994907 / 50000) (1989817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438251776 :
    ThetaLowerSegment 438251776 438317312 (8764486568311 / 20000) (10957226438823 / 25000) := by
  exact
    packedTile32768 438251776 438317312 13 3253 20934 29 _ _ (1989829 / 100000) (248729 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438317312 :
    ThetaLowerSegment 438317312 438382848 (10957226438823 / 25000) (10958876019499 / 25000) := by
  exact
    packedTile32768 438317312 438382848 13 3316 20936 29 _ _ (497461 / 25000) (1989847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438382848 :
    ThetaLowerSegment 438382848 438448384 (10958876019499 / 25000) (10960499744443 / 25000) := by
  exact
    packedTile32768 438382848 438448384 13 3264 20937 29 _ _ (1989859 / 100000) (994931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438448384 :
    ThetaLowerSegment 438448384 438513920 (10960499744443 / 25000) (10962143380367 / 25000) := by
  exact
    packedTile32768 438448384 438513920 13 3304 20939 29 _ _ (994937 / 50000) (1989877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438513920 :
    ThetaLowerSegment 438513920 438579456 (10962143380367 / 25000) (8771041164301 / 20000) := by
  exact
    packedTile32768 438513920 438579456 13 3333 20940 29 _ _ (1989889 / 100000) (497473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438579456 :
    ThetaLowerSegment 438579456 438644992 (8771041164301 / 20000) (43861800363361 / 100000) := by
  exact
    packedTile32768 438579456 438644992 13 3314 20942 29 _ _ (124369 / 6250) (1989907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438644992 :
    ThetaLowerSegment 438644992 438710528 (43861800363361 / 100000) (43868462612173 / 100000) := by
  exact
    packedTile32768 438644992 438710528 13 3348 20943 29 _ _ (1989919 / 100000) (994961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438710528 :
    ThetaLowerSegment 438710528 438776064 (43868462612173 / 100000) (43874941837277 / 100000) := by
  exact
    packedTile32768 438710528 438776064 13 3256 20945 29 _ _ (994967 / 50000) (1989937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438776064 :
    ThetaLowerSegment 438776064 438841600 (43874941837277 / 100000) (43881506675729 / 100000) := by
  exact
    packedTile32768 438776064 438841600 13 3299 20946 29 _ _ (497487 / 25000) (1989951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438841600 :
    ThetaLowerSegment 438841600 438907136 (43881506675729 / 100000) (43888049674073 / 100000) := by
  exact
    packedTile32768 438841600 438907136 13 3288 20948 29 _ _ (1989963 / 100000) (994983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438907136 :
    ThetaLowerSegment 438907136 438972672 (43888049674073 / 100000) (43894712120417 / 100000) := by
  exact
    packedTile32768 438907136 438972672 13 3348 20950 29 _ _ (994989 / 50000) (1989981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell438972672 :
    ThetaLowerSegment 438972672 439038208 (43894712120417 / 100000) (5487658643419 / 12500) := by
  exact
    packedTile32768 438972672 439038208 13 3295 20951 29 _ _ (1989993 / 100000) (497499 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439038208 :
    ThetaLowerSegment 439038208 439103744 (5487658643419 / 12500) (2744240880239 / 6250) := by
  exact
    packedTile32768 439038208 439103744 13 3309 20953 29 _ _ (248751 / 12500) (1990011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439103744 :
    ThetaLowerSegment 439103744 439169280 (2744240880239 / 6250) (43914387329333 / 100000) := by
  exact
    packedTile32768 439103744 439169280 13 3283 20954 29 _ _ (1990023 / 100000) (995013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439169280 :
    ThetaLowerSegment 439169280 439234816 (43914387329333 / 100000) (43920821122187 / 100000) := by
  exact
    packedTile32768 439169280 439234816 13 3233 20956 29 _ _ (995019 / 50000) (1990041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439234816 :
    ThetaLowerSegment 439234816 439300352 (43920821122187 / 100000) (21963653352457 / 50000) := by
  exact
    packedTile32768 439234816 439300352 13 3259 20957 29 _ _ (1990053 / 100000) (248757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439300352 :
    ThetaLowerSegment 439300352 439365888 (21963653352457 / 50000) (21966911093773 / 50000) := by
  exact
    packedTile32768 439300352 439365888 13 3274 20959 29 _ _ (497517 / 25000) (1990071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439365888 :
    ThetaLowerSegment 439365888 439431424 (21966911093773 / 50000) (43940323788707 / 100000) := by
  exact
    packedTile32768 439365888 439431424 13 3267 20961 29 _ _ (1990083 / 100000) (995043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439431424 :
    ThetaLowerSegment 439431424 439496960 (43940323788707 / 100000) (8789370660049 / 20000) := by
  exact
    packedTile32768 439431424 439496960 13 3281 20962 29 _ _ (995049 / 50000) (1990101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439496960 :
    ThetaLowerSegment 439496960 439562496 (8789370660049 / 20000) (21976782975697 / 50000) := by
  exact
    packedTile32768 439496960 439562496 13 3373 20964 29 _ _ (1990113 / 100000) (497529 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439562496 :
    ThetaLowerSegment 439562496 439628032 (21976782975697 / 50000) (21980111464777 / 50000) := by
  exact
    packedTile32768 439562496 439628032 13 3345 20965 29 _ _ (124383 / 6250) (1990131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439628032 :
    ThetaLowerSegment 439628032 439693568 (21980111464777 / 50000) (21983365346947 / 50000) := by
  exact
    packedTile32768 439628032 439693568 13 3270 20967 29 _ _ (995071 / 50000) (398029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439693568 :
    ThetaLowerSegment 439693568 439759104 (21983365346947 / 50000) (21986621243799 / 50000) := by
  exact
    packedTile32768 439693568 439759104 13 3272 20968 29 _ _ (1990157 / 100000) (24877 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439759104 :
    ThetaLowerSegment 439759104 439824640 (21986621243799 / 50000) (21989888111137 / 50000) := by
  exact
    packedTile32768 439759104 439824640 13 3283 20970 29 _ _ (497543 / 25000) (79607 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439824640 :
    ThetaLowerSegment 439824640 439890176 (21989888111137 / 50000) (8797269961987 / 20000) := by
  exact
    packedTile32768 439824640 439890176 13 3303 20971 29 _ _ (1990187 / 100000) (199019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439890176 :
    ThetaLowerSegment 439890176 439955712 (8797269961987 / 20000) (43992794084011 / 100000) := by
  exact
    packedTile32768 439890176 439955712 13 3238 20973 29 _ _ (995101 / 50000) (398041 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell439955712 :
    ThetaLowerSegment 439955712 440021248 (43992794084011 / 100000) (8799845293071 / 20000) := by
  exact
    packedTile32768 439955712 440021248 13 3232 20975 29 _ _ (1990217 / 100000) (99511 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440021248 :
    ThetaLowerSegment 440021248 440086784 (8799845293071 / 20000) (44005796221187 / 100000) := by
  exact
    packedTile32768 440021248 440086784 13 3301 20976 29 _ _ (248779 / 12500) (398047 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440086784 :
    ThetaLowerSegment 440086784 440152320 (44005796221187 / 100000) (44012379958263 / 100000) := by
  exact
    packedTile32768 440086784 440152320 13 3308 20978 29 _ _ (1990247 / 100000) (7961 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440152320 :
    ThetaLowerSegment 440152320 440217856 (44012379958263 / 100000) (44018937871553 / 100000) := by
  exact
    packedTile32768 440152320 440217856 13 3295 20979 29 _ _ (995131 / 50000) (398053 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440217856 :
    ThetaLowerSegment 440217856 440283392 (44018937871553 / 100000) (2201272403381 / 5000) := by
  exact
    packedTile32768 440217856 440283392 13 3271 20981 29 _ _ (1990277 / 100000) (49757 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440283392 :
    ThetaLowerSegment 440283392 440348928 (2201272403381 / 5000) (44031974231809 / 100000) := by
  exact
    packedTile32768 440283392 440348928 13 3279 20982 29 _ _ (1990291 / 100000) (995147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440348928 :
    ThetaLowerSegment 440348928 440414464 (44031974231809 / 100000) (8807710836689 / 20000) := by
  exact
    packedTile32768 440348928 440414464 13 3306 20984 29 _ _ (995153 / 50000) (1990309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440414464 :
    ThetaLowerSegment 440414464 440480000 (8807710836689 / 20000) (22022589981027 / 50000) := by
  exact
    packedTile32768 440414464 440480000 13 3329 20986 29 _ _ (1990321 / 100000) (497581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440480000 :
    ThetaLowerSegment 440480000 440545536 (22022589981027 / 50000) (22025885977443 / 50000) := by
  exact
    packedTile32768 440480000 440545536 13 3312 20987 29 _ _ (62198 / 3125) (1990339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440545536 :
    ThetaLowerSegment 440545536 440611072 (22025885977443 / 50000) (44058369968451 / 100000) := by
  exact
    packedTile32768 440545536 440611072 13 3315 20989 29 _ _ (1990351 / 100000) (995177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440611072 :
    ThetaLowerSegment 440611072 440676608 (44058369968451 / 100000) (44064948128081 / 100000) := by
  exact
    packedTile32768 440611072 440676608 13 3305 20990 29 _ _ (995183 / 50000) (1990369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440676608 :
    ThetaLowerSegment 440676608 440742144 (44064948128081 / 100000) (44071639789003 / 100000) := by
  exact
    packedTile32768 440676608 440742144 13 3362 20992 29 _ _ (1990381 / 100000) (124399 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440742144 :
    ThetaLowerSegment 440742144 440807680 (44071639789003 / 100000) (44078210086199 / 100000) := by
  exact
    packedTile32768 440742144 440807680 13 3301 20993 29 _ _ (497599 / 25000) (1990399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440807680 :
    ThetaLowerSegment 440807680 440873216 (44078210086199 / 100000) (44084722707719 / 100000) := by
  exact
    packedTile32768 440807680 440873216 13 3272 20995 29 _ _ (199041 / 10000) (1990413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440873216 :
    ThetaLowerSegment 440873216 440938752 (44084722707719 / 100000) (22045676406697 / 50000) := by
  exact
    packedTile32768 440873216 440938752 13 3331 20996 29 _ _ (79617 / 4000) (497607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell440938752 :
    ThetaLowerSegment 440938752 441004288 (22045676406697 / 50000) (22048933761757 / 50000) := by
  exact
    packedTile32768 440938752 441004288 13 3273 20998 29 _ _ (49761 / 2500) (1990443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441004288 :
    ThetaLowerSegment 441004288 441069824 (22048933761757 / 50000) (5513054005513 / 12500) := by
  exact
    packedTile32768 441004288 441069824 13 3298 21000 29 _ _ (398091 / 20000) (995229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441069824 :
    ThetaLowerSegment 441069824 441135360 (5513054005513 / 12500) (22055459492917 / 50000) := by
  exact
    packedTile32768 441069824 441135360 13 3259 21001 29 _ _ (199047 / 10000) (1990473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441135360 :
    ThetaLowerSegment 441135360 441200896 (22055459492917 / 50000) (44117541329429 / 100000) := by
  exact
    packedTile32768 441135360 441200896 13 3327 21003 29 _ _ (398097 / 20000) (248811 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441200896 :
    ThetaLowerSegment 441200896 441266432 (44117541329429 / 100000) (44124121922429 / 100000) := by
  exact
    packedTile32768 441200896 441266432 13 3306 21004 29 _ _ (3981 / 200) (1990503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441266432 :
    ThetaLowerSegment 441266432 441331968 (44124121922429 / 100000) (44130704552227 / 100000) := by
  exact
    packedTile32768 441266432 441331968 13 3307 21006 29 _ _ (995257 / 50000) (1990517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441331968 :
    ThetaLowerSegment 441331968 441397504 (44130704552227 / 100000) (8827455455797 / 20000) := by
  exact
    packedTile32768 441331968 441397504 13 3302 21007 29 _ _ (1990529 / 100000) (497633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441397504 :
    ThetaLowerSegment 441397504 441463040 (8827455455797 / 20000) (44143858017449 / 100000) := by
  exact
    packedTile32768 441397504 441463040 13 3306 21009 29 _ _ (124409 / 6250) (1990547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441463040 :
    ThetaLowerSegment 441463040 441528576 (44143858017449 / 100000) (5518798630191 / 12500) := by
  exact
    packedTile32768 441463040 441528576 13 3281 21011 29 _ _ (1990559 / 100000) (995281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441528576 :
    ThetaLowerSegment 441528576 441594112 (5518798630191 / 12500) (55196018268 / 125) := by
  exact
    packedTile32768 441528576 441594112 13 3228 21012 29 _ _ (995287 / 50000) (1990577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441594112 :
    ThetaLowerSegment 441594112 441659648 (55196018268 / 125) (44163477115783 / 100000) := by
  exact
    packedTile32768 441594112 441659648 13 3347 21014 29 _ _ (1990589 / 100000) (62206 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441659648 :
    ThetaLowerSegment 441659648 441725184 (44163477115783 / 100000) (44169970466031 / 100000) := by
  exact
    packedTile32768 441659648 441725184 13 3262 21015 29 _ _ (497651 / 25000) (1990607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441725184 :
    ThetaLowerSegment 441725184 441790720 (44169970466031 / 100000) (44176587280263 / 100000) := by
  exact
    packedTile32768 441725184 441790720 13 3324 21017 29 _ _ (995309 / 50000) (1990621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441790720 :
    ThetaLowerSegment 441790720 441856256 (44176587280263 / 100000) (44183096650173 / 100000) := by
  exact
    packedTile32768 441790720 441856256 13 3270 21018 29 _ _ (1990633 / 100000) (497659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441856256 :
    ThetaLowerSegment 441856256 441921792 (44183096650173 / 100000) (44189590143949 / 100000) := by
  exact
    packedTile32768 441856256 441921792 13 3262 21020 29 _ _ (248831 / 12500) (1990651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441921792 :
    ThetaLowerSegment 441921792 441987328 (44189590143949 / 100000) (22098102558549 / 50000) := by
  exact
    packedTile32768 441921792 441987328 13 3323 21021 29 _ _ (1990663 / 100000) (995333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell441987328 :
    ThetaLowerSegment 441987328 442052864 (22098102558549 / 50000) (22101403102673 / 50000) := by
  exact
    packedTile32768 441987328 442052864 13 3316 21023 29 _ _ (995339 / 50000) (1990681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442052864 :
    ThetaLowerSegment 442052864 442118400 (22101403102673 / 50000) (1381543108551 / 3125) := by
  exact
    packedTile32768 442052864 442118400 13 3302 21025 29 _ _ (1990693 / 100000) (248837 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442118400 :
    ThetaLowerSegment 442118400 442183936 (1381543108551 / 3125) (4421597667663 / 10000) := by
  exact
    packedTile32768 442118400 442183936 13 3314 21026 29 _ _ (1990707 / 100000) (199071 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442183936 :
    ThetaLowerSegment 442183936 442249472 (4421597667663 / 10000) (22111275020337 / 50000) := by
  exact
    packedTile32768 442183936 442249472 13 3302 21028 29 _ _ (995361 / 50000) (79629 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442249472 :
    ThetaLowerSegment 442249472 442315008 (22111275020337 / 50000) (11057290817247 / 25000) := by
  exact
    packedTile32768 442249472 442315008 13 3322 21029 29 _ _ (1990737 / 100000) (99537 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442315008 :
    ThetaLowerSegment 442315008 442380544 (11057290817247 / 25000) (11058946625223 / 25000) := by
  exact
    packedTile32768 442315008 442380544 13 3327 21031 29 _ _ (62211 / 3125) (398151 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442380544 :
    ThetaLowerSegment 442380544 442446080 (11058946625223 / 25000) (11060563128027 / 25000) := by
  exact
    packedTile32768 442380544 442446080 13 3248 21032 29 _ _ (1990767 / 100000) (199077 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442446080 :
    ThetaLowerSegment 442446080 442511616 (11060563128027 / 25000) (44248732504263 / 100000) := by
  exact
    packedTile32768 442446080 442511616 13 3255 21034 29 _ _ (1990781 / 100000) (62212 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442511616 :
    ThetaLowerSegment 442511616 442577152 (44248732504263 / 100000) (44255477321111 / 100000) := by
  exact
    packedTile32768 442511616 442577152 13 3388 21035 29 _ _ (497699 / 25000) (1990799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442577152 :
    ThetaLowerSegment 442577152 442642688 (44255477321111 / 100000) (44261919585507 / 100000) := by
  exact
    packedTile32768 442577152 442642688 13 3236 21037 29 _ _ (1990811 / 100000) (995407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442642688 :
    ThetaLowerSegment 442642688 442708224 (44261919585507 / 100000) (44268560981043 / 100000) := by
  exact
    packedTile32768 442642688 442708224 13 3336 21039 29 _ _ (995413 / 50000) (1990829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442708224 :
    ThetaLowerSegment 442708224 442773760 (44268560981043 / 100000) (4427514469223 / 10000) := by
  exact
    packedTile32768 442708224 442773760 13 3307 21040 29 _ _ (1990841 / 100000) (497711 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442773760 :
    ThetaLowerSegment 442773760 442839296 (4427514469223 / 10000) (8856352060679 / 20000) := by
  exact
    packedTile32768 442773760 442839296 13 3323 21042 29 _ _ (398171 / 20000) (995429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442839296 :
    ThetaLowerSegment 442839296 442904832 (8856352060679 / 20000) (8857657275051 / 20000) := by
  exact
    packedTile32768 442839296 442904832 13 3278 21043 29 _ _ (199087 / 10000) (1990873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442904832 :
    ThetaLowerSegment 442904832 442970368 (8857657275051 / 20000) (8858982408107 / 20000) := by
  exact
    packedTile32768 442904832 442970368 13 3328 21045 29 _ _ (398177 / 20000) (248861 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell442970368 :
    ThetaLowerSegment 442970368 443035904 (8858982408107 / 20000) (8860285651247 / 20000) := by
  exact
    packedTile32768 442970368 443035904 13 3273 21046 29 _ _ (19909 / 1000) (1990903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443035904 :
    ThetaLowerSegment 443035904 443101440 (8860285651247 / 20000) (8861603636977 / 20000) := by
  exact
    packedTile32768 443035904 443101440 13 3310 21048 29 _ _ (398183 / 20000) (995459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443101440 :
    ThetaLowerSegment 443101440 443166976 (8861603636977 / 20000) (22157307066331 / 50000) := by
  exact
    packedTile32768 443101440 443166976 13 3313 21049 29 _ _ (1990929 / 100000) (497733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443166976 :
    ThetaLowerSegment 443166976 443232512 (22157307066331 / 50000) (22160541354859 / 50000) := by
  exact
    packedTile32768 443166976 443232512 13 3249 21051 29 _ _ (62217 / 3125) (1990947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443232512 :
    ThetaLowerSegment 443232512 443298048 (22160541354859 / 50000) (1773107946659 / 4000) := by
  exact
    packedTile32768 443232512 443298048 13 3323 21053 29 _ _ (1990959 / 100000) (995481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443298048 :
    ThetaLowerSegment 443298048 443363584 (1773107946659 / 4000) (44334264898727 / 100000) := by
  exact
    packedTile32768 443298048 443363584 13 3298 21054 29 _ _ (995487 / 50000) (1990977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443363584 :
    ThetaLowerSegment 443363584 443429120 (44334264898727 / 100000) (44340803306603 / 100000) := by
  exact
    packedTile32768 443363584 443429120 13 3284 21056 29 _ _ (1990989 / 100000) (124437 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443429120 :
    ThetaLowerSegment 443429120 443494656 (44340803306603 / 100000) (4434751099571 / 10000) := by
  exact
    packedTile32768 443429120 443494656 13 3369 21057 29 _ _ (1991003 / 100000) (995503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443494656 :
    ThetaLowerSegment 443494656 443560192 (4434751099571 / 10000) (4435400171439 / 10000) := by
  exact
    packedTile32768 443494656 443560192 13 3260 21059 29 _ _ (995509 / 50000) (1991021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443560192 :
    ThetaLowerSegment 443560192 443625728 (4435400171439 / 10000) (2772532522277 / 6250) := by
  exact
    packedTile32768 443560192 443625728 13 3274 21060 29 _ _ (1991033 / 100000) (497759 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443625728 :
    ThetaLowerSegment 443625728 443691264 (2772532522277 / 6250) (5545871170113 / 12500) := by
  exact
    packedTile32768 443625728 443691264 13 3239 21062 29 _ _ (248881 / 12500) (1991051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443691264 :
    ThetaLowerSegment 443691264 443756800 (5545871170113 / 12500) (1109339890381 / 2500) := by
  exact
    packedTile32768 443691264 443756800 13 3328 21063 29 _ _ (995531 / 50000) (398213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443756800 :
    ThetaLowerSegment 443756800 443822336 (1109339890381 / 2500) (22190037289899 / 50000) := by
  exact
    packedTile32768 443756800 443822336 13 3254 21065 29 _ _ (1991077 / 100000) (49777 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443822336 :
    ThetaLowerSegment 443822336 443887872 (22190037289899 / 50000) (22193275801037 / 50000) := by
  exact
    packedTile32768 443822336 443887872 13 3253 21067 29 _ _ (497773 / 25000) (398219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443887872 :
    ThetaLowerSegment 443887872 443953408 (22193275801037 / 50000) (11098277577133 / 25000) := by
  exact
    packedTile32768 443887872 443953408 13 3294 21068 29 _ _ (1991107 / 100000) (199111 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell443953408 :
    ThetaLowerSegment 443953408 444018944 (11098277577133 / 25000) (11099914279417 / 25000) := by
  exact
    packedTile32768 443953408 444018944 13 3288 21070 29 _ _ (995561 / 50000) (15929 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444018944 :
    ThetaLowerSegment 444018944 444084480 (11099914279417 / 25000) (11101548504289 / 25000) := by
  exact
    packedTile32768 444018944 444084480 13 3283 21071 29 _ _ (62223 / 3125) (1991139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444084480 :
    ThetaLowerSegment 444084480 444150016 (11101548504289 / 25000) (44412726983587 / 100000) := by
  exact
    packedTile32768 444084480 444150016 13 3281 21073 29 _ _ (1991151 / 100000) (995577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444150016 :
    ThetaLowerSegment 444150016 444215552 (44412726983587 / 100000) (8883864743309 / 20000) := by
  exact
    packedTile32768 444150016 444215552 13 3313 21074 29 _ _ (995583 / 50000) (1991169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444215552 :
    ThetaLowerSegment 444215552 444281088 (8883864743309 / 20000) (44425771160623 / 100000) := by
  exact
    packedTile32768 444215552 444281088 13 3238 21076 29 _ _ (1991181 / 100000) (124449 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444281088 :
    ThetaLowerSegment 444281088 444346624 (44425771160623 / 100000) (44432266438713 / 100000) := by
  exact
    packedTile32768 444281088 444346624 13 3262 21077 29 _ _ (398239 / 20000) (995599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444346624 :
    ThetaLowerSegment 444346624 444412160 (44432266438713 / 100000) (44438887211963 / 100000) := by
  exact
    packedTile32768 444346624 444412160 13 3325 21079 29 _ _ (199121 / 10000) (1991213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444412160 :
    ThetaLowerSegment 444412160 444477696 (44438887211963 / 100000) (11111382982447 / 25000) := by
  exact
    packedTile32768 444412160 444477696 13 3337 21081 29 _ _ (79649 / 4000) (497807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444477696 :
    ThetaLowerSegment 444477696 444543232 (11111382982447 / 25000) (11113031729167 / 25000) := by
  exact
    packedTile32768 444477696 444543232 13 3312 21082 29 _ _ (49781 / 2500) (1991243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444543232 :
    ThetaLowerSegment 444543232 444608768 (11113031729167 / 25000) (22229338075537 / 50000) := by
  exact
    packedTile32768 444543232 444608768 13 3289 21084 29 _ _ (995627 / 50000) (1991257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444608768 :
    ThetaLowerSegment 444608768 444674304 (22229338075537 / 50000) (8893045086963 / 20000) := by
  exact
    packedTile32768 444608768 444674304 13 3289 21085 29 _ _ (1991269 / 100000) (248909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444674304 :
    ThetaLowerSegment 444674304 444739840 (8893045086963 / 20000) (44471760828903 / 100000) := by
  exact
    packedTile32768 444674304 444739840 13 3282 21087 29 _ _ (497821 / 25000) (1991287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444739840 :
    ThetaLowerSegment 444739840 444805376 (44471760828903 / 100000) (2779895632769 / 6250) := by
  exact
    packedTile32768 444739840 444805376 13 3299 21088 29 _ _ (1991299 / 100000) (995651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444805376 :
    ThetaLowerSegment 444805376 444870912 (2779895632769 / 6250) (44484947257403 / 100000) := by
  exact
    packedTile32768 444805376 444870912 13 3323 21090 29 _ _ (1991313 / 100000) (497829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444870912 :
    ThetaLowerSegment 444870912 444936448 (44484947257403 / 100000) (44491409116763 / 100000) := by
  exact
    packedTile32768 444870912 444936448 13 3245 21091 29 _ _ (62229 / 3125) (1991331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell444936448 :
    ThetaLowerSegment 444936448 445001984 (44491409116763 / 100000) (44497960635233 / 100000) := by
  exact
    packedTile32768 444936448 445001984 13 3290 21093 29 _ _ (1991343 / 100000) (995673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445001984 :
    ThetaLowerSegment 445001984 445067520 (44497960635233 / 100000) (44504440510911 / 100000) := by
  exact
    packedTile32768 445001984 445067520 13 3254 21095 29 _ _ (1991357 / 100000) (12446 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445067520 :
    ThetaLowerSegment 445067520 445133056 (44504440510911 / 100000) (44511000090279 / 100000) := by
  exact
    packedTile32768 445067520 445133056 13 3294 21096 29 _ _ (497843 / 25000) (15931 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445133056 :
    ThetaLowerSegment 445133056 445198592 (44511000090279 / 100000) (44517551753509 / 100000) := by
  exact
    packedTile32768 445133056 445198592 13 3290 21098 29 _ _ (1991387 / 100000) (199139 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445198592 :
    ThetaLowerSegment 445198592 445264128 (44517551753509 / 100000) (44524031775617 / 100000) := by
  exact
    packedTile32768 445198592 445264128 13 3254 21099 29 _ _ (995701 / 50000) (398281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445264128 :
    ThetaLowerSegment 445264128 445329664 (44524031775617 / 100000) (44530597474169 / 100000) := by
  exact
    packedTile32768 445264128 445329664 13 3297 21101 29 _ _ (248927 / 12500) (1991419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445329664 :
    ThetaLowerSegment 445329664 445395200 (44530597474169 / 100000) (11134260934079 / 25000) := by
  exact
    packedTile32768 445329664 445395200 13 3237 21102 29 _ _ (1991431 / 100000) (995717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445395200 :
    ThetaLowerSegment 445395200 445460736 (11134260934079 / 25000) (22271790826767 / 50000) := by
  exact
    packedTile32768 445395200 445460736 13 3283 21104 29 _ _ (995723 / 50000) (1991449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445460736 :
    ThetaLowerSegment 445460736 445526272 (22271790826767 / 50000) (22275039893757 / 50000) := by
  exact
    packedTile32768 445460736 445526272 13 3263 21105 29 _ _ (99573 / 5000) (1991463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445526272 :
    ThetaLowerSegment 445526272 445591808 (22275039893757 / 50000) (44556713390739 / 100000) := by
  exact
    packedTile32768 445526272 445591808 13 3331 21107 29 _ _ (79659 / 4000) (995739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445591808 :
    ThetaLowerSegment 445591808 445657344 (44556713390739 / 100000) (44563327129029 / 100000) := by
  exact
    packedTile32768 445591808 445657344 13 3321 21109 29 _ _ (199149 / 10000) (1991493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445657344 :
    ThetaLowerSegment 445657344 445722880 (44563327129029 / 100000) (44569835367369 / 100000) := by
  exact
    packedTile32768 445657344 445722880 13 3268 21110 29 _ _ (398301 / 20000) (497877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445722880 :
    ThetaLowerSegment 445722880 445788416 (44569835367369 / 100000) (278603404968 / 625) := by
  exact
    packedTile32768 445722880 445788416 13 3369 21112 29 _ _ (1991519 / 100000) (995761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445788416 :
    ThetaLowerSegment 445788416 445853952 (278603404968 / 625) (445829774497 / 1000) := by
  exact
    packedTile32768 445788416 445853952 13 3230 21113 29 _ _ (995767 / 50000) (1991537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445853952 :
    ThetaLowerSegment 445853952 445919488 (445829774497 / 1000) (11147349550919 / 25000) := by
  exact
    packedTile32768 445853952 445919488 13 3224 21115 29 _ _ (1991549 / 100000) (62236 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445919488 :
    ThetaLowerSegment 445919488 445985024 (11147349550919 / 25000) (44595920572501 / 100000) := by
  exact
    packedTile32768 445919488 445985024 13 3275 21116 29 _ _ (1991563 / 100000) (995783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell445985024 :
    ThetaLowerSegment 445985024 446050560 (44595920572501 / 100000) (8920497759349 / 20000) := by
  exact
    packedTile32768 445985024 446050560 13 3298 21118 29 _ _ (995789 / 50000) (1991581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446050560 :
    ThetaLowerSegment 446050560 446116096 (8920497759349 / 20000) (1394036829926 / 3125) := by
  exact
    packedTile32768 446050560 446116096 13 3359 21119 29 _ _ (1991593 / 100000) (497899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446116096 :
    ThetaLowerSegment 446116096 446181632 (1394036829926 / 3125) (44615677171273 / 100000) := by
  exact
    packedTile32768 446116096 446181632 13 3263 21121 29 _ _ (1991607 / 100000) (199161 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446181632 :
    ThetaLowerSegment 446181632 446247168 (44615677171273 / 100000) (44622235582519 / 100000) := by
  exact
    packedTile32768 446181632 446247168 13 3293 21123 29 _ _ (995811 / 50000) (15933 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446247168 :
    ThetaLowerSegment 446247168 446312704 (44622235582519 / 100000) (44628792051523 / 100000) := by
  exact
    packedTile32768 446247168 446312704 13 3292 21124 29 _ _ (1991637 / 100000) (49791 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446312704 :
    ThetaLowerSegment 446312704 446378240 (44628792051523 / 100000) (44635444169203 / 100000) := by
  exact
    packedTile32768 446312704 446378240 13 3340 21126 29 _ _ (497913 / 25000) (398331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446378240 :
    ThetaLowerSegment 446378240 446443776 (44635444169203 / 100000) (44642028616999 / 100000) := by
  exact
    packedTile32768 446378240 446443776 13 3306 21127 29 _ _ (995833 / 50000) (1991669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446443776 :
    ThetaLowerSegment 446443776 446509312 (44642028616999 / 100000) (44648549380593 / 100000) := by
  exact
    packedTile32768 446443776 446509312 13 3274 21129 29 _ _ (1991681 / 100000) (497921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446509312 :
    ThetaLowerSegment 446509312 446574848 (44648549380593 / 100000) (44655207620321 / 100000) := by
  exact
    packedTile32768 446509312 446574848 13 3343 21130 29 _ _ (124481 / 6250) (1991699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446574848 :
    ThetaLowerSegment 446574848 446640384 (44655207620321 / 100000) (44661730470571 / 100000) := by
  exact
    packedTile32768 446574848 446640384 13 3275 21132 29 _ _ (199171 / 10000) (1991713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446640384 :
    ThetaLowerSegment 446640384 446705920 (44661730470571 / 100000) (11167052387999 / 25000) := by
  exact
    packedTile32768 446640384 446705920 13 3253 21133 29 _ _ (79669 / 4000) (124483 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446705920 :
    ThetaLowerSegment 446705920 446771456 (11167052387999 / 25000) (5584348035717 / 12500) := by
  exact
    packedTile32768 446705920 446771456 13 3301 21135 29 _ _ (99587 / 5000) (1991743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446771456 :
    ThetaLowerSegment 446771456 446836992 (5584348035717 / 12500) (22340645673027 / 50000) := by
  exact
    packedTile32768 446771456 446836992 13 3267 21136 29 _ _ (995877 / 50000) (1991757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446836992 :
    ThetaLowerSegment 446836992 446902528 (22340645673027 / 50000) (22343967943719 / 50000) := by
  exact
    packedTile32768 446836992 446902528 13 3336 21138 29 _ _ (1991769 / 100000) (497943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446902528 :
    ThetaLowerSegment 446902528 446968064 (22343967943719 / 50000) (22347201605043 / 50000) := by
  exact
    packedTile32768 446902528 446968064 13 3247 21140 29 _ _ (248973 / 12500) (1991787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell446968064 :
    ThetaLowerSegment 446968064 447033600 (22347201605043 / 50000) (22350462178369 / 50000) := by
  exact
    packedTile32768 446968064 447033600 13 3274 21141 29 _ _ (995899 / 50000) (1991801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447033600 :
    ThetaLowerSegment 447033600 447099136 (22350462178369 / 50000) (2235376261251 / 5000) := by
  exact
    packedTile32768 447033600 447099136 13 3314 21143 29 _ _ (1991813 / 100000) (248977 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447099136 :
    ThetaLowerSegment 447099136 447164672 (2235376261251 / 5000) (11178506637903 / 25000) := by
  exact
    packedTile32768 447099136 447164672 13 3264 21144 29 _ _ (497957 / 25000) (1991831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447164672 :
    ThetaLowerSegment 447164672 447230208 (11178506637903 / 25000) (22360245039451 / 50000) := by
  exact
    packedTile32768 447164672 447230208 13 3245 21146 29 _ _ (995921 / 50000) (398369 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447230208 :
    ThetaLowerSegment 447230208 447295744 (22360245039451 / 50000) (22363523636073 / 50000) := by
  exact
    packedTile32768 447230208 447295744 13 3292 21147 29 _ _ (1991857 / 100000) (99593 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447295744 :
    ThetaLowerSegment 447295744 447361280 (22363523636073 / 50000) (22366773375241 / 50000) := by
  exact
    packedTile32768 447295744 447361280 13 3263 21149 29 _ _ (62246 / 3125) (3187 / 160) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447361280 :
    ThetaLowerSegment 447361280 447426816 (22366773375241 / 50000) (11185057382003 / 25000) := by
  exact
    packedTile32768 447361280 447426816 13 3355 21150 29 _ _ (995943 / 50000) (1991889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447426816 :
    ThetaLowerSegment 447426816 447492352 (11185057382003 / 25000) (44746912355867 / 100000) := by
  exact
    packedTile32768 447426816 447492352 13 3355 21152 29 _ _ (1991901 / 100000) (62247 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447492352 :
    ThetaLowerSegment 447492352 447557888 (44746912355867 / 100000) (44753447832263 / 100000) := by
  exact
    packedTile32768 447492352 447557888 13 3281 21154 29 _ _ (497979 / 25000) (1991919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447557888 :
    ThetaLowerSegment 447557888 447623424 (44753447832263 / 100000) (44760061039863 / 100000) := by
  exact
    packedTile32768 447557888 447623424 13 3320 21155 29 _ _ (199193 / 10000) (1991933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447623424 :
    ThetaLowerSegment 447623424 447688960 (44760061039863 / 100000) (44766610555023 / 100000) := by
  exact
    packedTile32768 447623424 447688960 13 3288 21157 29 _ _ (398389 / 20000) (497987 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447688960 :
    ThetaLowerSegment 447688960 447754496 (44766610555023 / 100000) (44773271665919 / 100000) := by
  exact
    packedTile32768 447688960 447754496 13 3344 21158 29 _ _ (1991959 / 100000) (995981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447754496 :
    ThetaLowerSegment 447754496 447820032 (44773271665919 / 100000) (44779745581419 / 100000) := by
  exact
    packedTile32768 447754496 447820032 13 3250 21160 29 _ _ (995987 / 50000) (1991977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447820032 :
    ThetaLowerSegment 447820032 447885568 (44779745581419 / 100000) (4478631715313 / 10000) := by
  exact
    packedTile32768 447820032 447885568 13 3299 21161 29 _ _ (1991989 / 100000) (248999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447885568 :
    ThetaLowerSegment 447885568 447951104 (4478631715313 / 10000) (2239649518159 / 5000) := by
  exact
    packedTile32768 447885568 447951104 13 3350 21163 29 _ _ (1992003 / 100000) (996003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell447951104 :
    ThetaLowerSegment 447951104 448016640 (2239649518159 / 5000) (1399984757191 / 3125) := by
  exact
    packedTile32768 447951104 448016640 13 3274 21164 29 _ _ (996009 / 50000) (1992021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448016640 :
    ThetaLowerSegment 448016640 448082176 (1399984757191 / 3125) (22403013089011 / 50000) := by
  exact
    packedTile32768 448016640 448082176 13 3270 21166 29 _ _ (1992033 / 100000) (498009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448082176 :
    ThetaLowerSegment 448082176 448147712 (22403013089011 / 50000) (11203148987257 / 25000) := by
  exact
    packedTile32768 448082176 448147712 13 3298 21167 29 _ _ (1992047 / 100000) (39841 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448147712 :
    ThetaLowerSegment 448147712 448213248 (11203148987257 / 25000) (22409571928411 / 50000) := by
  exact
    packedTile32768 448147712 448213248 13 3287 21169 29 _ _ (996031 / 50000) (398413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448213248 :
    ThetaLowerSegment 448213248 448278784 (22409571928411 / 50000) (22412829968709 / 50000) := by
  exact
    packedTile32768 448213248 448278784 13 3271 21171 29 _ _ (498019 / 25000) (1992079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448278784 :
    ThetaLowerSegment 448278784 448344320 (22412829968709 / 50000) (44832235829809 / 100000) := by
  exact
    packedTile32768 448278784 448344320 13 3301 21172 29 _ _ (1992091 / 100000) (996047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448344320 :
    ThetaLowerSegment 448344320 448409856 (44832235829809 / 100000) (44838809779609 / 100000) := by
  exact
    packedTile32768 448344320 448409856 13 3300 21174 29 _ _ (996053 / 50000) (1992109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448409856 :
    ThetaLowerSegment 448409856 448475392 (44838809779609 / 100000) (44845294130209 / 100000) := by
  exact
    packedTile32768 448409856 448475392 13 3255 21175 29 _ _ (49803 / 2500) (1992123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448475392 :
    ThetaLowerSegment 448475392 448540928 (44845294130209 / 100000) (44851935908299 / 100000) := by
  exact
    packedTile32768 448475392 448540928 13 3334 21177 29 _ _ (398427 / 20000) (996069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448540928 :
    ThetaLowerSegment 448540928 448606464 (44851935908299 / 100000) (44858474144599 / 100000) := by
  exact
    packedTile32768 448540928 448606464 13 3282 21178 29 _ _ (39843 / 2000) (1992153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448606464 :
    ThetaLowerSegment 448606464 448672000 (44858474144599 / 100000) (44864851061563 / 100000) := by
  exact
    packedTile32768 448606464 448672000 13 3201 21180 29 _ _ (498041 / 25000) (1992167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448672000 :
    ThetaLowerSegment 448672000 448737536 (44864851061563 / 100000) (4487137146343 / 10000) := by
  exact
    packedTile32768 448672000 448737536 13 3273 21181 29 _ _ (1992179 / 100000) (996091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448737536 :
    ThetaLowerSegment 448737536 448803072 (4487137146343 / 10000) (56097407223 / 125) := by
  exact
    packedTile32768 448737536 448803072 13 3290 21183 29 _ _ (1992193 / 100000) (498049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448803072 :
    ThetaLowerSegment 448803072 448868608 (56097407223 / 125) (2805277892199 / 6250) := by
  exact
    packedTile32768 448803072 448868608 13 3273 21184 29 _ _ (124513 / 6250) (1992211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448868608 :
    ThetaLowerSegment 448868608 448934144 (2805277892199 / 6250) (11222787028339 / 25000) := by
  exact
    packedTile32768 448868608 448934144 13 3364 21186 29 _ _ (1992223 / 100000) (996113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448934144 :
    ThetaLowerSegment 448934144 448999680 (11222787028339 / 25000) (22448847302069 / 50000) := by
  exact
    packedTile32768 448934144 448999680 13 3286 21188 29 _ _ (1992237 / 100000) (24903 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell448999680 :
    ThetaLowerSegment 448999680 449065216 (22448847302069 / 50000) (22452147467507 / 50000) := by
  exact
    packedTile32768 448999680 449065216 13 3313 21189 29 _ _ (498063 / 25000) (398451 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449065216 :
    ThetaLowerSegment 449065216 449130752 (22452147467507 / 50000) (22455335093107 / 50000) := by
  exact
    packedTile32768 449065216 449130752 13 3200 21191 29 _ _ (996133 / 50000) (1992269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449130752 :
    ThetaLowerSegment 449130752 449196288 (22455335093107 / 50000) (8983445356597 / 20000) := by
  exact
    packedTile32768 449130752 449196288 13 3291 21192 29 _ _ (1992281 / 100000) (498071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449196288 :
    ThetaLowerSegment 449196288 449261824 (8983445356597 / 20000) (8984764256549 / 20000) := by
  exact
    packedTile32768 449196288 449261824 13 3310 21194 29 _ _ (249037 / 12500) (1992299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449261824 :
    ThetaLowerSegment 449261824 449327360 (8984764256549 / 20000) (8986079978073 / 20000) := by
  exact
    packedTile32768 449261824 449327360 13 3302 21195 29 _ _ (199231 / 10000) (1992313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449327360 :
    ThetaLowerSegment 449327360 449392896 (8986079978073 / 20000) (4493701640169 / 10000) := by
  exact
    packedTile32768 449327360 449392896 13 3321 21197 29 _ _ (79693 / 4000) (249041 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449392896 :
    ThetaLowerSegment 449392896 449458432 (4493701640169 / 10000) (22471767667449 / 50000) := by
  exact
    packedTile32768 449392896 449458432 13 3272 21198 29 _ _ (1992339 / 100000) (996171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449458432 :
    ThetaLowerSegment 449458432 449523968 (22471767667449 / 50000) (11237537985633 / 25000) := by
  exact
    packedTile32768 449458432 449523968 13 3321 21200 29 _ _ (996177 / 50000) (1992357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449523968 :
    ThetaLowerSegment 449523968 449589504 (11237537985633 / 25000) (11239186670153 / 25000) := by
  exact
    packedTile32768 449523968 449589504 13 3310 21201 29 _ _ (124523 / 6250) (1992371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449589504 :
    ThetaLowerSegment 449589504 449655040 (11239186670153 / 25000) (44963200009149 / 100000) := by
  exact
    packedTile32768 449589504 449655040 13 3239 21203 29 _ _ (1992383 / 100000) (996193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449655040 :
    ThetaLowerSegment 449655040 449720576 (44963200009149 / 100000) (44969902436021 / 100000) := by
  exact
    packedTile32768 449655040 449720576 13 3364 21205 29 _ _ (996199 / 50000) (1992401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449720576 :
    ThetaLowerSegment 449720576 449786112 (44969902436021 / 100000) (44976479388033 / 100000) := by
  exact
    packedTile32768 449720576 449786112 13 3301 21206 29 _ _ (498103 / 25000) (398483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449786112 :
    ThetaLowerSegment 449786112 449851648 (44976479388033 / 100000) (22491462444689 / 50000) := by
  exact
    packedTile32768 449786112 449851648 13 3235 21208 29 _ _ (1992427 / 100000) (199243 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449851648 :
    ThetaLowerSegment 449851648 449917184 (22491462444689 / 50000) (44989462088299 / 100000) := by
  exact
    packedTile32768 449851648 449917184 13 3281 21209 29 _ _ (1992441 / 100000) (498111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449917184 :
    ThetaLowerSegment 449917184 449982720 (44989462088299 / 100000) (44996033208187 / 100000) := by
  exact
    packedTile32768 449917184 449982720 13 3298 21211 29 _ _ (249057 / 12500) (1992459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell449982720 :
    ThetaLowerSegment 449982720 450048256 (44996033208187 / 100000) (45002448961587 / 100000) := by
  exact
    packedTile32768 449982720 450048256 13 3220 21212 29 _ _ (199247 / 10000) (1992473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450048256 :
    ThetaLowerSegment 450048256 450113792 (45002448961587 / 100000) (11252252553673 / 25000) := by
  exact
    packedTile32768 450048256 450113792 13 3293 21214 29 _ _ (398497 / 20000) (249061 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450113792 :
    ThetaLowerSegment 450113792 450179328 (11252252553673 / 25000) (11253859504923 / 25000) := by
  exact
    packedTile32768 450113792 450179328 13 3226 21215 29 _ _ (797 / 40) (1992503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450179328 :
    ThetaLowerSegment 450179328 450244864 (11253859504923 / 25000) (22510981751521 / 50000) := by
  exact
    packedTile32768 450179328 450244864 13 3275 21217 29 _ _ (996257 / 50000) (1992517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450244864 :
    ThetaLowerSegment 450244864 450310400 (22510981751521 / 50000) (45028461140111 / 100000) := by
  exact
    packedTile32768 450244864 450310400 13 3261 21218 29 _ _ (1992529 / 100000) (498133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450310400 :
    ThetaLowerSegment 450310400 450375936 (45028461140111 / 100000) (22517555128051 / 50000) := by
  exact
    packedTile32768 450310400 450375936 13 3337 21220 29 _ _ (1992543 / 100000) (996273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450375936 :
    ThetaLowerSegment 450375936 450441472 (22517555128051 / 50000) (450416478389 / 1000) := by
  exact
    packedTile32768 450375936 450441472 13 3281 21222 29 _ _ (996279 / 50000) (1992561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450441472 :
    ThetaLowerSegment 450441472 450507008 (450416478389 / 1000) (2815513584299 / 6250) := by
  exact
    packedTile32768 450441472 450507008 13 3297 21223 29 _ _ (498143 / 25000) (79703 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450507008 :
    ThetaLowerSegment 450507008 450572544 (2815513584299 / 6250) (45054814804341 / 100000) := by
  exact
    packedTile32768 450507008 450572544 13 3311 21225 29 _ _ (1992587 / 100000) (199259 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450572544 :
    ThetaLowerSegment 450572544 450638080 (45054814804341 / 100000) (45061354520823 / 100000) := by
  exact
    packedTile32768 450572544 450638080 13 3282 21226 29 _ _ (1992601 / 100000) (498151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450638080 :
    ThetaLowerSegment 450638080 450703616 (45061354520823 / 100000) (45067932146239 / 100000) := by
  exact
    packedTile32768 450638080 450703616 13 3301 21228 29 _ _ (249077 / 12500) (1992619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450703616 :
    ThetaLowerSegment 450703616 450769152 (45067932146239 / 100000) (45074448049609 / 100000) := by
  exact
    packedTile32768 450703616 450769152 13 3270 21229 29 _ _ (1992631 / 100000) (996317 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450769152 :
    ThetaLowerSegment 450769152 450834688 (45074448049609 / 100000) (2817562865269 / 6250) := by
  exact
    packedTile32768 450769152 450834688 13 3291 21231 29 _ _ (398529 / 20000) (249081 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450834688 :
    ThetaLowerSegment 450834688 450900224 (2817562865269 / 6250) (1408985929367 / 3125) := by
  exact
    packedTile32768 450834688 450900224 13 3284 21232 29 _ _ (99633 / 5000) (1992663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450900224 :
    ThetaLowerSegment 450900224 450965760 (1408985929367 / 3125) (22547089683071 / 50000) := by
  exact
    packedTile32768 450900224 450965760 13 3327 21234 29 _ _ (996337 / 50000) (1992677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell450965760 :
    ThetaLowerSegment 450965760 451031296 (22547089683071 / 50000) (2818798946093 / 6250) := by
  exact
    packedTile32768 450965760 451031296 13 3314 21235 29 _ _ (1992689 / 100000) (498173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451031296 :
    ThetaLowerSegment 451031296 451096832 (2818798946093 / 6250) (45107293298189 / 100000) := by
  exact
    packedTile32768 451031296 451096832 13 3267 21237 29 _ _ (1992703 / 100000) (996353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451096832 :
    ThetaLowerSegment 451096832 451162368 (45107293298189 / 100000) (45113825427793 / 100000) := by
  exact
    packedTile32768 451096832 451162368 13 3278 21239 29 _ _ (996359 / 50000) (1992721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451162368 :
    ThetaLowerSegment 451162368 451227904 (45113825427793 / 100000) (45120351625093 / 100000) := by
  exact
    packedTile32768 451162368 451227904 13 3275 21240 29 _ _ (498183 / 25000) (398547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451227904 :
    ThetaLowerSegment 451227904 451293440 (45120351625093 / 100000) (45126947617663 / 100000) := by
  exact
    packedTile32768 451227904 451293440 13 3310 21242 29 _ _ (1992747 / 100000) (7971 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451293440 :
    ThetaLowerSegment 451293440 451358976 (45126947617663 / 100000) (45133591482837 / 100000) := by
  exact
    packedTile32768 451293440 451358976 13 3334 21243 29 _ _ (1992761 / 100000) (498191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451358976 :
    ThetaLowerSegment 451358976 451424512 (45133591482837 / 100000) (45140109853133 / 100000) := by
  exact
    packedTile32768 451358976 451424512 13 3271 21245 29 _ _ (249097 / 12500) (1992779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451424512 :
    ThetaLowerSegment 451424512 451490048 (45140109853133 / 100000) (45146642218753 / 100000) := by
  exact
    packedTile32768 451424512 451490048 13 3278 21246 29 _ _ (199279 / 10000) (1992793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451490048 :
    ThetaLowerSegment 451490048 451555584 (45146642218753 / 100000) (5644158038721 / 12500) := by
  exact
    packedTile32768 451490048 451555584 13 3323 21248 29 _ _ (398561 / 20000) (249101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451555584 :
    ThetaLowerSegment 451555584 451621120 (5644158038721 / 12500) (45159798763269 / 100000) := by
  exact
    packedTile32768 451555584 451621120 13 3279 21249 29 _ _ (1992819 / 100000) (996411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451621120 :
    ThetaLowerSegment 451621120 451686656 (45159798763269 / 100000) (45166478742837 / 100000) := by
  exact
    packedTile32768 451621120 451686656 13 3352 21251 29 _ _ (996417 / 50000) (1992837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451686656 :
    ThetaLowerSegment 451686656 451752192 (45166478742837 / 100000) (45172991370101 / 100000) := by
  exact
    packedTile32768 451686656 451752192 13 3268 21252 29 _ _ (124553 / 6250) (1992851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451752192 :
    ThetaLowerSegment 451752192 451817728 (45172991370101 / 100000) (22589814798377 / 50000) := by
  exact
    packedTile32768 451752192 451817728 13 3331 21254 29 _ _ (1992863 / 100000) (996433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451817728 :
    ThetaLowerSegment 451817728 451883264 (22589814798377 / 50000) (22592975501299 / 50000) := by
  exact
    packedTile32768 451817728 451883264 13 3172 21256 29 _ _ (1992877 / 100000) (24911 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451883264 :
    ThetaLowerSegment 451883264 451948800 (22592975501299 / 50000) (22596278719789 / 50000) := by
  exact
    packedTile32768 451883264 451948800 13 3315 21257 29 _ _ (498223 / 25000) (398579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell451948800 :
    ThetaLowerSegment 451948800 452014336 (22596278719789 / 50000) (5649891504559 / 12500) := by
  exact
    packedTile32768 451948800 452014336 13 3299 21259 29 _ _ (996453 / 50000) (1992909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452014336 :
    ThetaLowerSegment 452014336 452079872 (5649891504559 / 12500) (1130140126097 / 2500) := by
  exact
    packedTile32768 452014336 452079872 13 3248 21260 29 _ _ (1992921 / 100000) (498231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452079872 :
    ThetaLowerSegment 452079872 452145408 (1130140126097 / 2500) (361697884309 / 800) := by
  exact
    packedTile32768 452079872 452145408 13 3327 21262 29 _ _ (398587 / 20000) (996469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452145408 :
    ThetaLowerSegment 452145408 452210944 (361697884309 / 800) (1808750976303 / 4000) := by
  exact
    packedTile32768 452145408 452210944 13 3281 21263 29 _ _ (39859 / 2000) (1992953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452210944 :
    ThetaLowerSegment 452210944 452276480 (1808750976303 / 4000) (45225317308387 / 100000) := by
  exact
    packedTile32768 452210944 452276480 13 3283 21265 29 _ _ (498241 / 25000) (1992967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452276480 :
    ThetaLowerSegment 452276480 452342016 (45225317308387 / 100000) (22615928136243 / 50000) := by
  exact
    packedTile32768 452276480 452342016 13 3281 21266 29 _ _ (1992979 / 100000) (996491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452342016 :
    ThetaLowerSegment 452342016 452407552 (22615928136243 / 50000) (9047663909757 / 20000) := by
  exact
    packedTile32768 452342016 452407552 13 3243 21268 29 _ _ (1992993 / 100000) (498249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452407552 :
    ThetaLowerSegment 452407552 452473088 (9047663909757 / 20000) (45244930356321 / 100000) := by
  exact
    packedTile32768 452407552 452473088 13 3317 21269 29 _ _ (124563 / 6250) (1993011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452473088 :
    ThetaLowerSegment 452473088 452538624 (45244930356321 / 100000) (45251407677821 / 100000) := by
  exact
    packedTile32768 452473088 452538624 13 3250 21271 29 _ _ (996511 / 50000) (79721 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452538624 :
    ThetaLowerSegment 452538624 452604160 (45251407677821 / 100000) (1414310713942 / 3125) := by
  exact
    packedTile32768 452538624 452604160 13 3279 21272 29 _ _ (1993037 / 100000) (24913 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452604160 :
    ThetaLowerSegment 452604160 452669696 (1414310713942 / 3125) (22632218103151 / 50000) := by
  exact
    packedTile32768 452604160 452669696 13 3258 21274 29 _ _ (1993051 / 100000) (996527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452669696 :
    ThetaLowerSegment 452669696 452735232 (22632218103151 / 50000) (22635500682853 / 50000) := by
  exact
    packedTile32768 452669696 452735232 13 3294 21276 29 _ _ (996533 / 50000) (1993069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452735232 :
    ThetaLowerSegment 452735232 452800768 (22635500682853 / 50000) (22638791257933 / 50000) := by
  exact
    packedTile32768 452735232 452800768 13 3302 21277 29 _ _ (49827 / 2500) (1993083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452800768 :
    ThetaLowerSegment 452800768 452866304 (22638791257933 / 50000) (45284165708651 / 100000) := by
  exact
    packedTile32768 452800768 452866304 13 3303 21279 29 _ _ (398619 / 20000) (996549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452866304 :
    ThetaLowerSegment 452866304 452931840 (45284165708651 / 100000) (5661344116737 / 12500) := by
  exact
    packedTile32768 452866304 452931840 13 3305 21280 29 _ _ (1993109 / 100000) (249139 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452931840 :
    ThetaLowerSegment 452931840 452997376 (5661344116737 / 12500) (1132431063641 / 2500) := by
  exact
    packedTile32768 452931840 452997376 13 3256 21282 29 _ _ (498281 / 25000) (1993127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell452997376 :
    ThetaLowerSegment 452997376 453062912 (1132431063641 / 2500) (22651930878469 / 50000) := by
  exact
    packedTile32768 452997376 453062912 13 3321 21283 29 _ _ (996569 / 50000) (1993141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453062912 :
    ThetaLowerSegment 453062912 453128448 (22651930878469 / 50000) (22655271402897 / 50000) := by
  exact
    packedTile32768 453062912 453128448 13 3352 21285 29 _ _ (1993153 / 100000) (498289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453128448 :
    ThetaLowerSegment 453128448 453193984 (22655271402897 / 50000) (22658504319771 / 50000) := by
  exact
    packedTile32768 453128448 453193984 13 3244 21286 29 _ _ (1993167 / 100000) (199317 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453193984 :
    ThetaLowerSegment 453193984 453259520 (22658504319771 / 50000) (22661791076889 / 50000) := by
  exact
    packedTile32768 453193984 453259520 13 3298 21288 29 _ _ (996591 / 50000) (398637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453259520 :
    ThetaLowerSegment 453259520 453325056 (22661791076889 / 50000) (22665059918329 / 50000) := by
  exact
    packedTile32768 453259520 453325056 13 3280 21289 29 _ _ (498299 / 25000) (1993199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453325056 :
    ThetaLowerSegment 453325056 453390592 (22665059918329 / 50000) (11334160903247 / 25000) := by
  exact
    packedTile32768 453325056 453390592 13 3273 21291 29 _ _ (199321 / 10000) (1993213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453390592 :
    ThetaLowerSegment 453390592 453456128 (11334160903247 / 25000) (45343131560363 / 100000) := by
  exact
    packedTile32768 453390592 453456128 13 3255 21292 29 _ _ (79729 / 4000) (498307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453456128 :
    ThetaLowerSegment 453456128 453521664 (45343131560363 / 100000) (22674823729327 / 50000) := by
  exact
    packedTile32768 453456128 453521664 13 3269 21294 29 _ _ (1993239 / 100000) (996621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453521664 :
    ThetaLowerSegment 453521664 453587200 (22674823729327 / 50000) (22678094659141 / 50000) := by
  exact
    packedTile32768 453521664 453587200 13 3282 21296 29 _ _ (996627 / 50000) (1993257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453587200 :
    ThetaLowerSegment 453587200 453652736 (22678094659141 / 50000) (22681422420067 / 50000) := by
  exact
    packedTile32768 453587200 453652736 13 3339 21297 29 _ _ (498317 / 25000) (1993271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453652736 :
    ThetaLowerSegment 453652736 453718272 (22681422420067 / 50000) (45369480479241 / 100000) := by
  exact
    packedTile32768 453652736 453718272 13 3329 21299 29 _ _ (1993283 / 100000) (996643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453718272 :
    ThetaLowerSegment 453718272 453783808 (45369480479241 / 100000) (9075216455781 / 20000) := by
  exact
    packedTile32768 453718272 453783808 13 3312 21300 29 _ _ (1993297 / 100000) (19933 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453783808 :
    ThetaLowerSegment 453783808 453849344 (9075216455781 / 20000) (45382536623161 / 100000) := by
  exact
    packedTile32768 453783808 453849344 13 3238 21302 29 _ _ (62291 / 3125) (398663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453849344 :
    ThetaLowerSegment 453849344 453914880 (45382536623161 / 100000) (45389156458807 / 100000) := by
  exact
    packedTile32768 453849344 453914880 13 3321 21303 29 _ _ (996663 / 50000) (1993329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453914880 :
    ThetaLowerSegment 453914880 453980416 (45389156458807 / 100000) (45395786310973 / 100000) := by
  exact
    packedTile32768 453914880 453980416 13 3326 21305 29 _ _ (1993341 / 100000) (62292 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell453980416 :
    ThetaLowerSegment 453980416 454045952 (45395786310973 / 100000) (45402256741303 / 100000) := by
  exact
    packedTile32768 453980416 454045952 13 3246 21306 29 _ _ (398671 / 20000) (996679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454045952 :
    ThetaLowerSegment 454045952 454111488 (45402256741303 / 100000) (22704372578699 / 50000) := by
  exact
    packedTile32768 454045952 454111488 13 3255 21308 29 _ _ (1993369 / 100000) (498343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454111488 :
    ThetaLowerSegment 454111488 454177024 (22704372578699 / 50000) (22707608837623 / 50000) := by
  exact
    packedTile32768 454111488 454177024 13 3247 21309 29 _ _ (249173 / 12500) (1993387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454177024 :
    ThetaLowerSegment 454177024 454242560 (22707608837623 / 50000) (11355439503521 / 25000) := by
  exact
    packedTile32768 454177024 454242560 13 3281 21311 29 _ _ (996699 / 50000) (1993401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454242560 :
    ThetaLowerSegment 454242560 454308096 (11355439503521 / 25000) (45428282454833 / 100000) := by
  exact
    packedTile32768 454242560 454308096 13 3273 21312 29 _ _ (1993413 / 100000) (249177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454308096 :
    ThetaLowerSegment 454308096 454373632 (45428282454833 / 100000) (45434765079437 / 100000) := by
  exact
    packedTile32768 454308096 454373632 13 3252 21314 29 _ _ (1993427 / 100000) (199343 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454373632 :
    ThetaLowerSegment 454373632 454439168 (45434765079437 / 100000) (45441403241297 / 100000) := by
  exact
    packedTile32768 454373632 454439168 13 3330 21316 29 _ _ (996721 / 50000) (398689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454439168 :
    ThetaLowerSegment 454439168 454504704 (45441403241297 / 100000) (45448031482497 / 100000) := by
  exact
    packedTile32768 454439168 454504704 13 3325 21317 29 _ _ (124591 / 6250) (1993459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454504704 :
    ThetaLowerSegment 454504704 454570240 (45448031482497 / 100000) (45454550129397 / 100000) := by
  exact
    packedTile32768 454504704 454570240 13 3270 21319 29 _ _ (199347 / 10000) (1993473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454570240 :
    ThetaLowerSegment 454570240 454635776 (45454550129397 / 100000) (45461104708077 / 100000) := by
  exact
    packedTile32768 454570240 454635776 13 3288 21320 29 _ _ (398697 / 20000) (124593 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454635776 :
    ThetaLowerSegment 454635776 454701312 (45461104708077 / 100000) (11366925299067 / 25000) := by
  exact
    packedTile32768 454635776 454701312 13 3309 21322 29 _ _ (1993499 / 100000) (996751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454701312 :
    ThetaLowerSegment 454701312 454766848 (11366925299067 / 25000) (11368559980547 / 25000) := by
  exact
    packedTile32768 454701312 454766848 13 3280 21323 29 _ _ (996757 / 50000) (1993517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454766848 :
    ThetaLowerSegment 454766848 454832384 (11368559980547 / 25000) (11370202149237 / 25000) := by
  exact
    packedTile32768 454766848 454832384 13 3295 21325 29 _ _ (249191 / 12500) (1993531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454832384 :
    ThetaLowerSegment 454832384 454897920 (11370202149237 / 25000) (11371838847219 / 25000) := by
  exact
    packedTile32768 454832384 454897920 13 3284 21326 29 _ _ (996771 / 50000) (398709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454897920 :
    ThetaLowerSegment 454897920 454963456 (11371838847219 / 25000) (45493991940129 / 100000) := by
  exact
    packedTile32768 454897920 454963456 13 3329 21328 29 _ _ (1993557 / 100000) (49839 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell454963456 :
    ThetaLowerSegment 454963456 455028992 (45493991940129 / 100000) (45500419213033 / 100000) := by
  exact
    packedTile32768 454963456 455028992 13 3224 21329 29 _ _ (1993571 / 100000) (996787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455028992 :
    ThetaLowerSegment 455028992 455094528 (45500419213033 / 100000) (45506936245667 / 100000) := by
  exact
    packedTile32768 455028992 455094528 13 3269 21331 29 _ _ (996793 / 50000) (1993589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455094528 :
    ThetaLowerSegment 455094528 455160064 (45506936245667 / 100000) (45513451330467 / 100000) := by
  exact
    packedTile32768 455094528 455160064 13 3268 21332 29 _ _ (2492 / 125) (1993603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455160064 :
    ThetaLowerSegment 455160064 455225600 (45513451330467 / 100000) (45520036237509 / 100000) := by
  exact
    packedTile32768 455160064 455225600 13 3303 21334 29 _ _ (996807 / 50000) (1993617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455225600 :
    ThetaLowerSegment 455225600 455291136 (45520036237509 / 100000) (45526730843691 / 100000) := by
  exact
    packedTile32768 455225600 455291136 13 3358 21336 29 _ _ (1993629 / 100000) (62301 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455291136 :
    ThetaLowerSegment 455291136 455356672 (45526730843691 / 100000) (45533377649453 / 100000) := by
  exact
    packedTile32768 455291136 455356672 13 3334 21337 29 _ _ (1993643 / 100000) (996823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455356672 :
    ThetaLowerSegment 455356672 455422208 (45533377649453 / 100000) (9107982970807 / 20000) := by
  exact
    packedTile32768 455356672 455422208 13 3279 21339 29 _ _ (996829 / 50000) (1993661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455422208 :
    ThetaLowerSegment 455422208 455487744 (9107982970807 / 20000) (45546505933667 / 100000) := by
  exact
    packedTile32768 455422208 455487744 13 3306 21340 29 _ _ (249209 / 12500) (79747 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455487744 :
    ThetaLowerSegment 455487744 455553280 (45546505933667 / 100000) (45553055192177 / 100000) := by
  exact
    packedTile32768 455487744 455553280 13 3285 21342 29 _ _ (996843 / 50000) (1993689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455553280 :
    ThetaLowerSegment 455553280 455618816 (45553055192177 / 100000) (2847471044633 / 6250) := by
  exact
    packedTile32768 455553280 455618816 13 3251 21343 29 _ _ (1993701 / 100000) (249213 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455618816 :
    ThetaLowerSegment 455618816 455684352 (2847471044633 / 6250) (1423941871819 / 3125) := by
  exact
    packedTile32768 455618816 455684352 13 3312 21345 29 _ _ (398743 / 20000) (996859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455684352 :
    ThetaLowerSegment 455684352 455749888 (1423941871819 / 3125) (2848299436343 / 6250) := by
  exact
    packedTile32768 455684352 455749888 13 3336 21346 29 _ _ (199373 / 10000) (1993733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455749888 :
    ThetaLowerSegment 455749888 455815424 (2848299436343 / 6250) (2848711144479 / 6250) := by
  exact
    packedTile32768 455749888 455815424 13 3304 21348 29 _ _ (124609 / 6250) (1993747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455815424 :
    ThetaLowerSegment 455815424 455880960 (2848711144479 / 6250) (911719832139 / 2000) := by
  exact
    packedTile32768 455815424 455880960 13 3317 21349 29 _ _ (996879 / 50000) (1993761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455880960 :
    ThetaLowerSegment 455880960 455946496 (911719832139 / 2000) (9118512217797 / 20000) := by
  exact
    packedTile32768 455880960 455946496 13 3295 21351 29 _ _ (1993773 / 100000) (124611 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell455946496 :
    ThetaLowerSegment 455946496 456012032 (9118512217797 / 20000) (11399755738163 / 25000) := by
  exact
    packedTile32768 455946496 456012032 13 3241 21352 29 _ _ (1993787 / 100000) (199379 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456012032 :
    ThetaLowerSegment 456012032 456077568 (11399755738163 / 25000) (45605516762509 / 100000) := by
  exact
    packedTile32768 456012032 456077568 13 3257 21354 29 _ _ (1993801 / 100000) (498451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456077568 :
    ThetaLowerSegment 456077568 456143104 (45605516762509 / 100000) (45612090373861 / 100000) := by
  exact
    packedTile32768 456077568 456143104 13 3297 21355 29 _ _ (249227 / 12500) (1993819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456143104 :
    ThetaLowerSegment 456143104 456208640 (45612090373861 / 100000) (45618679982011 / 100000) := by
  exact
    packedTile32768 456143104 456208640 13 3305 21357 29 _ _ (199383 / 10000) (1993833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456208640 :
    ThetaLowerSegment 456208640 456274176 (45618679982011 / 100000) (1425790174703 / 3125) := by
  exact
    packedTile32768 456208640 456274176 13 3313 21359 29 _ _ (398769 / 20000) (249231 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456274176 :
    ThetaLowerSegment 456274176 456339712 (1425790174703 / 3125) (45631695847181 / 100000) := by
  exact
    packedTile32768 456274176 456339712 13 3215 21360 29 _ _ (1993859 / 100000) (996931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456339712 :
    ThetaLowerSegment 456339712 456405248 (45631695847181 / 100000) (5704794173641 / 12500) := by
  exact
    packedTile32768 456339712 456405248 13 3339 21362 29 _ _ (1993873 / 100000) (498469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456405248 :
    ThetaLowerSegment 456405248 456470784 (5704794173641 / 12500) (228225104753 / 500) := by
  exact
    packedTile32768 456405248 456470784 13 3344 21363 29 _ _ (62309 / 3125) (1993891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456470784 :
    ThetaLowerSegment 456470784 456536320 (228225104753 / 500) (22825847270297 / 50000) := by
  exact
    packedTile32768 456470784 456536320 13 3347 21365 29 _ _ (996951 / 50000) (398781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456536320 :
    ThetaLowerSegment 456536320 456601856 (22825847270297 / 50000) (22829157170857 / 50000) := by
  exact
    packedTile32768 456536320 456601856 13 3320 21366 29 _ _ (498479 / 25000) (1993919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456601856 :
    ThetaLowerSegment 456601856 456667392 (22829157170857 / 50000) (45664952138013 / 100000) := by
  exact
    packedTile32768 456601856 456667392 13 3329 21368 29 _ _ (1993931 / 100000) (996967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456667392 :
    ThetaLowerSegment 456667392 456732928 (45664952138013 / 100000) (45671524180733 / 100000) := by
  exact
    packedTile32768 456667392 456732928 13 3296 21369 29 _ _ (398789 / 20000) (498487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456732928 :
    ThetaLowerSegment 456732928 456798464 (45671524180733 / 100000) (45678036450827 / 100000) := by
  exact
    packedTile32768 456732928 456798464 13 3266 21371 29 _ _ (1993959 / 100000) (996981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456798464 :
    ThetaLowerSegment 456798464 456864000 (45678036450827 / 100000) (45684604601183 / 100000) := by
  exact
    packedTile32768 456798464 456864000 13 3294 21372 29 _ _ (996987 / 50000) (1993977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456864000 :
    ThetaLowerSegment 456864000 456929536 (45684604601183 / 100000) (45691180773607 / 100000) := by
  exact
    packedTile32768 456864000 456929536 13 3298 21374 29 _ _ (498497 / 25000) (1993991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456929536 :
    ThetaLowerSegment 456929536 456995072 (45691180773607 / 100000) (45697685208131 / 100000) := by
  exact
    packedTile32768 456929536 456995072 13 3262 21375 29 _ _ (997001 / 50000) (398801 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell456995072 :
    ThetaLowerSegment 456995072 457060608 (45697685208131 / 100000) (45704097966803 / 100000) := by
  exact
    packedTile32768 456995072 457060608 13 3216 21377 29 _ _ (1994017 / 100000) (99701 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457060608 :
    ThetaLowerSegment 457060608 457126144 (45704097966803 / 100000) (285691327913 / 625) := by
  exact
    packedTile32768 457060608 457126144 13 3267 21378 29 _ _ (1994031 / 100000) (997017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457126144 :
    ThetaLowerSegment 457126144 457191680 (285691327913 / 625) (9143415830803 / 20000) := by
  exact
    packedTile32768 457126144 457191680 13 3243 21380 29 _ _ (398809 / 20000) (62314 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457191680 :
    ThetaLowerSegment 457191680 457257216 (9143415830803 / 20000) (9144727124659 / 20000) := by
  exact
    packedTile32768 457191680 457257216 13 3288 21382 29 _ _ (99703 / 5000) (1994063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457257216 :
    ThetaLowerSegment 457257216 457322752 (9144727124659 / 20000) (45730267913419 / 100000) := by
  exact
    packedTile32768 457257216 457322752 13 3326 21383 29 _ _ (997037 / 50000) (1994077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457322752 :
    ThetaLowerSegment 457322752 457339136 (45730267913419 / 100000) (45731809343443 / 100000) := by
  exact
    packedTile32768 457322752 457339136 11 773 21385 29 _ _ (249261 / 12500) (1994091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457339136 :
    ThetaLowerSegment 457339136 457341184 (45731809343443 / 100000) (45732012740827 / 100000) := by
  exact
    packedTile32768 457339136 457341184 8 102 21385 29 _ _ (498523 / 25000) (398819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_425341184_457341184 :
    ThetaLowerSegment 425341184 457341184 (42531736180899 / 100000) (45732012740827 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell425341184 cell425406720)
                    (ThetaLowerSegment.join cell425472256 cell425537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell425603328 cell425668864)
                    (ThetaLowerSegment.join cell425734400 cell425799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell425865472 cell425931008)
                    (ThetaLowerSegment.join cell425996544 cell426062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell426127616 cell426193152)
                    (ThetaLowerSegment.join cell426258688 cell426324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell426389760 cell426455296)
                    (ThetaLowerSegment.join cell426520832 cell426586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell426651904 cell426717440)
                    (ThetaLowerSegment.join cell426782976 cell426848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell426914048 cell426979584)
                    (ThetaLowerSegment.join cell427045120 cell427110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell427176192 cell427241728)
                    (ThetaLowerSegment.join cell427307264 cell427372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell427438336 cell427503872)
                    (ThetaLowerSegment.join cell427569408 cell427634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell427700480 cell427766016)
                    (ThetaLowerSegment.join cell427831552 cell427897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell427962624 cell428028160)
                    (ThetaLowerSegment.join cell428093696 cell428159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell428224768 cell428290304)
                    (ThetaLowerSegment.join cell428355840 cell428421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell428486912 cell428552448)
                    (ThetaLowerSegment.join cell428617984 cell428683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell428749056 cell428814592)
                    (ThetaLowerSegment.join cell428880128 cell428945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell429011200 cell429076736)
                    (ThetaLowerSegment.join cell429142272 cell429207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell429273344 cell429338880)
                    (ThetaLowerSegment.join cell429404416 cell429469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell429535488 cell429601024)
                    (ThetaLowerSegment.join cell429666560 cell429732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell429797632 cell429863168)
                    (ThetaLowerSegment.join cell429928704 cell429994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell430059776 cell430125312)
                    (ThetaLowerSegment.join cell430190848 cell430256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell430321920 cell430387456)
                    (ThetaLowerSegment.join cell430452992 cell430518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell430584064 cell430649600)
                    (ThetaLowerSegment.join cell430715136 cell430780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell430846208 cell430911744)
                    (ThetaLowerSegment.join cell430977280 cell431042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell431108352 cell431173888)
                    (ThetaLowerSegment.join cell431239424 cell431304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell431370496 cell431436032)
                    (ThetaLowerSegment.join cell431501568 cell431567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell431632640 cell431698176)
                    (ThetaLowerSegment.join cell431763712 cell431829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell431894784 cell431960320)
                    (ThetaLowerSegment.join cell432025856 cell432091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell432156928 cell432222464)
                    (ThetaLowerSegment.join cell432288000 cell432353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell432419072 cell432484608)
                    (ThetaLowerSegment.join cell432550144 cell432615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell432681216 cell432746752)
                    (ThetaLowerSegment.join cell432812288 cell432877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell432943360 cell433008896)
                    (ThetaLowerSegment.join cell433074432 cell433139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell433205504 cell433271040)
                    (ThetaLowerSegment.join cell433336576 cell433402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell433467648 cell433533184)
                    (ThetaLowerSegment.join cell433598720 cell433664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell433729792 cell433795328)
                    (ThetaLowerSegment.join cell433860864 cell433926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell433991936 cell434057472)
                    (ThetaLowerSegment.join cell434123008 cell434188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell434254080 cell434319616)
                    (ThetaLowerSegment.join cell434385152 cell434450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell434516224 cell434581760)
                    (ThetaLowerSegment.join cell434647296 cell434712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell434778368 cell434843904)
                    (ThetaLowerSegment.join cell434909440 cell434974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell435040512 cell435106048)
                    (ThetaLowerSegment.join cell435171584 cell435237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell435302656 cell435368192)
                    (ThetaLowerSegment.join cell435433728 cell435499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell435564800 cell435630336)
                    (ThetaLowerSegment.join cell435695872 cell435761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell435826944 cell435892480)
                    (ThetaLowerSegment.join cell435958016 cell436023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell436089088 cell436154624)
                    (ThetaLowerSegment.join cell436220160 cell436285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell436351232 cell436416768)
                    (ThetaLowerSegment.join cell436482304 cell436547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell436613376 cell436678912)
                    (ThetaLowerSegment.join cell436744448 cell436809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell436875520 cell436941056)
                    (ThetaLowerSegment.join cell437006592 cell437072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell437137664 cell437203200)
                    (ThetaLowerSegment.join cell437268736 cell437334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell437399808 cell437465344)
                    (ThetaLowerSegment.join cell437530880 cell437596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell437661952 cell437727488)
                    (ThetaLowerSegment.join cell437793024 cell437858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell437924096 cell437989632)
                    (ThetaLowerSegment.join cell438055168 cell438120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell438186240 cell438251776)
                    (ThetaLowerSegment.join cell438317312 cell438382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell438448384 cell438513920)
                    (ThetaLowerSegment.join cell438579456 cell438644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell438710528 cell438776064)
                    (ThetaLowerSegment.join cell438841600 cell438907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell438972672 cell439038208)
                    (ThetaLowerSegment.join cell439103744 cell439169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell439234816 cell439300352)
                    (ThetaLowerSegment.join cell439365888 cell439431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell439496960 cell439562496)
                    (ThetaLowerSegment.join cell439628032 cell439693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell439759104 cell439824640)
                    (ThetaLowerSegment.join cell439890176 cell439955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell440021248 cell440086784)
                    (ThetaLowerSegment.join cell440152320 cell440217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell440283392 cell440348928)
                    (ThetaLowerSegment.join cell440414464 cell440480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell440545536 cell440611072)
                    (ThetaLowerSegment.join cell440676608 cell440742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell440807680 cell440873216)
                    (ThetaLowerSegment.join cell440938752 cell441004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell441069824 cell441135360)
                    (ThetaLowerSegment.join cell441200896 cell441266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell441331968 cell441397504)
                    (ThetaLowerSegment.join cell441463040 cell441528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell441594112 cell441659648)
                    (ThetaLowerSegment.join cell441725184 cell441790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell441856256 cell441921792)
                    (ThetaLowerSegment.join cell441987328 cell442052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell442118400 cell442183936)
                    (ThetaLowerSegment.join cell442249472 cell442315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell442380544 cell442446080)
                    (ThetaLowerSegment.join cell442511616 cell442577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell442642688 cell442708224)
                    (ThetaLowerSegment.join cell442773760 cell442839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell442904832 cell442970368)
                    (ThetaLowerSegment.join cell443035904 cell443101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell443166976 cell443232512)
                    (ThetaLowerSegment.join cell443298048 cell443363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell443429120 cell443494656)
                    (ThetaLowerSegment.join cell443560192 cell443625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell443691264 cell443756800)
                    (ThetaLowerSegment.join cell443822336 cell443887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell443953408 cell444018944)
                    (ThetaLowerSegment.join cell444084480 cell444150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell444215552 cell444281088)
                    (ThetaLowerSegment.join cell444346624 cell444412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell444477696 cell444543232)
                    (ThetaLowerSegment.join cell444608768 cell444674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell444739840 cell444805376)
                    (ThetaLowerSegment.join cell444870912 cell444936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell445001984 cell445067520)
                    (ThetaLowerSegment.join cell445133056 cell445198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell445264128 cell445329664)
                    (ThetaLowerSegment.join cell445395200 cell445460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell445526272 cell445591808)
                    (ThetaLowerSegment.join cell445657344 cell445722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell445788416 cell445853952)
                    (ThetaLowerSegment.join cell445919488 cell445985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell446050560 cell446116096)
                    (ThetaLowerSegment.join cell446181632 cell446247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell446312704 cell446378240)
                    (ThetaLowerSegment.join cell446443776 cell446509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell446574848 cell446640384)
                    (ThetaLowerSegment.join cell446705920 cell446771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell446836992 cell446902528)
                    (ThetaLowerSegment.join cell446968064 cell447033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell447099136 cell447164672)
                    (ThetaLowerSegment.join cell447230208 cell447295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell447361280 cell447426816)
                    (ThetaLowerSegment.join cell447492352 cell447557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell447623424 cell447688960)
                    (ThetaLowerSegment.join cell447754496 cell447820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell447885568 cell447951104)
                    (ThetaLowerSegment.join cell448016640 cell448082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell448147712 cell448213248)
                    (ThetaLowerSegment.join cell448278784 cell448344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell448409856 cell448475392)
                    (ThetaLowerSegment.join cell448540928 cell448606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell448672000 cell448737536)
                    (ThetaLowerSegment.join cell448803072 cell448868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell448934144 cell448999680)
                    (ThetaLowerSegment.join cell449065216 cell449130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell449196288 cell449261824)
                    (ThetaLowerSegment.join cell449327360 cell449392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell449458432 cell449523968)
                    (ThetaLowerSegment.join cell449589504 cell449655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell449720576 cell449786112)
                    (ThetaLowerSegment.join cell449851648 cell449917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell449982720 cell450048256)
                    (ThetaLowerSegment.join cell450113792 cell450179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell450244864 cell450310400)
                    (ThetaLowerSegment.join cell450375936 cell450441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell450507008 cell450572544)
                    (ThetaLowerSegment.join cell450638080 cell450703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell450769152 cell450834688)
                    (ThetaLowerSegment.join cell450900224 cell450965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell451031296 cell451096832)
                    (ThetaLowerSegment.join cell451162368 cell451227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell451293440 cell451358976)
                    (ThetaLowerSegment.join cell451424512 cell451490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell451555584 cell451621120)
                    (ThetaLowerSegment.join cell451686656 cell451752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell451817728 cell451883264)
                    (ThetaLowerSegment.join cell451948800 cell452014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell452079872 cell452145408)
                    (ThetaLowerSegment.join cell452210944 cell452276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell452342016 cell452407552)
                    (ThetaLowerSegment.join cell452473088 cell452538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell452604160 cell452669696)
                    (ThetaLowerSegment.join cell452735232 cell452800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell452866304 cell452931840)
                    (ThetaLowerSegment.join cell452997376 cell453062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell453128448 cell453193984)
                    (ThetaLowerSegment.join cell453259520 cell453325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell453390592 cell453456128)
                    (ThetaLowerSegment.join cell453521664 cell453587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell453652736 cell453718272)
                    (ThetaLowerSegment.join cell453783808 cell453849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell453914880 cell453980416)
                    (ThetaLowerSegment.join cell454045952 cell454111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell454177024 cell454242560)
                    (ThetaLowerSegment.join cell454308096 cell454373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell454439168 cell454504704)
                    (ThetaLowerSegment.join cell454570240 cell454635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell454701312 cell454766848)
                    (ThetaLowerSegment.join cell454832384 cell454897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell454963456 cell455028992)
                    (ThetaLowerSegment.join cell455094528 cell455160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell455225600 cell455291136)
                    (ThetaLowerSegment.join cell455356672 cell455422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell455487744 cell455553280)
                    (ThetaLowerSegment.join cell455618816 cell455684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell455749888 cell455815424)
                    (ThetaLowerSegment.join cell455880960 cell455946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell456012032 cell456077568)
                    (ThetaLowerSegment.join cell456143104 cell456208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell456274176 cell456339712)
                    (ThetaLowerSegment.join cell456405248 cell456470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell456536320 cell456601856)
                    (ThetaLowerSegment.join cell456667392 cell456732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell456798464 cell456864000)
                  (ThetaLowerSegment.join cell456929536 cell456995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell457060608 cell457126144)
                  (ThetaLowerSegment.join cell457191680 cell457257216)))
              (ThetaLowerSegment.join cell457322752 cell457339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
