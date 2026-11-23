/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 809341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell777341184 :
    ThetaLowerSegment 777341184 777406720 (77729513866247 / 100000) (77736179344319 / 100000) := by
  exact
    packedTile32768 777341184 777406720 13 3256 27880 30 _ _ (2047137 / 100000) (102357 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777406720 :
    ThetaLowerSegment 777406720 777472256 (77736179344319 / 100000) (77742789578753 / 100000) := by
  exact
    packedTile32768 777406720 777472256 13 3229 27882 30 _ _ (1023573 / 50000) (2047149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777472256 :
    ThetaLowerSegment 777472256 777537792 (77742789578753 / 100000) (77749395744711 / 100000) := by
  exact
    packedTile32768 777472256 777537792 13 3227 27883 30 _ _ (1023577 / 50000) (2047157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777537792 :
    ThetaLowerSegment 777537792 777603328 (77749395744711 / 100000) (38877917036173 / 50000) := by
  exact
    packedTile32768 777537792 777603328 13 3145 27884 30 _ _ (2047163 / 100000) (1023583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777603328 :
    ThetaLowerSegment 777603328 777668864 (38877917036173 / 50000) (38881294868323 / 50000) := by
  exact
    packedTile32768 777603328 777668864 13 3300 27885 30 _ _ (2047171 / 100000) (1023587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777668864 :
    ThetaLowerSegment 777668864 777734400 (38881294868323 / 50000) (38884524294773 / 50000) := by
  exact
    packedTile32768 777668864 777734400 13 3155 27886 30 _ _ (102359 / 5000) (2047183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777734400 :
    ThetaLowerSegment 777734400 777799936 (38884524294773 / 50000) (38887803889949 / 50000) := by
  exact
    packedTile32768 777734400 777799936 13 3204 27887 30 _ _ (511797 / 25000) (2047191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777799936 :
    ThetaLowerSegment 777799936 777865472 (38887803889949 / 50000) (7778219360943 / 10000) := by
  exact
    packedTile32768 777799936 777865472 13 3217 27889 30 _ _ (511799 / 25000) (2047199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777865472 :
    ThetaLowerSegment 777865472 777931008 (7778219360943 / 10000) (3889432934141 / 5000) := by
  exact
    packedTile32768 777865472 777931008 13 3158 27890 30 _ _ (409441 / 20000) (255901 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777931008 :
    ThetaLowerSegment 777931008 777996544 (3889432934141 / 5000) (19448790157827 / 25000) := by
  exact
    packedTile32768 777931008 777996544 13 3176 27891 30 _ _ (2047213 / 100000) (127951 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell777996544 :
    ThetaLowerSegment 777996544 778062080 (19448790157827 / 25000) (2431305411199 / 3125) := by
  exact
    packedTile32768 777996544 778062080 13 3230 27892 30 _ _ (1023611 / 50000) (81889 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778062080 :
    ThetaLowerSegment 778062080 778127616 (2431305411199 / 3125) (38904144745729 / 50000) := by
  exact
    packedTile32768 778062080 778127616 13 3183 27893 30 _ _ (204723 / 10000) (2047233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778127616 :
    ThetaLowerSegment 778127616 778193152 (38904144745729 / 50000) (77814859081409 / 100000) := by
  exact
    packedTile32768 778127616 778193152 13 3209 27894 30 _ _ (2047239 / 100000) (1023621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778193152 :
    ThetaLowerSegment 778193152 778258688 (77814859081409 / 100000) (77821316098447 / 100000) := by
  exact
    packedTile32768 778193152 778258688 13 3154 27896 30 _ _ (2047247 / 100000) (8189 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778258688 :
    ThetaLowerSegment 778258688 778324224 (77821316098447 / 100000) (77827924637587 / 100000) := by
  exact
    packedTile32768 778258688 778324224 13 3228 27897 30 _ _ (409451 / 20000) (1023629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778324224 :
    ThetaLowerSegment 778324224 778389760 (77827924637587 / 100000) (77834471787859 / 100000) := by
  exact
    packedTile32768 778324224 778389760 13 3198 27898 30 _ _ (63977 / 3125) (2047267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778389760 :
    ThetaLowerSegment 778389760 778455296 (77834471787859 / 100000) (77841051720067 / 100000) := by
  exact
    packedTile32768 778389760 778455296 13 3214 27899 30 _ _ (255909 / 12500) (81891 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778455296 :
    ThetaLowerSegment 778455296 778520832 (77841051720067 / 100000) (77847467898721 / 100000) := by
  exact
    packedTile32768 778455296 778520832 13 3134 27900 30 _ _ (2047281 / 100000) (511821 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778520832 :
    ThetaLowerSegment 778520832 778586368 (77847467898721 / 100000) (9731752147029 / 12500) := by
  exact
    packedTile32768 778520832 778586368 13 3199 27901 30 _ _ (2047289 / 100000) (511823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778586368 :
    ThetaLowerSegment 778586368 778651904 (9731752147029 / 12500) (19465116541233 / 25000) := by
  exact
    packedTile32768 778586368 778651904 13 3150 27903 30 _ _ (1023649 / 50000) (2047301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778651904 :
    ThetaLowerSegment 778651904 778717440 (19465116541233 / 25000) (38933558931063 / 50000) := by
  exact
    packedTile32768 778651904 778717440 13 3249 27904 30 _ _ (1023653 / 50000) (2047309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778717440 :
    ThetaLowerSegment 778717440 778782976 (38933558931063 / 50000) (4867105480797 / 6250) := by
  exact
    packedTile32768 778717440 778782976 13 3209 27905 30 _ _ (1023657 / 50000) (2047317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778782976 :
    ThetaLowerSegment 778782976 778848512 (4867105480797 / 6250) (38940109326561 / 50000) := by
  exact
    packedTile32768 778782976 778848512 13 3190 27906 30 _ _ (2047323 / 100000) (1023663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778848512 :
    ThetaLowerSegment 778848512 778914048 (38940109326561 / 50000) (38943360488189 / 50000) := by
  exact
    packedTile32768 778848512 778914048 13 3176 27907 30 _ _ (2047331 / 100000) (1023667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778914048 :
    ThetaLowerSegment 778914048 778979584 (38943360488189 / 50000) (38946620877139 / 50000) := by
  exact
    packedTile32768 778914048 778979584 13 3185 27909 30 _ _ (102367 / 5000) (2047343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell778979584 :
    ThetaLowerSegment 778979584 779045120 (38946620877139 / 50000) (38949945770291 / 50000) := by
  exact
    packedTile32768 778979584 779045120 13 3248 27910 30 _ _ (511837 / 25000) (2047351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779045120 :
    ThetaLowerSegment 779045120 779110656 (38949945770291 / 50000) (38953232800349 / 50000) := by
  exact
    packedTile32768 779045120 779110656 13 3211 27911 30 _ _ (511839 / 25000) (2047359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779110656 :
    ThetaLowerSegment 779110656 779176192 (38953232800349 / 50000) (38956533152729 / 50000) := by
  exact
    packedTile32768 779110656 779176192 13 3224 27912 30 _ _ (409473 / 20000) (255921 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779176192 :
    ThetaLowerSegment 779176192 779241728 (38956533152729 / 50000) (38959796665291 / 50000) := by
  exact
    packedTile32768 779176192 779241728 13 3188 27913 30 _ _ (2047373 / 100000) (127961 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779241728 :
    ThetaLowerSegment 779241728 779307264 (38959796665291 / 50000) (38963002865503 / 50000) := by
  exact
    packedTile32768 779241728 779307264 13 3132 27914 30 _ _ (1023691 / 50000) (409477 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779307264 :
    ThetaLowerSegment 779307264 779372800 (38963002865503 / 50000) (38966250026043 / 50000) := by
  exact
    packedTile32768 779307264 779372800 13 3172 27916 30 _ _ (204739 / 10000) (2047393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779372800 :
    ThetaLowerSegment 779372800 779438336 (38966250026043 / 50000) (19484768050719 / 25000) := by
  exact
    packedTile32768 779372800 779438336 13 3210 27917 30 _ _ (2047399 / 100000) (1023701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779438336 :
    ThetaLowerSegment 779438336 779503872 (19484768050719 / 25000) (77945662806009 / 100000) := by
  exact
    packedTile32768 779438336 779503872 13 3219 27918 30 _ _ (2047407 / 100000) (204741 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779503872 :
    ThetaLowerSegment 779503872 779569408 (77945662806009 / 100000) (38976081674317 / 50000) := by
  exact
    packedTile32768 779503872 779569408 13 3175 27919 30 _ _ (409483 / 20000) (1023709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779569408 :
    ThetaLowerSegment 779569408 779634944 (38976081674317 / 50000) (38979363694989 / 50000) := by
  exact
    packedTile32768 779569408 779634944 13 3206 27920 30 _ _ (63982 / 3125) (2047427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779634944 :
    ThetaLowerSegment 779634944 779700480 (38979363694989 / 50000) (38982624230449 / 50000) := by
  exact
    packedTile32768 779634944 779700480 13 3185 27921 30 _ _ (255929 / 12500) (409487 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779700480 :
    ThetaLowerSegment 779700480 779766016 (38982624230449 / 50000) (77971904691589 / 100000) := by
  exact
    packedTile32768 779700480 779766016 13 3251 27923 30 _ _ (2047441 / 100000) (511861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779766016 :
    ThetaLowerSegment 779766016 779831552 (77971904691589 / 100000) (3898922724047 / 5000) := by
  exact
    packedTile32768 779766016 779831552 13 3199 27924 30 _ _ (2047449 / 100000) (511863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779831552 :
    ThetaLowerSegment 779831552 779897088 (3898922724047 / 5000) (15597027885609 / 20000) := by
  exact
    packedTile32768 779831552 779897088 13 3265 27925 30 _ _ (2047457 / 100000) (102373 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779897088 :
    ThetaLowerSegment 779897088 779962624 (15597027885609 / 20000) (77991730221099 / 100000) := by
  exact
    packedTile32768 779897088 779962624 13 3219 27926 30 _ _ (1023733 / 50000) (2047469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell779962624 :
    ThetaLowerSegment 779962624 780028160 (77991730221099 / 100000) (77998200238939 / 100000) := by
  exact
    packedTile32768 779962624 780028160 13 3160 27927 30 _ _ (1023737 / 50000) (2047477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780028160 :
    ThetaLowerSegment 780028160 780093696 (77998200238939 / 100000) (1950119162923 / 2500) := by
  exact
    packedTile32768 780028160 780093696 13 3207 27928 30 _ _ (2047483 / 100000) (1023743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780093696 :
    ThetaLowerSegment 780093696 780159232 (1950119162923 / 2500) (78011263205863 / 100000) := by
  exact
    packedTile32768 780093696 780159232 13 3173 27930 30 _ _ (2047491 / 100000) (1023747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780159232 :
    ThetaLowerSegment 780159232 780224768 (78011263205863 / 100000) (78017950337597 / 100000) := by
  exact
    packedTile32768 780159232 780224768 13 3266 27931 30 _ _ (2047499 / 100000) (1023751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780224768 :
    ThetaLowerSegment 780224768 780290304 (78017950337597 / 100000) (78024635451217 / 100000) := by
  exact
    packedTile32768 780224768 780290304 13 3265 27932 30 _ _ (511877 / 25000) (2047511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780290304 :
    ThetaLowerSegment 780290304 780355840 (78024635451217 / 100000) (78031013463557 / 100000) := by
  exact
    packedTile32768 780290304 780355840 13 3115 27933 30 _ _ (511879 / 25000) (2047519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780355840 :
    ThetaLowerSegment 780355840 780421376 (78031013463557 / 100000) (78037471357407 / 100000) := by
  exact
    packedTile32768 780355840 780421376 13 3154 27934 30 _ _ (81901 / 4000) (255941 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780421376 :
    ThetaLowerSegment 780421376 780486912 (78037471357407 / 100000) (15608794864443 / 20000) := by
  exact
    packedTile32768 780421376 780486912 13 3176 27936 30 _ _ (2047533 / 100000) (127971 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780486912 :
    ThetaLowerSegment 780486912 780552448 (15608794864443 / 20000) (7805055716653 / 10000) := by
  exact
    packedTile32768 780486912 780552448 13 3215 27937 30 _ _ (2047541 / 100000) (255943 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780552448 :
    ThetaLowerSegment 780552448 780617984 (7805055716653 / 10000) (3902854954439 / 5000) := by
  exact
    packedTile32768 780552448 780617984 13 3195 27938 30 _ _ (40951 / 2000) (2047553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780617984 :
    ThetaLowerSegment 780617984 780683520 (3902854954439 / 5000) (39031855326781 / 50000) := by
  exact
    packedTile32768 780617984 780683520 13 3229 27939 30 _ _ (1023779 / 50000) (2047561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780683520 :
    ThetaLowerSegment 780683520 780749056 (39031855326781 / 50000) (78070264915529 / 100000) := by
  exact
    packedTile32768 780683520 780749056 13 3201 27940 30 _ _ (2047567 / 100000) (204757 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780749056 :
    ThetaLowerSegment 780749056 780814592 (78070264915529 / 100000) (78076886773079 / 100000) := by
  exact
    packedTile32768 780749056 780814592 13 3234 27941 30 _ _ (81903 / 4000) (1023789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780814592 :
    ThetaLowerSegment 780814592 780880128 (78076886773079 / 100000) (15616676341271 / 20000) := by
  exact
    packedTile32768 780814592 780880128 13 3172 27943 30 _ _ (2047583 / 100000) (1023793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780880128 :
    ThetaLowerSegment 780880128 780945664 (15616676341271 / 20000) (78090003618883 / 100000) := by
  exact
    packedTile32768 780880128 780945664 13 3234 27944 30 _ _ (255949 / 12500) (409519 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell780945664 :
    ThetaLowerSegment 780945664 781011200 (78090003618883 / 100000) (78096541605683 / 100000) := by
  exact
    packedTile32768 780945664 781011200 13 3193 27945 30 _ _ (5119 / 250) (2047603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781011200 :
    ThetaLowerSegment 781011200 781076736 (78096541605683 / 100000) (78103040716649 / 100000) := by
  exact
    packedTile32768 781011200 781076736 13 3174 27946 30 _ _ (2047609 / 100000) (511903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781076736 :
    ThetaLowerSegment 781076736 781142272 (78103040716649 / 100000) (39054818045503 / 50000) := by
  exact
    packedTile32768 781076736 781142272 13 3221 27947 30 _ _ (2047617 / 100000) (102381 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781142272 :
    ThetaLowerSegment 781142272 781207808 (39054818045503 / 50000) (78116194633881 / 100000) := by
  exact
    packedTile32768 781142272 781207808 13 3203 27948 30 _ _ (16381 / 800) (511907 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781207808 :
    ThetaLowerSegment 781207808 781273344 (78116194633881 / 100000) (78122792110629 / 100000) := by
  exact
    packedTile32768 781207808 781273344 13 3222 27950 30 _ _ (1023817 / 50000) (2047637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781273344 :
    ThetaLowerSegment 781273344 781338880 (78122792110629 / 100000) (15625888570369 / 20000) := by
  exact
    packedTile32768 781273344 781338880 13 3248 27951 30 _ _ (1023821 / 50000) (409529 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781338880 :
    ThetaLowerSegment 781338880 781404416 (15625888570369 / 20000) (15627211352269 / 20000) := by
  exact
    packedTile32768 781338880 781404416 13 3230 27952 30 _ _ (40953 / 2000) (2047653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781404416 :
    ThetaLowerSegment 781404416 781469952 (15627211352269 / 20000) (78142728034367 / 100000) := by
  exact
    packedTile32768 781404416 781469952 13 3258 27953 30 _ _ (2047659 / 100000) (1023831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781469952 :
    ThetaLowerSegment 781469952 781535488 (78142728034367 / 100000) (39074633117549 / 50000) := by
  exact
    packedTile32768 781469952 781535488 13 3193 27954 30 _ _ (2047667 / 100000) (204767 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781535488 :
    ThetaLowerSegment 781535488 781601024 (39074633117549 / 50000) (39077889946227 / 50000) := by
  exact
    packedTile32768 781535488 781601024 13 3181 27955 30 _ _ (511919 / 25000) (2047679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781601024 :
    ThetaLowerSegment 781601024 781666560 (39077889946227 / 50000) (39081130406157 / 50000) := by
  exact
    packedTile32768 781601024 781666560 13 3165 27957 30 _ _ (511921 / 25000) (2047687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781666560 :
    ThetaLowerSegment 781666560 781732096 (39081130406157 / 50000) (39084316614909 / 50000) := by
  exact
    packedTile32768 781666560 781732096 13 3112 27958 30 _ _ (511923 / 25000) (409539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781732096 :
    ThetaLowerSegment 781732096 781797632 (39084316614909 / 50000) (78175265733357 / 100000) := by
  exact
    packedTile32768 781732096 781797632 13 3239 27959 30 _ _ (2047701 / 100000) (255963 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781797632 :
    ThetaLowerSegment 781797632 781863168 (78175265733357 / 100000) (78181769257141 / 100000) := by
  exact
    packedTile32768 781797632 781863168 13 3176 27960 30 _ _ (2047709 / 100000) (63991 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781863168 :
    ThetaLowerSegment 781863168 781928704 (78181769257141 / 100000) (78188422292923 / 100000) := by
  exact
    packedTile32768 781863168 781928704 13 3249 27961 30 _ _ (1023859 / 50000) (2047721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781928704 :
    ThetaLowerSegment 781928704 781994240 (78188422292923 / 100000) (78194995493383 / 100000) := by
  exact
    packedTile32768 781928704 781994240 13 3210 27962 30 _ _ (1023863 / 50000) (2047729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell781994240 :
    ThetaLowerSegment 781994240 782059776 (78194995493383 / 100000) (78201572814991 / 100000) := by
  exact
    packedTile32768 781994240 782059776 13 3212 27964 30 _ _ (1023867 / 50000) (2047737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782059776 :
    ThetaLowerSegment 782059776 782125312 (78201572814991 / 100000) (78208129688077 / 100000) := by
  exact
    packedTile32768 782059776 782125312 13 3202 27965 30 _ _ (2047743 / 100000) (1023873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782125312 :
    ThetaLowerSegment 782125312 782190848 (78208129688077 / 100000) (78214649727261 / 100000) := by
  exact
    packedTile32768 782125312 782190848 13 3184 27966 30 _ _ (2047751 / 100000) (1023877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782190848 :
    ThetaLowerSegment 782190848 782256384 (78214649727261 / 100000) (3128847774601 / 4000) := by
  exact
    packedTile32768 782190848 782256384 13 3196 27967 30 _ _ (2047759 / 100000) (1023881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782256384 :
    ThetaLowerSegment 782256384 782321920 (3128847774601 / 4000) (78227782034681 / 100000) := by
  exact
    packedTile32768 782256384 782321920 13 3217 27968 30 _ _ (255971 / 12500) (2047771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782321920 :
    ThetaLowerSegment 782321920 782387456 (78227782034681 / 100000) (15646870669573 / 20000) := by
  exact
    packedTile32768 782321920 782387456 13 3209 27970 30 _ _ (63993 / 3125) (2047779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782387456 :
    ThetaLowerSegment 782387456 782452992 (15646870669573 / 20000) (15648180432859 / 20000) := by
  exact
    packedTile32768 782387456 782452992 13 3198 27971 30 _ _ (409557 / 20000) (511947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782452992 :
    ThetaLowerSegment 782452992 782518528 (15648180432859 / 20000) (78247442815137 / 100000) := by
  exact
    packedTile32768 782452992 782518528 13 3194 27972 30 _ _ (2047793 / 100000) (511949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782518528 :
    ThetaLowerSegment 782518528 782584064 (78247442815137 / 100000) (39126962052651 / 50000) := by
  exact
    packedTile32768 782518528 782584064 13 3165 27973 30 _ _ (2047801 / 100000) (511951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782584064 :
    ThetaLowerSegment 782584064 782649600 (39126962052651 / 50000) (39130265170181 / 50000) := by
  exact
    packedTile32768 782584064 782649600 13 3226 27974 30 _ _ (204781 / 10000) (2047813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782649600 :
    ThetaLowerSegment 782649600 782715136 (39130265170181 / 50000) (156534334637 / 200) := by
  exact
    packedTile32768 782649600 782715136 13 3241 27975 30 _ _ (1023909 / 50000) (2047821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782715136 :
    ThetaLowerSegment 782715136 782780672 (156534334637 / 200) (4892108290541 / 6250) := by
  exact
    packedTile32768 782715136 782780672 13 3206 27977 30 _ _ (1023913 / 50000) (2047829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782780672 :
    ThetaLowerSegment 782780672 782846208 (4892108290541 / 6250) (39140112142803 / 50000) := by
  exact
    packedTile32768 782780672 782846208 13 3170 27978 30 _ _ (409567 / 20000) (1023919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782846208 :
    ThetaLowerSegment 782846208 782911744 (39140112142803 / 50000) (15657356705347 / 20000) := by
  exact
    packedTile32768 782846208 782911744 13 3203 27979 30 _ _ (2047843 / 100000) (1023923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782911744 :
    ThetaLowerSegment 782911744 782977280 (15657356705347 / 20000) (15658687809147 / 20000) := by
  exact
    packedTile32768 782911744 782977280 13 3250 27980 30 _ _ (511963 / 25000) (409571 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell782977280 :
    ThetaLowerSegment 782977280 783042816 (15658687809147 / 20000) (15659999258691 / 20000) := by
  exact
    packedTile32768 782977280 783042816 13 3202 27981 30 _ _ (102393 / 5000) (2047863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783042816 :
    ThetaLowerSegment 783042816 783108352 (15659999258691 / 20000) (78306594524151 / 100000) := by
  exact
    packedTile32768 783042816 783108352 13 3222 27982 30 _ _ (511967 / 25000) (2047871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783108352 :
    ThetaLowerSegment 783108352 783173888 (78306594524151 / 100000) (7831320302323 / 10000) := by
  exact
    packedTile32768 783108352 783173888 13 3227 27984 30 _ _ (2047877 / 100000) (51197 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783173888 :
    ThetaLowerSegment 783173888 783239424 (7831320302323 / 10000) (1957991551313 / 2500) := by
  exact
    packedTile32768 783173888 783239424 13 3154 27985 30 _ _ (409577 / 20000) (127993 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783239424 :
    ThetaLowerSegment 783239424 783304960 (1957991551313 / 2500) (78326274699017 / 100000) := by
  exact
    packedTile32768 783239424 783304960 13 3229 27986 30 _ _ (2047893 / 100000) (255987 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783304960 :
    ThetaLowerSegment 783304960 783370496 (78326274699017 / 100000) (78332893518281 / 100000) := by
  exact
    packedTile32768 783304960 783370496 13 3232 27987 30 _ _ (1023951 / 50000) (409581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783370496 :
    ThetaLowerSegment 783370496 783436032 (78332893518281 / 100000) (78339446830281 / 100000) := by
  exact
    packedTile32768 783370496 783436032 13 3200 27988 30 _ _ (204791 / 10000) (2047913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783436032 :
    ThetaLowerSegment 783436032 783501568 (78339446830281 / 100000) (78345889580309 / 100000) := by
  exact
    packedTile32768 783436032 783501568 13 3146 27989 30 _ _ (1023959 / 50000) (2047921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783501568 :
    ThetaLowerSegment 783501568 783567104 (78345889580309 / 100000) (78352488001103 / 100000) := by
  exact
    packedTile32768 783501568 783567104 13 3222 27991 30 _ _ (2047927 / 100000) (204793 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783567104 :
    ThetaLowerSegment 783567104 783632640 (78352488001103 / 100000) (19589782363577 / 25000) := by
  exact
    packedTile32768 783567104 783632640 13 3243 27992 30 _ _ (409587 / 20000) (1023969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783632640 :
    ThetaLowerSegment 783632640 783698176 (19589782363577 / 25000) (19591420718777 / 25000) := by
  exact
    packedTile32768 783632640 783698176 13 3200 27993 30 _ _ (255993 / 12500) (2047947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783698176 :
    ThetaLowerSegment 783698176 783763712 (19591420718777 / 25000) (19593070344113 / 25000) := by
  exact
    packedTile32768 783698176 783763712 13 3222 27994 30 _ _ (127997 / 6250) (409591 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783763712 :
    ThetaLowerSegment 783763712 783829248 (19593070344113 / 25000) (19594688744503 / 25000) := by
  exact
    packedTile32768 783763712 783829248 13 3161 27995 30 _ _ (51199 / 2500) (2047963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783829248 :
    ThetaLowerSegment 783829248 783894784 (19594688744503 / 25000) (78385380157727 / 100000) := by
  exact
    packedTile32768 783829248 783894784 13 3235 27996 30 _ _ (2047969 / 100000) (511993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783894784 :
    ThetaLowerSegment 783894784 783960320 (78385380157727 / 100000) (979899401449 / 1250) := by
  exact
    packedTile32768 783894784 783960320 13 3209 27998 30 _ _ (2047977 / 100000) (102399 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell783960320 :
    ThetaLowerSegment 783960320 784025856 (979899401449 / 1250) (156797126023 / 200) := by
  exact
    packedTile32768 783960320 784025856 13 3228 27999 30 _ _ (409597 / 20000) (511997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784025856 :
    ThetaLowerSegment 784025856 784091392 (156797126023 / 200) (39202506072303 / 50000) := by
  exact
    packedTile32768 784025856 784091392 13 3149 28000 30 _ _ (1023997 / 50000) (2047997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784091392 :
    ThetaLowerSegment 784091392 784156928 (39202506072303 / 50000) (39205809499529 / 50000) := by
  exact
    packedTile32768 784091392 784156928 13 3226 28001 30 _ _ (1024001 / 50000) (409601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784156928 :
    ThetaLowerSegment 784156928 784222464 (39205809499529 / 50000) (39209096555579 / 50000) := by
  exact
    packedTile32768 784156928 784222464 13 3210 28002 30 _ _ (204801 / 10000) (2048013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784222464 :
    ThetaLowerSegment 784222464 784288000 (39209096555579 / 50000) (1960616518879 / 2500) := by
  exact
    packedTile32768 784222464 784288000 13 3158 28003 30 _ _ (2048019 / 100000) (1024011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784288000 :
    ThetaLowerSegment 784288000 784353536 (1960616518879 / 2500) (490194578253 / 625) := by
  exact
    packedTile32768 784288000 784353536 13 3160 28005 30 _ _ (2048027 / 100000) (204803 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784353536 :
    ThetaLowerSegment 784353536 784419072 (490194578253 / 625) (9804714363523 / 12500) := by
  exact
    packedTile32768 784353536 784419072 13 3214 28006 30 _ _ (512009 / 25000) (2048039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784419072 :
    ThetaLowerSegment 784419072 784484608 (9804714363523 / 12500) (19611055385993 / 25000) := by
  exact
    packedTile32768 784419072 784484608 13 3177 28007 30 _ _ (512011 / 25000) (2048047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784484608 :
    ThetaLowerSegment 784484608 784550144 (19611055385993 / 25000) (98063312974 / 125) := by
  exact
    packedTile32768 784484608 784550144 13 3139 28008 30 _ _ (512013 / 25000) (409611 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784550144 :
    ThetaLowerSegment 784550144 784615680 (98063312974 / 125) (78457263568169 / 100000) := by
  exact
    packedTile32768 784550144 784615680 13 3229 28009 30 _ _ (2048061 / 100000) (64002 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784615680 :
    ThetaLowerSegment 784615680 784681216 (78457263568169 / 100000) (78463862446487 / 100000) := by
  exact
    packedTile32768 784615680 784681216 13 3222 28010 30 _ _ (2048069 / 100000) (256009 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784681216 :
    ThetaLowerSegment 784681216 784746752 (78463862446487 / 100000) (78470453158273 / 100000) := by
  exact
    packedTile32768 784681216 784746752 13 3218 28012 30 _ _ (2048077 / 100000) (25601 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784746752 :
    ThetaLowerSegment 784746752 784812288 (78470453158273 / 100000) (78477109437773 / 100000) := by
  exact
    packedTile32768 784746752 784812288 13 3250 28013 30 _ _ (1024043 / 50000) (2048089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784812288 :
    ThetaLowerSegment 784812288 784877824 (78477109437773 / 100000) (78483640809539 / 100000) := by
  exact
    packedTile32768 784812288 784877824 13 3189 28014 30 _ _ (1024047 / 50000) (2048097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784877824 :
    ThetaLowerSegment 784877824 784943360 (78483640809539 / 100000) (78490164014409 / 100000) := by
  exact
    packedTile32768 784877824 784943360 13 3185 28015 30 _ _ (1024051 / 50000) (409621 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell784943360 :
    ThetaLowerSegment 784943360 785008896 (78490164014409 / 100000) (78496828567603 / 100000) := by
  exact
    packedTile32768 784943360 785008896 13 3254 28016 30 _ _ (2048111 / 100000) (1024057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785008896 :
    ThetaLowerSegment 785008896 785074432 (78496828567603 / 100000) (78503415318307 / 100000) := by
  exact
    packedTile32768 785008896 785074432 13 3216 28018 30 _ _ (2048119 / 100000) (1024061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785074432 :
    ThetaLowerSegment 785074432 785139968 (78503415318307 / 100000) (15701999599697 / 20000) := by
  exact
    packedTile32768 785074432 785139968 13 3214 28019 30 _ _ (2048127 / 100000) (204813 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785139968 :
    ThetaLowerSegment 785139968 785205504 (15701999599697 / 20000) (78516502878421 / 100000) := by
  exact
    packedTile32768 785139968 785205504 13 3176 28020 30 _ _ (256017 / 12500) (2048139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785205504 :
    ThetaLowerSegment 785205504 785271040 (78516502878421 / 100000) (78523196213013 / 100000) := by
  exact
    packedTile32768 785205504 785271040 13 3268 28021 30 _ _ (128009 / 6250) (2048147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785271040 :
    ThetaLowerSegment 785271040 785336576 (78523196213013 / 100000) (78529694999309 / 100000) := by
  exact
    packedTile32768 785271040 785336576 13 3173 28022 30 _ _ (256019 / 12500) (409631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785336576 :
    ThetaLowerSegment 785336576 785402112 (78529694999309 / 100000) (2454254904602 / 3125) := by
  exact
    packedTile32768 785336576 785402112 13 3155 28023 30 _ _ (2048161 / 100000) (512041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785402112 :
    ThetaLowerSegment 785402112 785467648 (2454254904602 / 3125) (392712981953 / 500) := by
  exact
    packedTile32768 785402112 785467648 13 3144 28025 30 _ _ (2048169 / 100000) (512043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785467648 :
    ThetaLowerSegment 785467648 785533184 (392712981953 / 500) (78549123930699 / 100000) := by
  exact
    packedTile32768 785467648 785533184 13 3187 28026 30 _ _ (2048177 / 100000) (102409 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785533184 :
    ThetaLowerSegment 785533184 785598720 (78549123930699 / 100000) (78555805113431 / 100000) := by
  exact
    packedTile32768 785533184 785598720 13 3262 28027 30 _ _ (1024093 / 50000) (2048189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785598720 :
    ThetaLowerSegment 785598720 785664256 (78555805113431 / 100000) (78562388008947 / 100000) := by
  exact
    packedTile32768 785598720 785664256 13 3214 28028 30 _ _ (1024097 / 50000) (2048197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785664256 :
    ThetaLowerSegment 785664256 785729792 (78562388008947 / 100000) (78568979126201 / 100000) := by
  exact
    packedTile32768 785664256 785729792 13 3218 28029 30 _ _ (2048203 / 100000) (1024103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785729792 :
    ThetaLowerSegment 785729792 785795328 (78568979126201 / 100000) (39287802544393 / 50000) := by
  exact
    packedTile32768 785729792 785795328 13 3235 28030 30 _ _ (2048211 / 100000) (1024107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785795328 :
    ThetaLowerSegment 785795328 785860864 (39287802544393 / 50000) (15716440480437 / 20000) := by
  exact
    packedTile32768 785795328 785860864 13 3221 28032 30 _ _ (2048219 / 100000) (1024111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785860864 :
    ThetaLowerSegment 785860864 785926400 (15716440480437 / 20000) (78588758780013 / 100000) := by
  exact
    packedTile32768 785860864 785926400 13 3201 28033 30 _ _ (512057 / 25000) (2048231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785926400 :
    ThetaLowerSegment 785926400 785991936 (78588758780013 / 100000) (78595311086977 / 100000) := by
  exact
    packedTile32768 785926400 785991936 13 3199 28034 30 _ _ (512059 / 25000) (2048239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell785991936 :
    ThetaLowerSegment 785991936 786057472 (78595311086977 / 100000) (78601842937093 / 100000) := by
  exact
    packedTile32768 785991936 786057472 13 3189 28035 30 _ _ (512061 / 25000) (2048247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786057472 :
    ThetaLowerSegment 786057472 786123008 (78601842937093 / 100000) (7860841578097 / 10000) := by
  exact
    packedTile32768 786057472 786123008 13 3209 28036 30 _ _ (2048253 / 100000) (64008 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786123008 :
    ThetaLowerSegment 786123008 786188544 (7860841578097 / 10000) (39307509687217 / 50000) := by
  exact
    packedTile32768 786123008 786188544 13 3224 28037 30 _ _ (2048261 / 100000) (256033 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786188544 :
    ThetaLowerSegment 786188544 786254080 (39307509687217 / 50000) (78621579980041 / 100000) := by
  exact
    packedTile32768 786188544 786254080 13 3203 28039 30 _ _ (2048269 / 100000) (128017 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786254080 :
    ThetaLowerSegment 786254080 786319616 (78621579980041 / 100000) (78628154952421 / 100000) := by
  exact
    packedTile32768 786254080 786319616 13 3210 28040 30 _ _ (1024139 / 50000) (2048281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786319616 :
    ThetaLowerSegment 786319616 786385152 (78628154952421 / 100000) (78634756578199 / 100000) := by
  exact
    packedTile32768 786319616 786385152 13 3223 28041 30 _ _ (1024143 / 50000) (2048289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786385152 :
    ThetaLowerSegment 786385152 786450688 (78634756578199 / 100000) (78641343891703 / 100000) := by
  exact
    packedTile32768 786385152 786450688 13 3216 28042 30 _ _ (1024147 / 50000) (2048297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786450688 :
    ThetaLowerSegment 786450688 786516224 (78641343891703 / 100000) (78647841108819 / 100000) := by
  exact
    packedTile32768 786450688 786516224 13 3172 28043 30 _ _ (2048303 / 100000) (1024153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786516224 :
    ThetaLowerSegment 786516224 786581760 (78647841108819 / 100000) (39327211166031 / 50000) := by
  exact
    packedTile32768 786516224 786581760 13 3213 28044 30 _ _ (2048311 / 100000) (1024157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786581760 :
    ThetaLowerSegment 786581760 786647296 (39327211166031 / 50000) (39330447510051 / 50000) := by
  exact
    packedTile32768 786581760 786647296 13 3160 28046 30 _ _ (2048319 / 100000) (1024161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786647296 :
    ThetaLowerSegment 786647296 786712832 (39330447510051 / 50000) (39333754535607 / 50000) := by
  exact
    packedTile32768 786647296 786712832 13 3229 28047 30 _ _ (256041 / 12500) (2048331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786712832 :
    ThetaLowerSegment 786712832 786778368 (39333754535607 / 50000) (39337031873207 / 50000) := by
  exact
    packedTile32768 786712832 786778368 13 3200 28048 30 _ _ (128021 / 6250) (2048339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786778368 :
    ThetaLowerSegment 786778368 786843904 (39337031873207 / 50000) (39340339948767 / 50000) := by
  exact
    packedTile32768 786778368 786843904 13 3230 28049 30 _ _ (256043 / 12500) (2048347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786843904 :
    ThetaLowerSegment 786843904 786909440 (39340339948767 / 50000) (19671791245783 / 25000) := by
  exact
    packedTile32768 786843904 786909440 13 3166 28050 30 _ _ (2048353 / 100000) (512089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786909440 :
    ThetaLowerSegment 786909440 786974976 (19671791245783 / 25000) (78693652142419 / 100000) := by
  exact
    packedTile32768 786909440 786974976 13 3167 28051 30 _ _ (2048361 / 100000) (512091 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell786974976 :
    ThetaLowerSegment 786974976 787040512 (78693652142419 / 100000) (78700206923219 / 100000) := by
  exact
    packedTile32768 786974976 787040512 13 3200 28053 30 _ _ (2048369 / 100000) (512093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787040512 :
    ThetaLowerSegment 787040512 787106048 (78700206923219 / 100000) (78706802700379 / 100000) := by
  exact
    packedTile32768 787040512 787106048 13 3220 28054 30 _ _ (1024189 / 50000) (2048381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787106048 :
    ThetaLowerSegment 787106048 787171584 (78706802700379 / 100000) (78713285842069 / 100000) := by
  exact
    packedTile32768 787106048 787171584 13 3165 28055 30 _ _ (1024193 / 50000) (2048389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787171584 :
    ThetaLowerSegment 787171584 787237120 (78713285842069 / 100000) (78719857090021 / 100000) := by
  exact
    packedTile32768 787171584 787237120 13 3208 28056 30 _ _ (1024197 / 50000) (2048397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787237120 :
    ThetaLowerSegment 787237120 787302656 (78719857090021 / 100000) (78726383301979 / 100000) := by
  exact
    packedTile32768 787237120 787302656 13 3186 28057 30 _ _ (2048403 / 100000) (1024203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787302656 :
    ThetaLowerSegment 787302656 787368192 (78726383301979 / 100000) (15746577811063 / 20000) := by
  exact
    packedTile32768 787302656 787368192 13 3176 28058 30 _ _ (2048411 / 100000) (1024207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787368192 :
    ThetaLowerSegment 787368192 787433728 (15746577811063 / 20000) (39369698441239 / 50000) := by
  exact
    packedTile32768 787368192 787433728 13 3177 28060 30 _ _ (2048419 / 100000) (1024211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787433728 :
    ThetaLowerSegment 787433728 787499264 (39369698441239 / 50000) (39372939052753 / 50000) := by
  exact
    packedTile32768 787433728 787499264 13 3164 28061 30 _ _ (2048427 / 100000) (204843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787499264 :
    ThetaLowerSegment 787499264 787564800 (39372939052753 / 50000) (39376214501917 / 50000) := by
  exact
    packedTile32768 787499264 787564800 13 3198 28062 30 _ _ (512109 / 25000) (2048439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787564800 :
    ThetaLowerSegment 787564800 787630336 (39376214501917 / 50000) (39379519666311 / 50000) := by
  exact
    packedTile32768 787564800 787630336 13 3227 28063 30 _ _ (512111 / 25000) (2048447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787630336 :
    ThetaLowerSegment 787630336 787695872 (39379519666311 / 50000) (39382768511183 / 50000) := by
  exact
    packedTile32768 787630336 787695872 13 3172 28064 30 _ _ (512113 / 25000) (409691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787695872 :
    ThetaLowerSegment 787695872 787761408 (39382768511183 / 50000) (2461628518193 / 3125) := by
  exact
    packedTile32768 787695872 787761408 13 3210 28065 30 _ _ (2048461 / 100000) (128029 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787761408 :
    ThetaLowerSegment 787761408 787826944 (2461628518193 / 3125) (78778653343693 / 100000) := by
  exact
    packedTile32768 787761408 787826944 13 3193 28067 30 _ _ (2048469 / 100000) (256059 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787826944 :
    ThetaLowerSegment 787826944 787892480 (78778653343693 / 100000) (78785237148771 / 100000) := by
  exact
    packedTile32768 787826944 787892480 13 3214 28068 30 _ _ (2048477 / 100000) (12803 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787892480 :
    ThetaLowerSegment 787892480 787958016 (78785237148771 / 100000) (78791741091821 / 100000) := by
  exact
    packedTile32768 787892480 787958016 13 3175 28069 30 _ _ (1024243 / 50000) (2048489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell787958016 :
    ThetaLowerSegment 787958016 788023552 (78791741091821 / 100000) (78798251205753 / 100000) := by
  exact
    packedTile32768 787958016 788023552 13 3178 28070 30 _ _ (1024247 / 50000) (2048497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788023552 :
    ThetaLowerSegment 788023552 788089088 (78798251205753 / 100000) (78804810509157 / 100000) := by
  exact
    packedTile32768 788023552 788089088 13 3202 28071 30 _ _ (1024251 / 50000) (409701 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788089088 :
    ThetaLowerSegment 788089088 788154624 (78804810509157 / 100000) (39405718721121 / 50000) := by
  exact
    packedTile32768 788089088 788154624 13 3235 28072 30 _ _ (2048511 / 100000) (1024257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788154624 :
    ThetaLowerSegment 788154624 788220160 (39405718721121 / 50000) (78817892325611 / 100000) := by
  exact
    packedTile32768 788154624 788220160 13 3151 28074 30 _ _ (2048519 / 100000) (1024261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788220160 :
    ThetaLowerSegment 788220160 788285696 (78817892325611 / 100000) (19706099099709 / 25000) := by
  exact
    packedTile32768 788220160 788285696 13 3175 28075 30 _ _ (2048527 / 100000) (204853 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788285696 :
    ThetaLowerSegment 788285696 788351232 (19706099099709 / 25000) (19707743049849 / 25000) := by
  exact
    packedTile32768 788285696 788351232 13 3210 28076 30 _ _ (256067 / 12500) (2048539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788351232 :
    ThetaLowerSegment 788351232 788416768 (19707743049849 / 25000) (19709375739417 / 25000) := by
  exact
    packedTile32768 788351232 788416768 13 3188 28077 30 _ _ (64017 / 3125) (2048547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788416768 :
    ThetaLowerSegment 788416768 788482304 (19709375739417 / 25000) (19711006898947 / 25000) := by
  exact
    packedTile32768 788416768 788482304 13 3185 28078 30 _ _ (256069 / 12500) (409711 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788482304 :
    ThetaLowerSegment 788482304 788547840 (19711006898947 / 25000) (39425240281469 / 50000) := by
  exact
    packedTile32768 788482304 788547840 13 3150 28079 30 _ _ (2048561 / 100000) (512141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788547840 :
    ThetaLowerSegment 788547840 788613376 (39425240281469 / 50000) (9857137180101 / 12500) := by
  exact
    packedTile32768 788547840 788613376 13 3230 28081 30 _ _ (2048569 / 100000) (512143 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788613376 :
    ThetaLowerSegment 788613376 788678912 (9857137180101 / 12500) (78863671324401 / 100000) := by
  exact
    packedTile32768 788613376 788678912 13 3209 28082 30 _ _ (2048577 / 100000) (102429 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788678912 :
    ThetaLowerSegment 788678912 788744448 (78863671324401 / 100000) (39435225046083 / 50000) := by
  exact
    packedTile32768 788678912 788744448 13 3309 28083 30 _ _ (409717 / 20000) (512147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788744448 :
    ThetaLowerSegment 788744448 788809984 (39435225046083 / 50000) (1577539538253 / 2000) := by
  exact
    packedTile32768 788744448 788809984 13 3186 28084 30 _ _ (1024297 / 50000) (2048597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788809984 :
    ThetaLowerSegment 788809984 788875520 (1577539538253 / 2000) (19720889767719 / 25000) := by
  exact
    packedTile32768 788809984 788875520 13 3213 28085 30 _ _ (1024301 / 50000) (409721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788875520 :
    ThetaLowerSegment 788875520 788941056 (19720889767719 / 25000) (39445103405163 / 50000) := by
  exact
    packedTile32768 788875520 788941056 13 3245 28086 30 _ _ (204861 / 10000) (2048613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell788941056 :
    ThetaLowerSegment 788941056 789006592 (39445103405163 / 50000) (3155868119247 / 4000) := by
  exact
    packedTile32768 788941056 789006592 13 3171 28088 30 _ _ (2048619 / 100000) (1024311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789006592 :
    ThetaLowerSegment 789006592 789072128 (3155868119247 / 4000) (78903324143639 / 100000) := by
  exact
    packedTile32768 789006592 789072128 13 3232 28089 30 _ _ (2048627 / 100000) (204863 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789072128 :
    ThetaLowerSegment 789072128 789137664 (78903324143639 / 100000) (2465934447207 / 3125) := by
  exact
    packedTile32768 789072128 789137664 13 3211 28090 30 _ _ (409727 / 20000) (1024319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789137664 :
    ThetaLowerSegment 789137664 789203200 (2465934447207 / 3125) (19729140613067 / 25000) := by
  exact
    packedTile32768 789137664 789203200 13 3251 28091 30 _ _ (512161 / 25000) (2048647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789203200 :
    ThetaLowerSegment 789203200 789268736 (19729140613067 / 25000) (4932694243463 / 6250) := by
  exact
    packedTile32768 789203200 789268736 13 3195 28092 30 _ _ (512163 / 25000) (409731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789268736 :
    ThetaLowerSegment 789268736 789334272 (4932694243463 / 6250) (19732420511337 / 25000) := by
  exact
    packedTile32768 789268736 789334272 13 3209 28093 30 _ _ (102433 / 5000) (2048663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789334272 :
    ThetaLowerSegment 789334272 789399808 (19732420511337 / 25000) (78936227542803 / 100000) := by
  exact
    packedTile32768 789334272 789399808 13 3195 28095 30 _ _ (2048669 / 100000) (64021 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789399808 :
    ThetaLowerSegment 789399808 789465344 (78936227542803 / 100000) (39471374240847 / 50000) := by
  exact
    packedTile32768 789399808 789465344 13 3183 28096 30 _ _ (2048677 / 100000) (51217 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789465344 :
    ThetaLowerSegment 789465344 789530880 (39471374240847 / 50000) (78949294030269 / 100000) := by
  exact
    packedTile32768 789465344 789530880 13 3195 28097 30 _ _ (409737 / 20000) (128043 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789530880 :
    ThetaLowerSegment 789530880 789596416 (78949294030269 / 100000) (39477893169193 / 50000) := by
  exact
    packedTile32768 789530880 789596416 13 3169 28098 30 _ _ (2048693 / 100000) (256087 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789596416 :
    ThetaLowerSegment 789596416 789661952 (39477893169193 / 50000) (19740605521041 / 25000) := by
  exact
    packedTile32768 789596416 789661952 13 3239 28099 30 _ _ (1024351 / 50000) (409741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789661952 :
    ThetaLowerSegment 789661952 789727488 (19740605521041 / 25000) (39484537122767 / 50000) := by
  exact
    packedTile32768 789661952 789727488 13 3247 28100 30 _ _ (204871 / 10000) (2048713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789727488 :
    ThetaLowerSegment 789727488 789793024 (39484537122767 / 50000) (39487808925413 / 50000) := by
  exact
    packedTile32768 789727488 789793024 13 3194 28102 30 _ _ (1024359 / 50000) (2048721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789793024 :
    ThetaLowerSegment 789793024 789858560 (39487808925413 / 50000) (78982245482671 / 100000) := by
  exact
    packedTile32768 789793024 789858560 13 3235 28103 30 _ _ (2048727 / 100000) (204873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789858560 :
    ThetaLowerSegment 789858560 789924096 (78982245482671 / 100000) (78988850604311 / 100000) := by
  exact
    packedTile32768 789858560 789924096 13 3224 28104 30 _ _ (409747 / 20000) (1024369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789924096 :
    ThetaLowerSegment 789924096 789989632 (78988850604311 / 100000) (9874427615389 / 12500) := by
  exact
    packedTile32768 789924096 789989632 13 3207 28105 30 _ _ (2048743 / 100000) (1024373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell789989632 :
    ThetaLowerSegment 789989632 790055168 (9874427615389 / 12500) (9875255567291 / 12500) := by
  exact
    packedTile32768 789989632 790055168 13 3233 28106 30 _ _ (128047 / 6250) (409751 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790055168 :
    ThetaLowerSegment 790055168 790120704 (9875255567291 / 12500) (2469017167229 / 3125) := by
  exact
    packedTile32768 790055168 790120704 13 3175 28107 30 _ _ (51219 / 2500) (2048763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790120704 :
    ThetaLowerSegment 790120704 790186240 (2469017167229 / 3125) (98768827981 / 125) := by
  exact
    packedTile32768 790120704 790186240 13 3179 28109 30 _ _ (64024 / 3125) (2048771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790186240 :
    ThetaLowerSegment 790186240 790251776 (98768827981 / 125) (4938848849377 / 6250) := by
  exact
    packedTile32768 790186240 790251776 13 3182 28110 30 _ _ (256097 / 12500) (2048779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790251776 :
    ThetaLowerSegment 790251776 790317312 (4938848849377 / 6250) (39514074997371 / 50000) := by
  exact
    packedTile32768 790251776 790317312 13 3206 28111 30 _ _ (409757 / 20000) (512197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790317312 :
    ThetaLowerSegment 790317312 790382848 (39514074997371 / 50000) (790347184251 / 1000) := by
  exact
    packedTile32768 790317312 790382848 13 3206 28112 30 _ _ (2048793 / 100000) (512199 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790382848 :
    ThetaLowerSegment 790382848 790448384 (790347184251 / 1000) (39520631147747 / 50000) := by
  exact
    packedTile32768 790382848 790448384 13 3194 28113 30 _ _ (2048801 / 100000) (512201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790448384 :
    ThetaLowerSegment 790448384 790513920 (39520631147747 / 50000) (39523991196147 / 50000) := by
  exact
    packedTile32768 790448384 790513920 13 3280 28114 30 _ _ (204881 / 10000) (2048813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790513920 :
    ThetaLowerSegment 790513920 790579456 (39523991196147 / 50000) (3952729696399 / 5000) := by
  exact
    packedTile32768 790513920 790579456 13 3227 28116 30 _ _ (1024409 / 50000) (2048821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790579456 :
    ThetaLowerSegment 790579456 790644992 (3952729696399 / 5000) (9882637112713 / 12500) := by
  exact
    packedTile32768 790579456 790644992 13 3174 28117 30 _ _ (1024413 / 50000) (2048829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790644992 :
    ThetaLowerSegment 790644992 790710528 (9882637112713 / 12500) (9883475085819 / 12500) := by
  exact
    packedTile32768 790644992 790710528 13 3272 28118 30 _ _ (1024417 / 50000) (2048837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790710528 :
    ThetaLowerSegment 790710528 790776064 (9883475085819 / 12500) (39537196931663 / 50000) := by
  exact
    packedTile32768 790710528 790776064 13 3218 28119 30 _ _ (2048843 / 100000) (1024423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790776064 :
    ThetaLowerSegment 790776064 790841600 (39537196931663 / 50000) (3954046894671 / 5000) := by
  exact
    packedTile32768 790776064 790841600 13 3194 28120 30 _ _ (2048851 / 100000) (1024427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790841600 :
    ThetaLowerSegment 790841600 790907136 (3954046894671 / 5000) (1977184282767 / 2500) := by
  exact
    packedTile32768 790841600 790907136 13 3140 28121 30 _ _ (2048859 / 100000) (1024431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790907136 :
    ThetaLowerSegment 790907136 790972672 (1977184282767 / 2500) (988672815561 / 1250) := by
  exact
    packedTile32768 790907136 790972672 13 3150 28123 30 _ _ (512217 / 25000) (2048871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell790972672 :
    ThetaLowerSegment 790972672 791038208 (988672815561 / 1250) (19775112315247 / 25000) := by
  exact
    packedTile32768 790972672 791038208 13 3233 28124 30 _ _ (512219 / 25000) (2048879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791038208 :
    ThetaLowerSegment 791038208 791103744 (19775112315247 / 25000) (4944189008109 / 6250) := by
  exact
    packedTile32768 791038208 791103744 13 3209 28125 30 _ _ (512221 / 25000) (2048887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791103744 :
    ThetaLowerSegment 791103744 791169280 (4944189008109 / 6250) (4944595713171 / 6250) := by
  exact
    packedTile32768 791103744 791169280 13 3176 28126 30 _ _ (512223 / 25000) (409779 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791169280 :
    ThetaLowerSegment 791169280 791234816 (4944595713171 / 6250) (15824029462413 / 20000) := by
  exact
    packedTile32768 791169280 791234816 13 3229 28127 30 _ _ (2048901 / 100000) (256113 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791234816 :
    ThetaLowerSegment 791234816 791300352 (15824029462413 / 20000) (19781671345171 / 25000) := by
  exact
    packedTile32768 791234816 791300352 13 3191 28128 30 _ _ (2048909 / 100000) (128057 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791300352 :
    ThetaLowerSegment 791300352 791365888 (19781671345171 / 25000) (2472909968127 / 3125) := by
  exact
    packedTile32768 791300352 791365888 13 3140 28130 30 _ _ (2048917 / 100000) (51223 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791365888 :
    ThetaLowerSegment 791365888 791431424 (2472909968127 / 3125) (19784946546317 / 25000) := by
  exact
    packedTile32768 791365888 791431424 13 3254 28131 30 _ _ (1024463 / 50000) (2048929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791431424 :
    ThetaLowerSegment 791431424 791496960 (19784946546317 / 25000) (2473323339748 / 3125) := by
  exact
    packedTile32768 791431424 791496960 13 3202 28132 30 _ _ (1024467 / 50000) (2048937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791496960 :
    ThetaLowerSegment 791496960 791562496 (2473323339748 / 3125) (39576399495147 / 50000) := by
  exact
    packedTile32768 791496960 791562496 13 3149 28133 30 _ _ (1024471 / 50000) (409789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791562496 :
    ThetaLowerSegment 791562496 791628032 (39576399495147 / 50000) (39579686010947 / 50000) := by
  exact
    packedTile32768 791562496 791628032 13 3208 28134 30 _ _ (40979 / 2000) (2048953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791628032 :
    ThetaLowerSegment 791628032 791693568 (39579686010947 / 50000) (494786721361 / 625) := by
  exact
    packedTile32768 791628032 791693568 13 3174 28135 30 _ _ (2048959 / 100000) (1024481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791693568 :
    ThetaLowerSegment 791693568 791759104 (494786721361 / 625) (9896551965053 / 12500) := by
  exact
    packedTile32768 791693568 791759104 13 3192 28137 30 _ _ (2048967 / 100000) (204897 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791759104 :
    ThetaLowerSegment 791759104 791824640 (9896551965053 / 12500) (79178982685299 / 100000) := by
  exact
    packedTile32768 791759104 791824640 13 3205 28138 30 _ _ (81959 / 4000) (1024489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791824640 :
    ThetaLowerSegment 791824640 791890176 (79178982685299 / 100000) (79185566070891 / 100000) := by
  exact
    packedTile32768 791824640 791890176 13 3213 28139 30 _ _ (256123 / 12500) (2048987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791890176 :
    ThetaLowerSegment 791890176 791955712 (79185566070891 / 100000) (633537835143 / 800) := by
  exact
    packedTile32768 791890176 791955712 13 3252 28140 30 _ _ (64031 / 3125) (409799 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell791955712 :
    ThetaLowerSegment 791955712 792021248 (633537835143 / 800) (633589699431 / 800) := by
  exact
    packedTile32768 791955712 792021248 13 3164 28141 30 _ _ (2049 / 100) (2049003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792021248 :
    ThetaLowerSegment 792021248 792086784 (633589699431 / 800) (15841029262799 / 20000) := by
  exact
    packedTile32768 792021248 792086784 13 3140 28142 30 _ _ (128063 / 6250) (2049011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792086784 :
    ThetaLowerSegment 792086784 792152320 (15841029262799 / 20000) (79211690874293 / 100000) := by
  exact
    packedTile32768 792086784 792152320 13 3194 28144 30 _ _ (2049017 / 100000) (102451 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792152320 :
    ThetaLowerSegment 792152320 792217856 (79211690874293 / 100000) (39609128999709 / 50000) := by
  exact
    packedTile32768 792152320 792217856 13 3205 28145 30 _ _ (81961 / 4000) (512257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792217856 :
    ThetaLowerSegment 792217856 792283392 (39609128999709 / 50000) (19806196554639 / 25000) := by
  exact
    packedTile32768 792217856 792283392 13 3186 28146 30 _ _ (2049033 / 100000) (512259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792283392 :
    ThetaLowerSegment 792283392 792348928 (19806196554639 / 25000) (15846276416307 / 20000) := by
  exact
    packedTile32768 792283392 792348928 13 3219 28147 30 _ _ (2049041 / 100000) (512261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792348928 :
    ThetaLowerSegment 792348928 792414464 (15846276416307 / 20000) (15847593545647 / 20000) := by
  exact
    packedTile32768 792348928 792414464 13 3214 28148 30 _ _ (40981 / 2000) (2049053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792414464 :
    ThetaLowerSegment 792414464 792480000 (15847593545647 / 20000) (15848880354071 / 20000) := by
  exact
    packedTile32768 792414464 792480000 13 3140 28149 30 _ _ (1024529 / 50000) (2049061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792480000 :
    ThetaLowerSegment 792480000 792545536 (15848880354071 / 20000) (79251018204469 / 100000) := by
  exact
    packedTile32768 792480000 792545536 13 3229 28151 30 _ _ (1024533 / 50000) (2049069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792545536 :
    ThetaLowerSegment 792545536 792611072 (79251018204469 / 100000) (79257628520419 / 100000) := by
  exact
    packedTile32768 792545536 792611072 13 3226 28152 30 _ _ (81963 / 4000) (1024539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792611072 :
    ThetaLowerSegment 792611072 792676608 (79257628520419 / 100000) (79264214273181 / 100000) := by
  exact
    packedTile32768 792611072 792676608 13 3214 28153 30 _ _ (2049083 / 100000) (1024543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792676608 :
    ThetaLowerSegment 792676608 792742144 (79264214273181 / 100000) (19817674911549 / 25000) := by
  exact
    packedTile32768 792676608 792742144 13 3165 28154 30 _ _ (2049091 / 100000) (1024547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792742144 :
    ThetaLowerSegment 792742144 792807680 (19817674911549 / 25000) (7927726905759 / 10000) := by
  exact
    packedTile32768 792742144 792807680 13 3206 28155 30 _ _ (2049099 / 100000) (1024551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792807680 :
    ThetaLowerSegment 792807680 792873216 (7927726905759 / 10000) (1585675294599 / 2000) := by
  exact
    packedTile32768 792807680 792873216 13 3170 28156 30 _ _ (512277 / 25000) (2049111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792873216 :
    ThetaLowerSegment 792873216 792938752 (1585675294599 / 2000) (39645205006569 / 50000) := by
  exact
    packedTile32768 792873216 792938752 13 3243 28158 30 _ _ (512279 / 25000) (2049119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell792938752 :
    ThetaLowerSegment 792938752 793004288 (39645205006569 / 50000) (39648508194457 / 50000) := by
  exact
    packedTile32768 792938752 793004288 13 3224 28159 30 _ _ (512281 / 25000) (2049127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793004288 :
    ThetaLowerSegment 793004288 793069824 (39648508194457 / 50000) (39651792953053 / 50000) := by
  exact
    packedTile32768 793004288 793069824 13 3206 28160 30 _ _ (512283 / 25000) (409827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793069824 :
    ThetaLowerSegment 793069824 793135360 (39651792953053 / 50000) (15862040516479 / 20000) := by
  exact
    packedTile32768 793069824 793135360 13 3229 28161 30 _ _ (2049141 / 100000) (256143 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793135360 :
    ThetaLowerSegment 793135360 793200896 (15862040516479 / 20000) (39658342020341 / 50000) := by
  exact
    packedTile32768 793135360 793200896 13 3163 28162 30 _ _ (2049149 / 100000) (64036 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793200896 :
    ThetaLowerSegment 793200896 793266432 (39658342020341 / 50000) (79323124541133 / 100000) := by
  exact
    packedTile32768 793200896 793266432 13 3143 28163 30 _ _ (2049157 / 100000) (51229 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793266432 :
    ThetaLowerSegment 793266432 793331968 (79323124541133 / 100000) (79329608099193 / 100000) := by
  exact
    packedTile32768 793266432 793331968 13 3164 28164 30 _ _ (409833 / 20000) (128073 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793331968 :
    ThetaLowerSegment 793331968 793397504 (79329608099193 / 100000) (79336071193989 / 100000) := by
  exact
    packedTile32768 793331968 793397504 13 3154 28166 30 _ _ (1024587 / 50000) (2049177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793397504 :
    ThetaLowerSegment 793397504 793463040 (79336071193989 / 100000) (79342567100929 / 100000) := by
  exact
    packedTile32768 793397504 793463040 13 3170 28167 30 _ _ (1024591 / 50000) (409837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793463040 :
    ThetaLowerSegment 793463040 793528576 (79342567100929 / 100000) (79349095820269 / 100000) := by
  exact
    packedTile32768 793463040 793528576 13 3186 28168 30 _ _ (204919 / 10000) (2049193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793528576 :
    ThetaLowerSegment 793528576 793594112 (79349095820269 / 100000) (15871119995579 / 20000) := by
  exact
    packedTile32768 793528576 793594112 13 3174 28169 30 _ _ (2049199 / 100000) (1024601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793594112 :
    ThetaLowerSegment 793594112 793659648 (15871119995579 / 20000) (39681190401929 / 50000) := by
  exact
    packedTile32768 793594112 793659648 13 3309 28170 30 _ _ (2049207 / 100000) (204921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793659648 :
    ThetaLowerSegment 793659648 793725184 (39681190401929 / 50000) (79369026408103 / 100000) := by
  exact
    packedTile32768 793659648 793725184 13 3243 28171 30 _ _ (409843 / 20000) (1024609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793725184 :
    ThetaLowerSegment 793725184 793790720 (79369026408103 / 100000) (79375563429473 / 100000) := by
  exact
    packedTile32768 793725184 793790720 13 3190 28173 30 _ _ (2049223 / 100000) (1024613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793790720 :
    ThetaLowerSegment 793790720 793856256 (79375563429473 / 100000) (15876432801149 / 20000) := by
  exact
    packedTile32768 793790720 793856256 13 3221 28174 30 _ _ (128077 / 6250) (409847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793856256 :
    ThetaLowerSegment 793856256 793921792 (15876432801149 / 20000) (15877765216997 / 20000) := by
  exact
    packedTile32768 793856256 793921792 13 3251 28175 30 _ _ (51231 / 2500) (2049243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793921792 :
    ThetaLowerSegment 793921792 793987328 (15877765216997 / 20000) (79395295560921 / 100000) := by
  exact
    packedTile32768 793921792 793987328 13 3157 28176 30 _ _ (64039 / 3125) (2049251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell793987328 :
    ThetaLowerSegment 793987328 794052864 (79395295560921 / 100000) (79401844983097 / 100000) := by
  exact
    packedTile32768 793987328 794052864 13 3196 28177 30 _ _ (256157 / 12500) (2049259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794052864 :
    ThetaLowerSegment 794052864 794118400 (79401844983097 / 100000) (79408406729627 / 100000) := by
  exact
    packedTile32768 794052864 794118400 13 3202 28178 30 _ _ (409853 / 20000) (512317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794118400 :
    ThetaLowerSegment 794118400 794183936 (79408406729627 / 100000) (9926863634107 / 12500) := by
  exact
    packedTile32768 794118400 794183936 13 3173 28180 30 _ _ (2049273 / 100000) (512319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794183936 :
    ThetaLowerSegment 794183936 794249472 (9926863634107 / 12500) (79421477018461 / 100000) := by
  exact
    packedTile32768 794183936 794249472 13 3205 28181 30 _ _ (2049281 / 100000) (512321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794249472 :
    ThetaLowerSegment 794249472 794315008 (79421477018461 / 100000) (39714026593431 / 50000) := by
  exact
    packedTile32768 794249472 794315008 13 3209 28182 30 _ _ (2049289 / 100000) (512323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794315008 :
    ThetaLowerSegment 794315008 794380544 (39714026593431 / 50000) (1985866349393 / 2500) := by
  exact
    packedTile32768 794315008 794380544 13 3221 28183 30 _ _ (1024649 / 50000) (2049301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794380544 :
    ThetaLowerSegment 794380544 794446080 (1985866349393 / 2500) (7944120150839 / 10000) := by
  exact
    packedTile32768 794380544 794446080 13 3195 28184 30 _ _ (1024653 / 50000) (2049309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794446080 :
    ThetaLowerSegment 794446080 794511616 (7944120150839 / 10000) (4965481498857 / 6250) := by
  exact
    packedTile32768 794446080 794511616 13 3173 28185 30 _ _ (1024657 / 50000) (2049317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794511616 :
    ThetaLowerSegment 794511616 794577152 (4965481498857 / 6250) (39727092993599 / 50000) := by
  exact
    packedTile32768 794511616 794577152 13 3163 28187 30 _ _ (1024661 / 50000) (81973 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794577152 :
    ThetaLowerSegment 794577152 794642688 (39727092993599 / 50000) (2483147604784 / 3125) := by
  exact
    packedTile32768 794577152 794642688 13 3190 28188 30 _ _ (2049331 / 100000) (1024667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794642688 :
    ThetaLowerSegment 794642688 794708224 (2483147604784 / 3125) (15893457477181 / 20000) := by
  exact
    packedTile32768 794642688 794708224 13 3203 28189 30 _ _ (2049339 / 100000) (1024671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794708224 :
    ThetaLowerSegment 794708224 794773760 (15893457477181 / 20000) (79473734631567 / 100000) := by
  exact
    packedTile32768 794708224 794773760 13 3146 28190 30 _ _ (2049347 / 100000) (40987 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794773760 :
    ThetaLowerSegment 794773760 794839296 (79473734631567 / 100000) (19870039839873 / 25000) := by
  exact
    packedTile32768 794773760 794839296 13 3135 28191 30 _ _ (409871 / 20000) (1024679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794839296 :
    ThetaLowerSegment 794839296 794904832 (19870039839873 / 25000) (1987163680677 / 2500) := by
  exact
    packedTile32768 794839296 794904832 13 3117 28192 30 _ _ (512341 / 25000) (2049367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794904832 :
    ThetaLowerSegment 794904832 794970368 (1987163680677 / 2500) (1987328655123 / 2500) := by
  exact
    packedTile32768 794904832 794970368 13 3220 28194 30 _ _ (512343 / 25000) (3279 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell794970368 :
    ThetaLowerSegment 794970368 795035904 (1987328655123 / 2500) (397498889993 / 500) := by
  exact
    packedTile32768 794970368 795035904 13 3236 28195 30 _ _ (102469 / 5000) (2049383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795035904 :
    ThetaLowerSegment 795035904 795101440 (397498889993 / 500) (19876613213829 / 25000) := by
  exact
    packedTile32768 795035904 795101440 13 3257 28196 30 _ _ (512347 / 25000) (2049391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795101440 :
    ThetaLowerSegment 795101440 795166976 (19876613213829 / 25000) (3180520191101 / 4000) := by
  exact
    packedTile32768 795101440 795166976 13 3197 28197 30 _ _ (2049397 / 100000) (10247 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795166976 :
    ThetaLowerSegment 795166976 795232512 (3180520191101 / 4000) (99399389548 / 125) := by
  exact
    packedTile32768 795166976 795232512 13 3175 28198 30 _ _ (409881 / 20000) (64044 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795232512 :
    ThetaLowerSegment 795232512 795298048 (99399389548 / 125) (39763036929413 / 50000) := by
  exact
    packedTile32768 795232512 795298048 13 3202 28199 30 _ _ (2049413 / 100000) (256177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795298048 :
    ThetaLowerSegment 795298048 795363584 (39763036929413 / 50000) (79532658648499 / 100000) := by
  exact
    packedTile32768 795298048 795363584 13 3213 28201 30 _ _ (2049421 / 100000) (128089 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795363584 :
    ThetaLowerSegment 795363584 795429120 (79532658648499 / 100000) (1590785115209 / 2000) := by
  exact
    packedTile32768 795363584 795429120 13 3219 28202 30 _ _ (2049429 / 100000) (256179 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795429120 :
    ThetaLowerSegment 795429120 795494656 (1590785115209 / 2000) (39772915178777 / 50000) := by
  exact
    packedTile32768 795429120 795494656 13 3208 28203 30 _ _ (1024719 / 50000) (2049441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795494656 :
    ThetaLowerSegment 795494656 795560192 (39772915178777 / 50000) (39776206589053 / 50000) := by
  exact
    packedTile32768 795494656 795560192 13 3212 28204 30 _ _ (1024723 / 50000) (2049449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795560192 :
    ThetaLowerSegment 795560192 795625728 (39776206589053 / 50000) (39779487764907 / 50000) := by
  exact
    packedTile32768 795560192 795625728 13 3202 28205 30 _ _ (1024727 / 50000) (2049457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795625728 :
    ThetaLowerSegment 795625728 795691264 (39779487764907 / 50000) (3978269824713 / 5000) := by
  exact
    packedTile32768 795625728 795691264 13 3133 28206 30 _ _ (1024731 / 50000) (409893 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795691264 :
    ThetaLowerSegment 795691264 795756800 (3978269824713 / 5000) (79571977345641 / 100000) := by
  exact
    packedTile32768 795691264 795756800 13 3211 28208 30 _ _ (2049471 / 100000) (1024737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795756800 :
    ThetaLowerSegment 795756800 795822336 (79571977345641 / 100000) (2486830328737 / 3125) := by
  exact
    packedTile32768 795756800 795822336 13 3217 28209 30 _ _ (2049479 / 100000) (1024741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795822336 :
    ThetaLowerSegment 795822336 795887872 (2486830328737 / 3125) (15917035203237 / 20000) := by
  exact
    packedTile32768 795822336 795887872 13 3223 28210 30 _ _ (2049487 / 100000) (204949 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795887872 :
    ThetaLowerSegment 795887872 795953408 (15917035203237 / 20000) (15918328844481 / 20000) := by
  exact
    packedTile32768 795887872 795953408 13 3156 28211 30 _ _ (409899 / 20000) (1024749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell795953408 :
    ThetaLowerSegment 795953408 796018944 (15918328844481 / 20000) (79598200585701 / 100000) := by
  exact
    packedTile32768 795953408 796018944 13 3199 28212 30 _ _ (64047 / 3125) (2049507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796018944 :
    ThetaLowerSegment 796018944 796084480 (79598200585701 / 100000) (79604746727029 / 100000) := by
  exact
    packedTile32768 796018944 796084480 13 3194 28213 30 _ _ (256189 / 12500) (409903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796084480 :
    ThetaLowerSegment 796084480 796150016 (79604746727029 / 100000) (79611374874709 / 100000) := by
  exact
    packedTile32768 796084480 796150016 13 3234 28214 30 _ _ (25619 / 1250) (2049523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796150016 :
    ThetaLowerSegment 796150016 796215552 (79611374874709 / 100000) (79617800144989 / 100000) := by
  exact
    packedTile32768 796150016 796215552 13 3135 28216 30 _ _ (256191 / 12500) (2049531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796215552 :
    ThetaLowerSegment 796215552 796281088 (79617800144989 / 100000) (3981216191063 / 5000) := by
  exact
    packedTile32768 796215552 796281088 13 3183 28217 30 _ _ (2049537 / 100000) (102477 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796281088 :
    ThetaLowerSegment 796281088 796346624 (3981216191063 / 5000) (1990771034359 / 2500) := by
  exact
    packedTile32768 796281088 796346624 13 3180 28218 30 _ _ (409909 / 20000) (512387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796346624 :
    ThetaLowerSegment 796346624 796412160 (1990771034359 / 2500) (79637520867587 / 100000) := by
  exact
    packedTile32768 796346624 796412160 13 3259 28219 30 _ _ (2049553 / 100000) (512389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796412160 :
    ThetaLowerSegment 796412160 796477696 (79637520867587 / 100000) (2488877803456 / 3125) := by
  exact
    packedTile32768 796412160 796477696 13 3205 28220 30 _ _ (2049561 / 100000) (512391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796477696 :
    ThetaLowerSegment 796477696 796543232 (2488877803456 / 3125) (79650629885271 / 100000) := by
  exact
    packedTile32768 796477696 796543232 13 3191 28221 30 _ _ (2049569 / 100000) (512393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796543232 :
    ThetaLowerSegment 796543232 796608768 (79650629885271 / 100000) (79657124997953 / 100000) := by
  exact
    packedTile32768 796543232 796608768 13 3169 28223 30 _ _ (1024789 / 50000) (2049581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796608768 :
    ThetaLowerSegment 796608768 796674304 (79657124997953 / 100000) (79663681623567 / 100000) := by
  exact
    packedTile32768 796608768 796674304 13 3199 28224 30 _ _ (1024793 / 50000) (2049589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796674304 :
    ThetaLowerSegment 796674304 796739840 (79663681623567 / 100000) (79670318208939 / 100000) := by
  exact
    packedTile32768 796674304 796739840 13 3238 28225 30 _ _ (1024797 / 50000) (2049597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796739840 :
    ThetaLowerSegment 796739840 796805376 (79670318208939 / 100000) (79676919976981 / 100000) := by
  exact
    packedTile32768 796739840 796805376 13 3221 28226 30 _ _ (1024801 / 50000) (409921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796805376 :
    ThetaLowerSegment 796805376 796870912 (79676919976981 / 100000) (79683495129069 / 100000) := by
  exact
    packedTile32768 796805376 796870912 13 3208 28227 30 _ _ (2049611 / 100000) (1024807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796870912 :
    ThetaLowerSegment 796870912 796936448 (79683495129069 / 100000) (79690111299201 / 100000) := by
  exact
    packedTile32768 796870912 796936448 13 3228 28228 30 _ _ (2049619 / 100000) (1024811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell796936448 :
    ThetaLowerSegment 796936448 797001984 (79690111299201 / 100000) (39848313531717 / 50000) := by
  exact
    packedTile32768 796936448 797001984 13 3179 28230 30 _ _ (2049627 / 100000) (204963 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797001984 :
    ThetaLowerSegment 797001984 797067520 (39848313531717 / 50000) (39851642138957 / 50000) := by
  exact
    packedTile32768 797001984 797067520 13 3248 28231 30 _ _ (409927 / 20000) (1024819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797067520 :
    ThetaLowerSegment 797067520 797133056 (39851642138957 / 50000) (15941971496603 / 20000) := by
  exact
    packedTile32768 797067520 797133056 13 3207 28232 30 _ _ (2049643 / 100000) (1024823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797133056 :
    ThetaLowerSegment 797133056 797198592 (15941971496603 / 20000) (79716500405147 / 100000) := by
  exact
    packedTile32768 797133056 797198592 13 3241 28233 30 _ _ (512413 / 25000) (409931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797198592 :
    ThetaLowerSegment 797198592 797264128 (79716500405147 / 100000) (79723040870207 / 100000) := by
  exact
    packedTile32768 797198592 797264128 13 3191 28234 30 _ _ (102483 / 5000) (2049663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797264128 :
    ThetaLowerSegment 797264128 797329664 (79723040870207 / 100000) (79729667446851 / 100000) := by
  exact
    packedTile32768 797264128 797329664 13 3233 28235 30 _ _ (512417 / 25000) (2049671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797329664 :
    ThetaLowerSegment 797329664 797395200 (79729667446851 / 100000) (15947248971427 / 20000) := by
  exact
    packedTile32768 797329664 797395200 13 3209 28237 30 _ _ (512419 / 25000) (2049679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797395200 :
    ThetaLowerSegment 797395200 797460736 (15947248971427 / 20000) (15948561589701 / 20000) := by
  exact
    packedTile32768 797395200 797460736 13 3202 28238 30 _ _ (409937 / 20000) (256211 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797460736 :
    ThetaLowerSegment 797460736 797526272 (15948561589701 / 20000) (39874680408513 / 50000) := by
  exact
    packedTile32768 797460736 797526272 13 3197 28239 30 _ _ (2049693 / 100000) (64053 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797526272 :
    ThetaLowerSegment 797526272 797591808 (39874680408513 / 50000) (39877927134897 / 50000) := by
  exact
    packedTile32768 797526272 797591808 13 3168 28240 30 _ _ (2049701 / 100000) (256213 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797591808 :
    ThetaLowerSegment 797591808 797657344 (39877927134897 / 50000) (4985155701721 / 6250) := by
  exact
    packedTile32768 797591808 797657344 13 3238 28241 30 _ _ (2049709 / 100000) (128107 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797657344 :
    ThetaLowerSegment 797657344 797722880 (4985155701721 / 6250) (7976905442137 / 10000) := by
  exact
    packedTile32768 797657344 797722880 13 3202 28242 30 _ _ (2049717 / 100000) (51243 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797722880 :
    ThetaLowerSegment 797722880 797788416 (7976905442137 / 10000) (7977563404183 / 10000) := by
  exact
    packedTile32768 797722880 797788416 13 3210 28243 30 _ _ (1024863 / 50000) (2049729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797788416 :
    ThetaLowerSegment 797788416 797853952 (7977563404183 / 10000) (2493195522887 / 3125) := by
  exact
    packedTile32768 797788416 797853952 13 3231 28245 30 _ _ (1024867 / 50000) (2049737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797853952 :
    ThetaLowerSegment 797853952 797919488 (2493195522887 / 3125) (39894415127489 / 50000) := by
  exact
    packedTile32768 797853952 797919488 13 3207 28246 30 _ _ (1024871 / 50000) (409949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797919488 :
    ThetaLowerSegment 797919488 797985024 (39894415127489 / 50000) (39897680379239 / 50000) := by
  exact
    packedTile32768 797919488 797985024 13 3186 28247 30 _ _ (8199 / 400) (2049753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell797985024 :
    ThetaLowerSegment 797985024 798050560 (39897680379239 / 50000) (15960385227311 / 20000) := by
  exact
    packedTile32768 797985024 798050560 13 3203 28248 30 _ _ (2049759 / 100000) (1024881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798050560 :
    ThetaLowerSegment 798050560 798116096 (15960385227311 / 20000) (638468047109 / 800) := by
  exact
    packedTile32768 798050560 798116096 13 3210 28249 30 _ _ (2049767 / 100000) (204977 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798116096 :
    ThetaLowerSegment 798116096 798181632 (638468047109 / 800) (199537422073 / 250) := by
  exact
    packedTile32768 798116096 798181632 13 3153 28250 30 _ _ (81991 / 4000) (1024889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798181632 :
    ThetaLowerSegment 798181632 798247168 (199537422073 / 250) (79821677768959 / 100000) := by
  exact
    packedTile32768 798181632 798247168 13 3273 28252 30 _ _ (2049783 / 100000) (1024893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798247168 :
    ThetaLowerSegment 798247168 798312704 (79821677768959 / 100000) (19957097708621 / 25000) := by
  exact
    packedTile32768 798247168 798312704 13 3275 28253 30 _ _ (2049791 / 100000) (1024897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798312704 :
    ThetaLowerSegment 798312704 798378240 (19957097708621 / 25000) (19958758559071 / 25000) := by
  exact
    packedTile32768 798312704 798378240 13 3241 28254 30 _ _ (10249 / 500) (2049803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798378240 :
    ThetaLowerSegment 798378240 798443776 (19958758559071 / 25000) (19960384569267 / 25000) := by
  exact
    packedTile32768 798378240 798443776 13 3173 28255 30 _ _ (128113 / 6250) (2049811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798443776 :
    ThetaLowerSegment 798443776 798509312 (19960384569267 / 25000) (19962036208509 / 25000) := by
  exact
    packedTile32768 798443776 798509312 13 3223 28256 30 _ _ (256227 / 12500) (2049819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798509312 :
    ThetaLowerSegment 798509312 798574848 (19962036208509 / 25000) (19963692466301 / 25000) := by
  exact
    packedTile32768 798509312 798574848 13 3232 28257 30 _ _ (64057 / 3125) (2049827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798574848 :
    ThetaLowerSegment 798574848 798640384 (19963692466301 / 25000) (19965329769611 / 25000) := by
  exact
    packedTile32768 798574848 798640384 13 3195 28259 30 _ _ (256229 / 12500) (409967 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798640384 :
    ThetaLowerSegment 798640384 798705920 (19965329769611 / 25000) (79867847822029 / 100000) := by
  exact
    packedTile32768 798640384 798705920 13 3185 28260 30 _ _ (2049841 / 100000) (512461 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798705920 :
    ThetaLowerSegment 798705920 798771456 (79867847822029 / 100000) (79874534429467 / 100000) := by
  exact
    packedTile32768 798705920 798771456 13 3262 28261 30 _ _ (2049849 / 100000) (512463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798771456 :
    ThetaLowerSegment 798771456 798836992 (79874534429467 / 100000) (4992562864251 / 6250) := by
  exact
    packedTile32768 798771456 798836992 13 3157 28262 30 _ _ (2049857 / 100000) (102493 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798836992 :
    ThetaLowerSegment 798836992 798902528 (4992562864251 / 6250) (39943739650843 / 50000) := by
  exact
    packedTile32768 798836992 798902528 13 3158 28263 30 _ _ (409973 / 20000) (512467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798902528 :
    ThetaLowerSegment 798902528 798968064 (39943739650843 / 50000) (1997347795079 / 2500) := by
  exact
    packedTile32768 798902528 798968064 13 3138 28264 30 _ _ (2049873 / 100000) (512469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell798968064 :
    ThetaLowerSegment 798968064 799033600 (1997347795079 / 2500) (9987544579021 / 12500) := by
  exact
    packedTile32768 798968064 799033600 13 3144 28266 30 _ _ (1024941 / 50000) (409977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799033600 :
    ThetaLowerSegment 799033600 799099136 (9987544579021 / 12500) (39953461214919 / 50000) := by
  exact
    packedTile32768 799033600 799099136 13 3203 28267 30 _ _ (204989 / 10000) (2049893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799099136 :
    ThetaLowerSegment 799099136 799164672 (39953461214919 / 50000) (19978372063283 / 25000) := by
  exact
    packedTile32768 799099136 799164672 13 3203 28268 30 _ _ (1024949 / 50000) (2049901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799164672 :
    ThetaLowerSegment 799164672 799230208 (19978372063283 / 25000) (39960002452153 / 50000) := by
  exact
    packedTile32768 799164672 799230208 13 3179 28269 30 _ _ (1024953 / 50000) (2049909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799230208 :
    ThetaLowerSegment 799230208 799295744 (39960002452153 / 50000) (39963245416101 / 50000) := by
  exact
    packedTile32768 799230208 799295744 13 3164 28270 30 _ _ (1024957 / 50000) (2049917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799295744 :
    ThetaLowerSegment 799295744 799361280 (39963245416101 / 50000) (39966488394287 / 50000) := by
  exact
    packedTile32768 799295744 799361280 13 3164 28271 30 _ _ (2049923 / 100000) (1024963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799361280 :
    ThetaLowerSegment 799361280 799426816 (39966488394287 / 50000) (1598786467499 / 2000) := by
  exact
    packedTile32768 799361280 799426816 13 3096 28272 30 _ _ (2049931 / 100000) (1024967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799426816 :
    ThetaLowerSegment 799426816 799492352 (1598786467499 / 2000) (19986451320517 / 25000) := by
  exact
    packedTile32768 799426816 799492352 13 3162 28274 30 _ _ (2049939 / 100000) (1024971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799492352 :
    ThetaLowerSegment 799492352 799557888 (19986451320517 / 25000) (15990469332589 / 20000) := by
  exact
    packedTile32768 799492352 799557888 13 3191 28275 30 _ _ (2049947 / 100000) (40999 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799557888 :
    ThetaLowerSegment 799557888 799623424 (15990469332589 / 20000) (15991766544113 / 20000) := by
  exact
    packedTile32768 799557888 799623424 13 3164 28276 30 _ _ (409991 / 20000) (1024979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799623424 :
    ThetaLowerSegment 799623424 799688960 (15991766544113 / 20000) (79965419254897 / 100000) := by
  exact
    packedTile32768 799623424 799688960 13 3213 28277 30 _ _ (512491 / 25000) (2049967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799688960 :
    ThetaLowerSegment 799688960 799754496 (79965419254897 / 100000) (79971960715549 / 100000) := by
  exact
    packedTile32768 799688960 799754496 13 3191 28278 30 _ _ (512493 / 25000) (81999 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799754496 :
    ThetaLowerSegment 799754496 799820032 (79971960715549 / 100000) (79978530901449 / 100000) := by
  exact
    packedTile32768 799754496 799820032 13 3205 28279 30 _ _ (102499 / 5000) (2049983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799820032 :
    ThetaLowerSegment 799820032 799885568 (79978530901449 / 100000) (79985070363169 / 100000) := by
  exact
    packedTile32768 799820032 799885568 13 3190 28281 30 _ _ (512497 / 25000) (2049991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799885568 :
    ThetaLowerSegment 799885568 799951104 (79985070363169 / 100000) (79991536050553 / 100000) := by
  exact
    packedTile32768 799885568 799951104 13 3154 28282 30 _ _ (512499 / 25000) (2049999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell799951104 :
    ThetaLowerSegment 799951104 800016640 (79991536050553 / 100000) (79998137066653 / 100000) := by
  exact
    packedTile32768 799951104 800016640 13 3220 28283 30 _ _ (410001 / 20000) (256251 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800016640 :
    ThetaLowerSegment 800016640 800082176 (79998137066653 / 100000) (16000932861609 / 20000) := by
  exact
    packedTile32768 800016640 800082176 13 3184 28284 30 _ _ (2050013 / 100000) (64063 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800082176 :
    ThetaLowerSegment 800082176 800147712 (16000932861609 / 20000) (20002815831411 / 25000) := by
  exact
    packedTile32768 800082176 800147712 13 3219 28285 30 _ _ (2050021 / 100000) (256253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800147712 :
    ThetaLowerSegment 800147712 800213248 (20002815831411 / 25000) (16003592974089 / 20000) := by
  exact
    packedTile32768 800147712 800213248 13 3269 28286 30 _ _ (2050029 / 100000) (128127 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800213248 :
    ThetaLowerSegment 800213248 800278784 (16003592974089 / 20000) (1600489064751 / 2000) := by
  exact
    packedTile32768 800213248 800278784 13 3165 28288 30 _ _ (2050037 / 100000) (51251 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800278784 :
    ThetaLowerSegment 800278784 800344320 (1600489064751 / 2000) (20007741558423 / 25000) := by
  exact
    packedTile32768 800278784 800344320 13 3177 28289 30 _ _ (1025023 / 50000) (2050049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800344320 :
    ThetaLowerSegment 800344320 800409856 (20007741558423 / 25000) (40018782678759 / 50000) := by
  exact
    packedTile32768 800344320 800409856 13 3219 28290 30 _ _ (1025027 / 50000) (2050057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800409856 :
    ThetaLowerSegment 800409856 800475392 (40018782678759 / 50000) (40022081228517 / 50000) := by
  exact
    packedTile32768 800409856 800475392 13 3218 28291 30 _ _ (1025031 / 50000) (410013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800475392 :
    ThetaLowerSegment 800475392 800540928 (40022081228517 / 50000) (10006323165793 / 12500) := by
  exact
    packedTile32768 800475392 800540928 13 3133 28292 30 _ _ (205007 / 10000) (2050073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800540928 :
    ThetaLowerSegment 800540928 800606464 (10006323165793 / 12500) (40028563562621 / 50000) := by
  exact
    packedTile32768 800540928 800606464 13 3191 28293 30 _ _ (1025039 / 50000) (2050081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800606464 :
    ThetaLowerSegment 800606464 800672000 (40028563562621 / 50000) (80063595149727 / 100000) := by
  exact
    packedTile32768 800606464 800672000 13 3155 28294 30 _ _ (2050087 / 100000) (205009 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800672000 :
    ThetaLowerSegment 800672000 800737536 (80063595149727 / 100000) (40035168956091 / 50000) := by
  exact
    packedTile32768 800672000 800737536 13 3289 28296 30 _ _ (410019 / 20000) (1025049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800737536 :
    ThetaLowerSegment 800737536 800803072 (40035168956091 / 50000) (2001920713457 / 2500) := by
  exact
    packedTile32768 800737536 800803072 13 3166 28297 30 _ _ (2050103 / 100000) (1025053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800803072 :
    ThetaLowerSegment 800803072 800868608 (2001920713457 / 2500) (80083436046033 / 100000) := by
  exact
    packedTile32768 800803072 800868608 13 3223 28298 30 _ _ (2050111 / 100000) (1025057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800868608 :
    ThetaLowerSegment 800868608 800934144 (80083436046033 / 100000) (8009000257719 / 10000) := by
  exact
    packedTile32768 800868608 800934144 13 3203 28299 30 _ _ (2050119 / 100000) (1025061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800934144 :
    ThetaLowerSegment 800934144 800999680 (8009000257719 / 10000) (20024133570453 / 25000) := by
  exact
    packedTile32768 800934144 800999680 13 3186 28300 30 _ _ (2050127 / 100000) (205013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell800999680 :
    ThetaLowerSegment 800999680 801065216 (20024133570453 / 25000) (4005153505769 / 5000) := by
  exact
    packedTile32768 800999680 801065216 13 3188 28301 30 _ _ (256267 / 12500) (2050139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801065216 :
    ThetaLowerSegment 801065216 801130752 (4005153505769 / 5000) (20027381504709 / 25000) := by
  exact
    packedTile32768 801065216 801130752 13 3149 28303 30 _ _ (64067 / 3125) (2050147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801130752 :
    ThetaLowerSegment 801130752 801196288 (20027381504709 / 25000) (20029060579197 / 25000) := by
  exact
    packedTile32768 801130752 801196288 13 3276 28304 30 _ _ (256269 / 12500) (410031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801196288 :
    ThetaLowerSegment 801196288 801261824 (20029060579197 / 25000) (20030742735477 / 25000) := by
  exact
    packedTile32768 801196288 801261824 13 3282 28305 30 _ _ (25627 / 1250) (2050163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801261824 :
    ThetaLowerSegment 801261824 801327360 (20030742735477 / 25000) (20032403884099 / 25000) := by
  exact
    packedTile32768 801261824 801327360 13 3241 28306 30 _ _ (256271 / 12500) (2050171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801327360 :
    ThetaLowerSegment 801327360 801392896 (20032403884099 / 25000) (80136096145893 / 100000) := by
  exact
    packedTile32768 801327360 801392896 13 3161 28307 30 _ _ (2050177 / 100000) (102509 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801392896 :
    ThetaLowerSegment 801392896 801458432 (80136096145893 / 100000) (80142611633823 / 100000) := by
  exact
    packedTile32768 801392896 801458432 13 3178 28308 30 _ _ (410037 / 20000) (512547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801458432 :
    ThetaLowerSegment 801458432 801523968 (80142611633823 / 100000) (10018665239439 / 12500) := by
  exact
    packedTile32768 801458432 801523968 13 3273 28310 30 _ _ (2050193 / 100000) (512549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801523968 :
    ThetaLowerSegment 801523968 801589504 (10018665239439 / 12500) (80155831303687 / 100000) := by
  exact
    packedTile32768 801523968 801589504 13 3175 28311 30 _ _ (2050201 / 100000) (512551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801589504 :
    ThetaLowerSegment 801589504 801655040 (80155831303687 / 100000) (80162400173323 / 100000) := by
  exact
    packedTile32768 801589504 801655040 13 3204 28312 30 _ _ (2050209 / 100000) (512553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801655040 :
    ThetaLowerSegment 801655040 801720576 (80162400173323 / 100000) (80168792749929 / 100000) := by
  exact
    packedTile32768 801655040 801720576 13 3118 28313 30 _ _ (2050217 / 100000) (102511 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801720576 :
    ThetaLowerSegment 801720576 801786112 (80168792749929 / 100000) (80175384226519 / 100000) := by
  exact
    packedTile32768 801720576 801786112 13 3215 28314 30 _ _ (1025113 / 50000) (2050229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801786112 :
    ThetaLowerSegment 801786112 801851648 (80175384226519 / 100000) (16036388585017 / 20000) := by
  exact
    packedTile32768 801786112 801851648 13 3199 28315 30 _ _ (1025117 / 50000) (2050237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801851648 :
    ThetaLowerSegment 801851648 801917184 (16036388585017 / 20000) (80188438091741 / 100000) := by
  exact
    packedTile32768 801851648 801917184 13 3168 28316 30 _ _ (1025121 / 50000) (410049 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801917184 :
    ThetaLowerSegment 801917184 801982720 (80188438091741 / 100000) (80194972238491 / 100000) := by
  exact
    packedTile32768 801917184 801982720 13 3187 28318 30 _ _ (8201 / 400) (2050253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell801982720 :
    ThetaLowerSegment 801982720 802048256 (80194972238491 / 100000) (80201512561511 / 100000) := by
  exact
    packedTile32768 801982720 802048256 13 3190 28319 30 _ _ (1025129 / 50000) (2050261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802048256 :
    ThetaLowerSegment 802048256 802113792 (80201512561511 / 100000) (80208098015903 / 100000) := by
  exact
    packedTile32768 802048256 802113792 13 3212 28320 30 _ _ (1025133 / 50000) (2050269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802113792 :
    ThetaLowerSegment 802113792 802179328 (80208098015903 / 100000) (80214646594253 / 100000) := by
  exact
    packedTile32768 802113792 802179328 13 3194 28321 30 _ _ (82011 / 4000) (1025139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802179328 :
    ThetaLowerSegment 802179328 802244864 (80214646594253 / 100000) (1604426569331 / 2000) := by
  exact
    packedTile32768 802179328 802244864 13 3259 28322 30 _ _ (2050283 / 100000) (1025143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802244864 :
    ThetaLowerSegment 802244864 802310400 (1604426569331 / 2000) (40113874988981 / 50000) := by
  exact
    packedTile32768 802244864 802310400 13 3132 28323 30 _ _ (2050291 / 100000) (1025147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802310400 :
    ThetaLowerSegment 802310400 802375936 (40113874988981 / 50000) (80234312985061 / 100000) := by
  exact
    packedTile32768 802310400 802375936 13 3201 28325 30 _ _ (2050299 / 100000) (1025151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802375936 :
    ThetaLowerSegment 802375936 802441472 (80234312985061 / 100000) (40120399053051 / 50000) := by
  exact
    packedTile32768 802375936 802441472 13 3163 28326 30 _ _ (2050307 / 100000) (205031 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802441472 :
    ThetaLowerSegment 802441472 802507008 (40120399053051 / 50000) (80247303755597 / 100000) := by
  exact
    packedTile32768 802441472 802507008 13 3173 28327 30 _ _ (410063 / 20000) (1025159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802507008 :
    ThetaLowerSegment 802507008 802572544 (80247303755597 / 100000) (80253754074901 / 100000) := by
  exact
    packedTile32768 802507008 802572544 13 3146 28328 30 _ _ (512581 / 25000) (2050327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802572544 :
    ThetaLowerSegment 802572544 802638080 (80253754074901 / 100000) (80260345892281 / 100000) := by
  exact
    packedTile32768 802572544 802638080 13 3215 28329 30 _ _ (512583 / 25000) (410067 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802638080 :
    ThetaLowerSegment 802638080 802703616 (80260345892281 / 100000) (80266880325861 / 100000) := by
  exact
    packedTile32768 802638080 802703616 13 3187 28330 30 _ _ (102517 / 5000) (2050343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802703616 :
    ThetaLowerSegment 802703616 802769152 (80266880325861 / 100000) (80273377878673 / 100000) := by
  exact
    packedTile32768 802703616 802769152 13 3169 28332 30 _ _ (512587 / 25000) (2050351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802769152 :
    ThetaLowerSegment 802769152 802834688 (80273377878673 / 100000) (80279875456837 / 100000) := by
  exact
    packedTile32768 802769152 802834688 13 3169 28333 30 _ _ (512589 / 25000) (2050359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802834688 :
    ThetaLowerSegment 802834688 802900224 (80279875456837 / 100000) (80286496082193 / 100000) := by
  exact
    packedTile32768 802834688 802900224 13 3229 28334 30 _ _ (512591 / 25000) (2050367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802900224 :
    ThetaLowerSegment 802900224 802965760 (80286496082193 / 100000) (10036622676499 / 12500) := by
  exact
    packedTile32768 802900224 802965760 13 3163 28335 30 _ _ (2050373 / 100000) (256297 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell802965760 :
    ThetaLowerSegment 802965760 803031296 (10036622676499 / 12500) (2509359169439 / 3125) := by
  exact
    packedTile32768 802965760 803031296 13 3176 28336 30 _ _ (2050381 / 100000) (128149 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803031296 :
    ThetaLowerSegment 803031296 803096832 (2509359169439 / 3125) (80305900887673 / 100000) := by
  exact
    packedTile32768 803031296 803096832 13 3125 28337 30 _ _ (2050389 / 100000) (256299 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803096832 :
    ThetaLowerSegment 803096832 803162368 (80305900887673 / 100000) (80312445754897 / 100000) := by
  exact
    packedTile32768 803096832 803162368 13 3192 28338 30 _ _ (2050397 / 100000) (2563 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803162368 :
    ThetaLowerSegment 803162368 803227904 (80312445754897 / 100000) (80319146478437 / 100000) := by
  exact
    packedTile32768 803162368 803227904 13 3268 28340 30 _ _ (410081 / 20000) (256301 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803227904 :
    ThetaLowerSegment 803227904 803293440 (80319146478437 / 100000) (80325744707471 / 100000) := by
  exact
    packedTile32768 803227904 803293440 13 3218 28341 30 _ _ (2050413 / 100000) (128151 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803293440 :
    ThetaLowerSegment 803293440 803358976 (80325744707471 / 100000) (80332244545211 / 100000) := by
  exact
    packedTile32768 803293440 803358976 13 3170 28342 30 _ _ (1025211 / 50000) (82017 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803358976 :
    ThetaLowerSegment 803358976 803424512 (80332244545211 / 100000) (80338797719491 / 100000) := by
  exact
    packedTile32768 803358976 803424512 13 3196 28343 30 _ _ (205043 / 10000) (2050433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803424512 :
    ThetaLowerSegment 803424512 803490048 (80338797719491 / 100000) (3213815841159 / 4000) := by
  exact
    packedTile32768 803424512 803490048 13 3218 28344 30 _ _ (1025219 / 50000) (2050441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803490048 :
    ThetaLowerSegment 803490048 803555584 (3213815841159 / 4000) (80351889791457 / 100000) := by
  exact
    packedTile32768 803490048 803555584 13 3167 28345 30 _ _ (1025223 / 50000) (2050449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803555584 :
    ThetaLowerSegment 803555584 803621120 (80351889791457 / 100000) (80358479950613 / 100000) := by
  exact
    packedTile32768 803555584 803621120 13 3214 28347 30 _ _ (1025227 / 50000) (2050457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803621120 :
    ThetaLowerSegment 803621120 803686656 (80358479950613 / 100000) (80364965561919 / 100000) := by
  exact
    packedTile32768 803621120 803686656 13 3163 28348 30 _ _ (1025231 / 50000) (410093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803686656 :
    ThetaLowerSegment 803686656 803752192 (80364965561919 / 100000) (8037161113843 / 10000) := by
  exact
    packedTile32768 803686656 803752192 13 3241 28349 30 _ _ (2050471 / 100000) (1025237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803752192 :
    ThetaLowerSegment 803752192 803817728 (8037161113843 / 10000) (80378063995843 / 100000) := by
  exact
    packedTile32768 803752192 803817728 13 3147 28350 30 _ _ (2050479 / 100000) (1025241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803817728 :
    ThetaLowerSegment 803817728 803883264 (80378063995843 / 100000) (80384547635737 / 100000) := by
  exact
    packedTile32768 803817728 803883264 13 3162 28351 30 _ _ (2050487 / 100000) (205049 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803883264 :
    ThetaLowerSegment 803883264 803948800 (80384547635737 / 100000) (80391129724687 / 100000) := by
  exact
    packedTile32768 803883264 803948800 13 3210 28352 30 _ _ (410099 / 20000) (1025249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell803948800 :
    ThetaLowerSegment 803948800 804014336 (80391129724687 / 100000) (80397658526239 / 100000) := by
  exact
    packedTile32768 803948800 804014336 13 3184 28353 30 _ _ (2050503 / 100000) (1025253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804014336 :
    ThetaLowerSegment 804014336 804079872 (80397658526239 / 100000) (8040409918129 / 10000) := by
  exact
    packedTile32768 804014336 804079872 13 3141 28355 30 _ _ (2050511 / 100000) (1025257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804079872 :
    ThetaLowerSegment 804079872 804145408 (8040409918129 / 10000) (40205363229349 / 50000) := by
  exact
    packedTile32768 804079872 804145408 13 3232 28356 30 _ _ (2050519 / 100000) (1025261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804145408 :
    ThetaLowerSegment 804145408 804210944 (40205363229349 / 50000) (1608346132061 / 2000) := by
  exact
    packedTile32768 804145408 804210944 13 3209 28357 30 _ _ (64079 / 3125) (2050531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804210944 :
    ThetaLowerSegment 804210944 804276480 (1608346132061 / 2000) (40211984397257 / 50000) := by
  exact
    packedTile32768 804210944 804276480 13 3249 28358 30 _ _ (256317 / 12500) (2050539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804276480 :
    ThetaLowerSegment 804276480 804342016 (40211984397257 / 50000) (40215237585313 / 50000) := by
  exact
    packedTile32768 804276480 804342016 13 3173 28359 30 _ _ (128159 / 6250) (2050547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804342016 :
    ThetaLowerSegment 804342016 804407552 (40215237585313 / 50000) (8043712306021 / 10000) := by
  exact
    packedTile32768 804342016 804407552 13 3242 28360 30 _ _ (256319 / 12500) (410111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804407552 :
    ThetaLowerSegment 804407552 804473088 (8043712306021 / 10000) (8044370740837 / 10000) := by
  exact
    packedTile32768 804407552 804473088 13 3211 28362 30 _ _ (12816 / 625) (2050563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804473088 :
    ThetaLowerSegment 804473088 804538624 (8044370740837 / 10000) (1609004769349 / 2000) := by
  exact
    packedTile32768 804473088 804538624 13 3185 28363 30 _ _ (256321 / 12500) (2050571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804538624 :
    ThetaLowerSegment 804538624 804604160 (1609004769349 / 2000) (40228455520877 / 50000) := by
  exact
    packedTile32768 804538624 804604160 13 3254 28364 30 _ _ (128161 / 6250) (2050579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804604160 :
    ThetaLowerSegment 804604160 804669696 (40228455520877 / 50000) (2514484938332 / 3125) := by
  exact
    packedTile32768 804604160 804669696 13 3222 28365 30 _ _ (410117 / 20000) (512647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804669696 :
    ThetaLowerSegment 804669696 804735232 (2514484938332 / 3125) (20117509728091 / 25000) := by
  exact
    packedTile32768 804669696 804735232 13 3180 28366 30 _ _ (2050593 / 100000) (512649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804735232 :
    ThetaLowerSegment 804735232 804800768 (20117509728091 / 25000) (8047661313917 / 10000) := by
  exact
    packedTile32768 804735232 804800768 13 3206 28367 30 _ _ (2050601 / 100000) (512651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804800768 :
    ThetaLowerSegment 804800768 804866304 (8047661313917 / 10000) (5030204338499 / 6250) := by
  exact
    packedTile32768 804800768 804866304 13 3246 28369 30 _ _ (2050609 / 100000) (512653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804866304 :
    ThetaLowerSegment 804866304 804931840 (5030204338499 / 6250) (80489804732363 / 100000) := by
  exact
    packedTile32768 804866304 804931840 13 3187 28370 30 _ _ (2050617 / 100000) (102531 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804931840 :
    ThetaLowerSegment 804931840 804997376 (80489804732363 / 100000) (80496469263613 / 100000) := by
  exact
    packedTile32768 804931840 804997376 13 3250 28371 30 _ _ (3281 / 160) (512657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell804997376 :
    ThetaLowerSegment 804997376 805062912 (80496469263613 / 100000) (40251533074987 / 50000) := by
  exact
    packedTile32768 804997376 805062912 13 3217 28372 30 _ _ (2050633 / 100000) (512659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805062912 :
    ThetaLowerSegment 805062912 805128448 (40251533074987 / 50000) (40254814102187 / 50000) := by
  exact
    packedTile32768 805062912 805128448 13 3200 28373 30 _ _ (1025321 / 50000) (410129 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805128448 :
    ThetaLowerSegment 805128448 805193984 (40254814102187 / 50000) (10064525067203 / 12500) := by
  exact
    packedTile32768 805128448 805193984 13 3205 28374 30 _ _ (41013 / 2000) (2050653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805193984 :
    ThetaLowerSegment 805193984 805259520 (10064525067203 / 12500) (40261310573911 / 50000) := by
  exact
    packedTile32768 805193984 805259520 13 3131 28375 30 _ _ (1025329 / 50000) (2050661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805259520 :
    ThetaLowerSegment 805259520 805325056 (40261310573911 / 50000) (40264626500833 / 50000) := by
  exact
    packedTile32768 805259520 805325056 13 3234 28377 30 _ _ (1025333 / 50000) (2050669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805325056 :
    ThetaLowerSegment 805325056 805390592 (40264626500833 / 50000) (40267915781929 / 50000) := by
  exact
    packedTile32768 805325056 805390592 13 3208 28378 30 _ _ (1025337 / 50000) (2050677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805390592 :
    ThetaLowerSegment 805390592 805456128 (40267915781929 / 50000) (10067801012629 / 12500) := by
  exact
    packedTile32768 805390592 805456128 13 3207 28379 30 _ _ (1025341 / 50000) (410137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805456128 :
    ThetaLowerSegment 805456128 805521664 (10067801012629 / 12500) (40274457470201 / 50000) := by
  exact
    packedTile32768 805456128 805521664 13 3173 28380 30 _ _ (205069 / 10000) (2050693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805521664 :
    ThetaLowerSegment 805521664 805587200 (40274457470201 / 50000) (2517359302631 / 3125) := by
  exact
    packedTile32768 805521664 805587200 13 3210 28381 30 _ _ (2050699 / 100000) (1025351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805587200 :
    ThetaLowerSegment 805587200 805652736 (2517359302631 / 3125) (80562131721337 / 100000) := by
  exact
    packedTile32768 805587200 805652736 13 3235 28382 30 _ _ (2050707 / 100000) (205071 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805652736 :
    ThetaLowerSegment 805652736 805718272 (80562131721337 / 100000) (40284354182171 / 50000) := by
  exact
    packedTile32768 805652736 805718272 13 3207 28384 30 _ _ (410143 / 20000) (1025359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805718272 :
    ThetaLowerSegment 805718272 805783808 (40284354182171 / 50000) (80575264525773 / 100000) := by
  exact
    packedTile32768 805718272 805783808 13 3197 28385 30 _ _ (2050723 / 100000) (1025363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805783808 :
    ThetaLowerSegment 805783808 805849344 (80575264525773 / 100000) (40290854986653 / 50000) := by
  exact
    packedTile32768 805783808 805849344 13 3143 28386 30 _ _ (2050731 / 100000) (1025367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805849344 :
    ThetaLowerSegment 805849344 805914880 (40290854986653 / 50000) (80588298997713 / 100000) := by
  exact
    packedTile32768 805849344 805914880 13 3213 28387 30 _ _ (2050739 / 100000) (1025371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805914880 :
    ThetaLowerSegment 805914880 805980416 (80588298997713 / 100000) (80594746546281 / 100000) := by
  exact
    packedTile32768 805914880 805980416 13 3144 28388 30 _ _ (2050747 / 100000) (8203 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell805980416 :
    ThetaLowerSegment 805980416 806045952 (80594746546281 / 100000) (80601341777577 / 100000) := by
  exact
    packedTile32768 805980416 806045952 13 3216 28389 30 _ _ (512689 / 25000) (2050759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806045952 :
    ThetaLowerSegment 806045952 806111488 (80601341777577 / 100000) (80608090841901 / 100000) := by
  exact
    packedTile32768 806045952 806111488 13 3291 28390 30 _ _ (512691 / 25000) (2050767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806111488 :
    ThetaLowerSegment 806111488 806177024 (80608090841901 / 100000) (80614641007669 / 100000) := by
  exact
    packedTile32768 806111488 806177024 13 3194 28392 30 _ _ (512693 / 25000) (82031 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806177024 :
    ThetaLowerSegment 806177024 806242560 (80614641007669 / 100000) (80621279382529 / 100000) := by
  exact
    packedTile32768 806177024 806242560 13 3237 28393 30 _ _ (102539 / 5000) (2050783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806242560 :
    ThetaLowerSegment 806242560 806308096 (80621279382529 / 100000) (80627772177337 / 100000) := by
  exact
    packedTile32768 806242560 806308096 13 3166 28394 30 _ _ (512697 / 25000) (2050791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806308096 :
    ThetaLowerSegment 806308096 806373632 (80627772177337 / 100000) (80634406502397 / 100000) := by
  exact
    packedTile32768 806308096 806373632 13 3235 28395 30 _ _ (512699 / 25000) (2050799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806373632 :
    ThetaLowerSegment 806373632 806439168 (80634406502397 / 100000) (80641028548513 / 100000) := by
  exact
    packedTile32768 806373632 806439168 13 3229 28396 30 _ _ (512701 / 25000) (2050807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806439168 :
    ThetaLowerSegment 806439168 806504704 (80641028548513 / 100000) (80647488606313 / 100000) := by
  exact
    packedTile32768 806439168 806504704 13 3150 28397 30 _ _ (512703 / 25000) (410163 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806504704 :
    ThetaLowerSegment 806504704 806570240 (80647488606313 / 100000) (20163532803883 / 25000) := by
  exact
    packedTile32768 806504704 806570240 13 3239 28399 30 _ _ (2050821 / 100000) (256353 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806570240 :
    ThetaLowerSegment 806570240 806635776 (20163532803883 / 25000) (2520646939739 / 3125) := by
  exact
    packedTile32768 806570240 806635776 13 3204 28400 30 _ _ (2050829 / 100000) (128177 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806635776 :
    ThetaLowerSegment 806635776 806701312 (2520646939739 / 3125) (80667258597537 / 100000) := by
  exact
    packedTile32768 806635776 806701312 13 3197 28401 30 _ _ (2050837 / 100000) (51271 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806701312 :
    ThetaLowerSegment 806701312 806766848 (80667258597537 / 100000) (20168430202533 / 25000) := by
  exact
    packedTile32768 806701312 806766848 13 3151 28402 30 _ _ (410169 / 20000) (64089 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806766848 :
    ThetaLowerSegment 806766848 806832384 (20168430202533 / 25000) (80680322505939 / 100000) := by
  exact
    packedTile32768 806766848 806832384 13 3219 28403 30 _ _ (2050853 / 100000) (256357 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806832384 :
    ThetaLowerSegment 806832384 806897920 (80680322505939 / 100000) (40343445706861 / 50000) := by
  exact
    packedTile32768 806832384 806897920 13 3203 28404 30 _ _ (2050861 / 100000) (128179 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806897920 :
    ThetaLowerSegment 806897920 806963456 (40343445706861 / 50000) (40346706588571 / 50000) := by
  exact
    packedTile32768 806897920 806963456 13 3180 28405 30 _ _ (2050869 / 100000) (256359 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell806963456 :
    ThetaLowerSegment 806963456 807028992 (40346706588571 / 50000) (20174992970447 / 25000) := by
  exact
    packedTile32768 806963456 807028992 13 3198 28407 30 _ _ (2050877 / 100000) (12818 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807028992 :
    ThetaLowerSegment 807028992 807094528 (20174992970447 / 25000) (40353309401657 / 50000) := by
  exact
    packedTile32768 807028992 807094528 13 3241 28408 30 _ _ (1025443 / 50000) (2050889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807094528 :
    ThetaLowerSegment 807094528 807160064 (40353309401657 / 50000) (40356521101661 / 50000) := by
  exact
    packedTile32768 807094528 807160064 13 3132 28409 30 _ _ (1025447 / 50000) (2050897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807160064 :
    ThetaLowerSegment 807160064 807225600 (40356521101661 / 50000) (40359884580941 / 50000) := by
  exact
    packedTile32768 807160064 807225600 13 3280 28410 30 _ _ (1025451 / 50000) (410181 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807225600 :
    ThetaLowerSegment 807225600 807291136 (40359884580941 / 50000) (10090785612869 / 12500) := by
  exact
    packedTile32768 807225600 807291136 13 3177 28411 30 _ _ (205091 / 10000) (2050913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807291136 :
    ThetaLowerSegment 807291136 807356672 (10090785612869 / 12500) (40366447505833 / 50000) := by
  exact
    packedTile32768 807291136 807356672 13 3223 28412 30 _ _ (1025459 / 50000) (2050921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807356672 :
    ThetaLowerSegment 807356672 807422208 (40366447505833 / 50000) (8073938414153 / 10000) := by
  exact
    packedTile32768 807356672 807422208 13 3164 28414 30 _ _ (1025463 / 50000) (2050929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807422208 :
    ThetaLowerSegment 807422208 807487744 (8073938414153 / 10000) (8074598814901 / 10000) := by
  exact
    packedTile32768 807422208 807487744 13 3220 28415 30 _ _ (1025467 / 50000) (2050937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807487744 :
    ThetaLowerSegment 807487744 807553280 (8074598814901 / 10000) (5047028423071 / 6250) := by
  exact
    packedTile32768 807487744 807553280 13 3153 28416 30 _ _ (1025471 / 50000) (410189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807553280 :
    ThetaLowerSegment 807553280 807618816 (5047028423071 / 6250) (40379450452493 / 50000) := by
  exact
    packedTile32768 807553280 807618816 13 3143 28417 30 _ _ (41019 / 2000) (2050953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807618816 :
    ThetaLowerSegment 807618816 807684352 (40379450452493 / 50000) (8076537373159 / 10000) := by
  exact
    packedTile32768 807618816 807684352 13 3156 28418 30 _ _ (2050959 / 100000) (1025481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807684352 :
    ThetaLowerSegment 807684352 807749888 (8076537373159 / 10000) (16154373008429 / 20000) := by
  exact
    packedTile32768 807684352 807749888 13 3165 28419 30 _ _ (2050967 / 100000) (205097 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807749888 :
    ThetaLowerSegment 807749888 807815424 (16154373008429 / 20000) (16155688913989 / 20000) := by
  exact
    packedTile32768 807749888 807815424 13 3208 28420 30 _ _ (82039 / 4000) (1025489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807815424 :
    ThetaLowerSegment 807815424 807880960 (16155688913989 / 20000) (2524531555204 / 3125) := by
  exact
    packedTile32768 807815424 807880960 13 3201 28422 30 _ _ (2050983 / 100000) (1025493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807880960 :
    ThetaLowerSegment 807880960 807946496 (2524531555204 / 3125) (20197891183441 / 25000) := by
  exact
    packedTile32768 807880960 807946496 13 3196 28423 30 _ _ (2050991 / 100000) (1025497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell807946496 :
    ThetaLowerSegment 807946496 808012032 (20197891183441 / 25000) (80798244837507 / 100000) := by
  exact
    packedTile32768 807946496 808012032 13 3257 28424 30 _ _ (2050999 / 100000) (1025501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808012032 :
    ThetaLowerSegment 808012032 808077568 (80798244837507 / 100000) (80804791651851 / 100000) := by
  exact
    packedTile32768 808012032 808077568 13 3192 28425 30 _ _ (2051007 / 100000) (205101 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808077568 :
    ThetaLowerSegment 808077568 808143104 (80804791651851 / 100000) (40405604638893 / 50000) := by
  exact
    packedTile32768 808077568 808143104 13 3129 28426 30 _ _ (410203 / 20000) (1025509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808143104 :
    ThetaLowerSegment 808143104 808208640 (40405604638893 / 50000) (20204446214381 / 25000) := by
  exact
    packedTile32768 808143104 808208640 13 3206 28427 30 _ _ (2051023 / 100000) (1025513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808208640 :
    ThetaLowerSegment 808208640 808274176 (20204446214381 / 25000) (20206076272063 / 25000) := by
  exact
    packedTile32768 808208640 808274176 13 3179 28429 30 _ _ (256379 / 12500) (410207 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808274176 :
    ThetaLowerSegment 808274176 808339712 (20206076272063 / 25000) (20207714027503 / 25000) := by
  exact
    packedTile32768 808274176 808339712 13 3194 28430 30 _ _ (12819 / 625) (2051043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808339712 :
    ThetaLowerSegment 808339712 808405248 (20207714027503 / 25000) (20209376914669 / 25000) := by
  exact
    packedTile32768 808339712 808405248 13 3243 28431 30 _ _ (256381 / 12500) (2051051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808405248 :
    ThetaLowerSegment 808405248 808470784 (20209376914669 / 25000) (20210999812729 / 25000) := by
  exact
    packedTile32768 808405248 808470784 13 3165 28432 30 _ _ (128191 / 6250) (2051059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808470784 :
    ThetaLowerSegment 808470784 808536320 (20210999812729 / 25000) (20212614512863 / 25000) := by
  exact
    packedTile32768 808470784 808536320 13 3149 28433 30 _ _ (256383 / 12500) (2051067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808536320 :
    ThetaLowerSegment 808536320 808601856 (20212614512863 / 25000) (20214276906719 / 25000) := by
  exact
    packedTile32768 808536320 808601856 13 3242 28434 30 _ _ (64096 / 3125) (82043 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808601856 :
    ThetaLowerSegment 808601856 808667392 (20214276906719 / 25000) (20215940845369 / 25000) := by
  exact
    packedTile32768 808601856 808667392 13 3245 28435 30 _ _ (51277 / 2500) (2051083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808667392 :
    ThetaLowerSegment 808667392 808732928 (20215940845369 / 25000) (808703227609 / 1000) := by
  exact
    packedTile32768 808667392 808732928 13 3198 28437 30 _ _ (128193 / 6250) (2051091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808732928 :
    ThetaLowerSegment 808732928 808798464 (808703227609 / 1000) (20219186185619 / 25000) := by
  exact
    packedTile32768 808732928 808798464 13 3131 28438 30 _ _ (256387 / 12500) (2051099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808798464 :
    ThetaLowerSegment 808798464 808864000 (20219186185619 / 25000) (80883310329581 / 100000) := by
  exact
    packedTile32768 808798464 808864000 13 3201 28439 30 _ _ (410221 / 20000) (512777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808864000 :
    ThetaLowerSegment 808864000 808929536 (80883310329581 / 100000) (80889968242379 / 100000) := by
  exact
    packedTile32768 808864000 808929536 13 3246 28440 30 _ _ (2051113 / 100000) (512779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808929536 :
    ThetaLowerSegment 808929536 808995072 (80889968242379 / 100000) (80896494909401 / 100000) := by
  exact
    packedTile32768 808929536 808995072 13 3182 28441 30 _ _ (2051121 / 100000) (512781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell808995072 :
    ThetaLowerSegment 808995072 809060608 (80896494909401 / 100000) (80903033908653 / 100000) := by
  exact
    packedTile32768 808995072 809060608 13 3188 28442 30 _ _ (2051129 / 100000) (512783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809060608 :
    ThetaLowerSegment 809060608 809126144 (80903033908653 / 100000) (80909687797081 / 100000) := by
  exact
    packedTile32768 809060608 809126144 13 3244 28443 30 _ _ (2051137 / 100000) (102557 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809126144 :
    ThetaLowerSegment 809126144 809191680 (80909687797081 / 100000) (40458073426343 / 50000) := by
  exact
    packedTile32768 809126144 809191680 13 3149 28445 30 _ _ (410229 / 20000) (512787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809191680 :
    ThetaLowerSegment 809191680 809257216 (40458073426343 / 50000) (80922782332641 / 100000) := by
  exact
    packedTile32768 809191680 809257216 13 3235 28446 30 _ _ (2051153 / 100000) (512789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809257216 :
    ThetaLowerSegment 809257216 809322752 (80922782332641 / 100000) (40464674049501 / 50000) := by
  exact
    packedTile32768 809257216 809322752 13 3201 28447 30 _ _ (2051161 / 100000) (512791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809322752 :
    ThetaLowerSegment 809322752 809339136 (40464674049501 / 50000) (80930995187709 / 100000) := by
  exact
    packedTile32768 809322752 809339136 11 803 28448 30 _ _ (2051169 / 100000) (512793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809339136 :
    ThetaLowerSegment 809339136 809341184 (80930995187709 / 100000) (80931183895441 / 100000) := by
  exact
    packedTile32768 809339136 809341184 8 92 28448 30 _ _ (2051171 / 100000) (1025587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_777341184_809341184 :
    ThetaLowerSegment 777341184 809341184 (77729513866247 / 100000) (80931183895441 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell777341184 cell777406720)
                    (ThetaLowerSegment.join cell777472256 cell777537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell777603328 cell777668864)
                    (ThetaLowerSegment.join cell777734400 cell777799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell777865472 cell777931008)
                    (ThetaLowerSegment.join cell777996544 cell778062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell778127616 cell778193152)
                    (ThetaLowerSegment.join cell778258688 cell778324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell778389760 cell778455296)
                    (ThetaLowerSegment.join cell778520832 cell778586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell778651904 cell778717440)
                    (ThetaLowerSegment.join cell778782976 cell778848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell778914048 cell778979584)
                    (ThetaLowerSegment.join cell779045120 cell779110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell779176192 cell779241728)
                    (ThetaLowerSegment.join cell779307264 cell779372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell779438336 cell779503872)
                    (ThetaLowerSegment.join cell779569408 cell779634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell779700480 cell779766016)
                    (ThetaLowerSegment.join cell779831552 cell779897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell779962624 cell780028160)
                    (ThetaLowerSegment.join cell780093696 cell780159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell780224768 cell780290304)
                    (ThetaLowerSegment.join cell780355840 cell780421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell780486912 cell780552448)
                    (ThetaLowerSegment.join cell780617984 cell780683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell780749056 cell780814592)
                    (ThetaLowerSegment.join cell780880128 cell780945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell781011200 cell781076736)
                    (ThetaLowerSegment.join cell781142272 cell781207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell781273344 cell781338880)
                    (ThetaLowerSegment.join cell781404416 cell781469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell781535488 cell781601024)
                    (ThetaLowerSegment.join cell781666560 cell781732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell781797632 cell781863168)
                    (ThetaLowerSegment.join cell781928704 cell781994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell782059776 cell782125312)
                    (ThetaLowerSegment.join cell782190848 cell782256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell782321920 cell782387456)
                    (ThetaLowerSegment.join cell782452992 cell782518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell782584064 cell782649600)
                    (ThetaLowerSegment.join cell782715136 cell782780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell782846208 cell782911744)
                    (ThetaLowerSegment.join cell782977280 cell783042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell783108352 cell783173888)
                    (ThetaLowerSegment.join cell783239424 cell783304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell783370496 cell783436032)
                    (ThetaLowerSegment.join cell783501568 cell783567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell783632640 cell783698176)
                    (ThetaLowerSegment.join cell783763712 cell783829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell783894784 cell783960320)
                    (ThetaLowerSegment.join cell784025856 cell784091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell784156928 cell784222464)
                    (ThetaLowerSegment.join cell784288000 cell784353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell784419072 cell784484608)
                    (ThetaLowerSegment.join cell784550144 cell784615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell784681216 cell784746752)
                    (ThetaLowerSegment.join cell784812288 cell784877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell784943360 cell785008896)
                    (ThetaLowerSegment.join cell785074432 cell785139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell785205504 cell785271040)
                    (ThetaLowerSegment.join cell785336576 cell785402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell785467648 cell785533184)
                    (ThetaLowerSegment.join cell785598720 cell785664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell785729792 cell785795328)
                    (ThetaLowerSegment.join cell785860864 cell785926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell785991936 cell786057472)
                    (ThetaLowerSegment.join cell786123008 cell786188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell786254080 cell786319616)
                    (ThetaLowerSegment.join cell786385152 cell786450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell786516224 cell786581760)
                    (ThetaLowerSegment.join cell786647296 cell786712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell786778368 cell786843904)
                    (ThetaLowerSegment.join cell786909440 cell786974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell787040512 cell787106048)
                    (ThetaLowerSegment.join cell787171584 cell787237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell787302656 cell787368192)
                    (ThetaLowerSegment.join cell787433728 cell787499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell787564800 cell787630336)
                    (ThetaLowerSegment.join cell787695872 cell787761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell787826944 cell787892480)
                    (ThetaLowerSegment.join cell787958016 cell788023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell788089088 cell788154624)
                    (ThetaLowerSegment.join cell788220160 cell788285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell788351232 cell788416768)
                    (ThetaLowerSegment.join cell788482304 cell788547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell788613376 cell788678912)
                    (ThetaLowerSegment.join cell788744448 cell788809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell788875520 cell788941056)
                    (ThetaLowerSegment.join cell789006592 cell789072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell789137664 cell789203200)
                    (ThetaLowerSegment.join cell789268736 cell789334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell789399808 cell789465344)
                    (ThetaLowerSegment.join cell789530880 cell789596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell789661952 cell789727488)
                    (ThetaLowerSegment.join cell789793024 cell789858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell789924096 cell789989632)
                    (ThetaLowerSegment.join cell790055168 cell790120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell790186240 cell790251776)
                    (ThetaLowerSegment.join cell790317312 cell790382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell790448384 cell790513920)
                    (ThetaLowerSegment.join cell790579456 cell790644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell790710528 cell790776064)
                    (ThetaLowerSegment.join cell790841600 cell790907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell790972672 cell791038208)
                    (ThetaLowerSegment.join cell791103744 cell791169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell791234816 cell791300352)
                    (ThetaLowerSegment.join cell791365888 cell791431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell791496960 cell791562496)
                    (ThetaLowerSegment.join cell791628032 cell791693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell791759104 cell791824640)
                    (ThetaLowerSegment.join cell791890176 cell791955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell792021248 cell792086784)
                    (ThetaLowerSegment.join cell792152320 cell792217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell792283392 cell792348928)
                    (ThetaLowerSegment.join cell792414464 cell792480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell792545536 cell792611072)
                    (ThetaLowerSegment.join cell792676608 cell792742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell792807680 cell792873216)
                    (ThetaLowerSegment.join cell792938752 cell793004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell793069824 cell793135360)
                    (ThetaLowerSegment.join cell793200896 cell793266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell793331968 cell793397504)
                    (ThetaLowerSegment.join cell793463040 cell793528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell793594112 cell793659648)
                    (ThetaLowerSegment.join cell793725184 cell793790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell793856256 cell793921792)
                    (ThetaLowerSegment.join cell793987328 cell794052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell794118400 cell794183936)
                    (ThetaLowerSegment.join cell794249472 cell794315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell794380544 cell794446080)
                    (ThetaLowerSegment.join cell794511616 cell794577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell794642688 cell794708224)
                    (ThetaLowerSegment.join cell794773760 cell794839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell794904832 cell794970368)
                    (ThetaLowerSegment.join cell795035904 cell795101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell795166976 cell795232512)
                    (ThetaLowerSegment.join cell795298048 cell795363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell795429120 cell795494656)
                    (ThetaLowerSegment.join cell795560192 cell795625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell795691264 cell795756800)
                    (ThetaLowerSegment.join cell795822336 cell795887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell795953408 cell796018944)
                    (ThetaLowerSegment.join cell796084480 cell796150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell796215552 cell796281088)
                    (ThetaLowerSegment.join cell796346624 cell796412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell796477696 cell796543232)
                    (ThetaLowerSegment.join cell796608768 cell796674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell796739840 cell796805376)
                    (ThetaLowerSegment.join cell796870912 cell796936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell797001984 cell797067520)
                    (ThetaLowerSegment.join cell797133056 cell797198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell797264128 cell797329664)
                    (ThetaLowerSegment.join cell797395200 cell797460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell797526272 cell797591808)
                    (ThetaLowerSegment.join cell797657344 cell797722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell797788416 cell797853952)
                    (ThetaLowerSegment.join cell797919488 cell797985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell798050560 cell798116096)
                    (ThetaLowerSegment.join cell798181632 cell798247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell798312704 cell798378240)
                    (ThetaLowerSegment.join cell798443776 cell798509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell798574848 cell798640384)
                    (ThetaLowerSegment.join cell798705920 cell798771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell798836992 cell798902528)
                    (ThetaLowerSegment.join cell798968064 cell799033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell799099136 cell799164672)
                    (ThetaLowerSegment.join cell799230208 cell799295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell799361280 cell799426816)
                    (ThetaLowerSegment.join cell799492352 cell799557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell799623424 cell799688960)
                    (ThetaLowerSegment.join cell799754496 cell799820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell799885568 cell799951104)
                    (ThetaLowerSegment.join cell800016640 cell800082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell800147712 cell800213248)
                    (ThetaLowerSegment.join cell800278784 cell800344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell800409856 cell800475392)
                    (ThetaLowerSegment.join cell800540928 cell800606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell800672000 cell800737536)
                    (ThetaLowerSegment.join cell800803072 cell800868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell800934144 cell800999680)
                    (ThetaLowerSegment.join cell801065216 cell801130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell801196288 cell801261824)
                    (ThetaLowerSegment.join cell801327360 cell801392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell801458432 cell801523968)
                    (ThetaLowerSegment.join cell801589504 cell801655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell801720576 cell801786112)
                    (ThetaLowerSegment.join cell801851648 cell801917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell801982720 cell802048256)
                    (ThetaLowerSegment.join cell802113792 cell802179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell802244864 cell802310400)
                    (ThetaLowerSegment.join cell802375936 cell802441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell802507008 cell802572544)
                    (ThetaLowerSegment.join cell802638080 cell802703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell802769152 cell802834688)
                    (ThetaLowerSegment.join cell802900224 cell802965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell803031296 cell803096832)
                    (ThetaLowerSegment.join cell803162368 cell803227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell803293440 cell803358976)
                    (ThetaLowerSegment.join cell803424512 cell803490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell803555584 cell803621120)
                    (ThetaLowerSegment.join cell803686656 cell803752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell803817728 cell803883264)
                    (ThetaLowerSegment.join cell803948800 cell804014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell804079872 cell804145408)
                    (ThetaLowerSegment.join cell804210944 cell804276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell804342016 cell804407552)
                    (ThetaLowerSegment.join cell804473088 cell804538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell804604160 cell804669696)
                    (ThetaLowerSegment.join cell804735232 cell804800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell804866304 cell804931840)
                    (ThetaLowerSegment.join cell804997376 cell805062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell805128448 cell805193984)
                    (ThetaLowerSegment.join cell805259520 cell805325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell805390592 cell805456128)
                    (ThetaLowerSegment.join cell805521664 cell805587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell805652736 cell805718272)
                    (ThetaLowerSegment.join cell805783808 cell805849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell805914880 cell805980416)
                    (ThetaLowerSegment.join cell806045952 cell806111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell806177024 cell806242560)
                    (ThetaLowerSegment.join cell806308096 cell806373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell806439168 cell806504704)
                    (ThetaLowerSegment.join cell806570240 cell806635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell806701312 cell806766848)
                    (ThetaLowerSegment.join cell806832384 cell806897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell806963456 cell807028992)
                    (ThetaLowerSegment.join cell807094528 cell807160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell807225600 cell807291136)
                    (ThetaLowerSegment.join cell807356672 cell807422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell807487744 cell807553280)
                    (ThetaLowerSegment.join cell807618816 cell807684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell807749888 cell807815424)
                    (ThetaLowerSegment.join cell807880960 cell807946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell808012032 cell808077568)
                    (ThetaLowerSegment.join cell808143104 cell808208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell808274176 cell808339712)
                    (ThetaLowerSegment.join cell808405248 cell808470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell808536320 cell808601856)
                    (ThetaLowerSegment.join cell808667392 cell808732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell808798464 cell808864000)
                  (ThetaLowerSegment.join cell808929536 cell808995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell809060608 cell809126144)
                  (ThetaLowerSegment.join cell809191680 cell809257216)))
              (ThetaLowerSegment.join cell809322752 cell809339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
