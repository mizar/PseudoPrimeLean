/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3273341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3241341184 :
    ThetaLowerSegment 3241341184 3241472256 (162062909616841 / 50000)
      (162069416976007 / 50000) := by
  exact
    packedTile65536 3241341184 3241472256 14 5943 56932 32 _ _ (547481 / 25000) (2189927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241472256 :
    ThetaLowerSegment 3241472256 3241603328 (162069416976007 / 50000) (32415202169843 / 10000) := by
  exact
    packedTile65536 3241472256 3241603328 14 6022 56933 32 _ _ (273741 / 12500) (2189931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241603328 :
    ThetaLowerSegment 3241603328 3241734400 (32415202169843 / 10000) (162082430634873 / 50000) := by
  exact
    packedTile65536 3241603328 3241734400 14 5863 56935 32 _ _ (547483 / 25000) (437987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241734400 :
    ThetaLowerSegment 3241734400 3241865472 (162082430634873 / 50000)
      (162088990588161 / 50000) := by
  exact
    packedTile65536 3241734400 3241865472 14 5991 56936 32 _ _ (136871 / 6250) (2189939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241865472 :
    ThetaLowerSegment 3241865472 3241996544 (162088990588161 / 50000)
      (162095559313191 / 50000) := by
  exact
    packedTile65536 3241865472 3241996544 14 5999 56937 32 _ _ (109497 / 5000) (2189943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241996544 :
    ThetaLowerSegment 3241996544 3242127616 (162095559313191 / 50000)
      (162102130240163 / 50000) := by
  exact
    packedTile65536 3241996544 3242127616 14 6001 56938 32 _ _ (273743 / 12500) (2189947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3242127616 :
    ThetaLowerSegment 3242127616 3242258688 (162102130240163 / 50000) (6484347477779 / 2000) := by
  exact
    packedTile65536 3242127616 3242258688 14 5988 56939 32 _ _ (547487 / 25000) (2189951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3242258688 :
    ThetaLowerSegment 3242258688 3242389760 (6484347477779 / 2000) (162115198766747 / 50000) := by
  exact
    packedTile65536 3242258688 3242389760 14 5947 56940 32 _ _ (68436 / 3125) (437991 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3242389760 :
    ThetaLowerSegment 3242389760 3242520832 (162115198766747 / 50000)
      (162121765349813 / 50000) := by
  exact
    packedTile65536 3242389760 3242520832 14 5997 56941 32 _ _ (547489 / 25000) (2189959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3242520832 :
    ThetaLowerSegment 3242520832 3242651904 (162121765349813 / 50000)
      (162128289240653 / 50000) := by
  exact
    packedTile65536 3242520832 3242651904 14 5958 56943 32 _ _ (54749 / 2500) (2189963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3242651904 :
    ThetaLowerSegment 3242651904 3242782976 (162128289240653 / 50000)
      (162134792338751 / 50000) := by
  exact
    packedTile65536 3242651904 3242782976 14 5939 56944 32 _ _ (547491 / 25000) (2189967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3242782976 :
    ThetaLowerSegment 3242782976 3242914048 (162134792338751 / 50000)
      (162141411517031 / 50000) := by
  exact
    packedTile65536 3242782976 3242914048 14 6045 56945 32 _ _ (136873 / 6250) (2189971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3242914048 :
    ThetaLowerSegment 3242914048 3243045120 (162141411517031 / 50000) (32429593877637 / 10000) := by
  exact
    packedTile65536 3242914048 3243045120 14 5989 56946 32 _ _ (547493 / 25000) (87599 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3243045120 :
    ThetaLowerSegment 3243045120 3243176192 (32429593877637 / 10000) (162154557930981 / 50000) := by
  exact
    packedTile65536 3243045120 3243176192 14 6017 56947 32 _ _ (273747 / 12500) (2189979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3243176192 :
    ThetaLowerSegment 3243176192 3243307264 (162154557930981 / 50000)
      (162161153055751 / 50000) := by
  exact
    packedTile65536 3243176192 3243307264 14 6023 56948 32 _ _ (109499 / 5000) (2189983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3243307264 :
    ThetaLowerSegment 3243307264 3243438336 (162161153055751 / 50000)
      (162167710962839 / 50000) := by
  exact
    packedTile65536 3243307264 3243438336 14 5989 56950 32 _ _ (68437 / 3125) (2189987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3243438336 :
    ThetaLowerSegment 3243438336 3243569408 (162167710962839 / 50000)
      (162174198802289 / 50000) := by
  exact
    packedTile65536 3243438336 3243569408 14 5925 56951 32 _ _ (547497 / 25000) (2189991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3243569408 :
    ThetaLowerSegment 3243569408 3243700480 (162174198802289 / 50000)
      (324361631732277 / 100000) := by
  exact
    packedTile65536 3243569408 3243700480 14 6043 56952 32 _ _ (2189993 / 100000) (547499 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3243700480 :
    ThetaLowerSegment 3243700480 3243831552 (324361631732277 / 100000)
      (81093707711049 / 25000) := by
  exact
    packedTile65536 3243700480 3243831552 14 6027 56953 32 _ _ (2189997 / 100000) (219 / 10)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3243831552 :
    ThetaLowerSegment 3243831552 3243962624 (81093707711049 / 25000) (162193987615099 / 50000) := by
  exact
    packedTile65536 3243831552 3243962624 14 6002 56954 32 _ _ (2190001 / 100000) (547501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3243962624 :
    ThetaLowerSegment 3243962624 3244093696 (162193987615099 / 50000) (10137533893754 / 3125) := by
  exact
    packedTile65536 3243962624 3244093696 14 5986 56955 32 _ _ (438001 / 20000) (273751 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3244093696 :
    ThetaLowerSegment 3244093696 3244224768 (10137533893754 / 3125) (12976571876977 / 4000) := by
  exact
    packedTile65536 3244093696 3244224768 14 6033 56956 32 _ _ (2190009 / 100000) (547503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3244224768 :
    ThetaLowerSegment 3244224768 3244355840 (12976571876977 / 4000) (324427498322789 / 100000) := by
  exact
    packedTile65536 3244224768 3244355840 14 6028 56958 32 _ _ (2190013 / 100000) (68438 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3244355840 :
    ThetaLowerSegment 3244355840 3244486912 (324427498322789 / 100000) (648881202389 / 200) := by
  exact
    packedTile65536 3244355840 3244486912 14 5983 56959 32 _ _ (2190017 / 100000) (109501 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3244486912 :
    ThetaLowerSegment 3244486912 3244617984 (648881202389 / 200) (32445358801903 / 10000) := by
  exact
    packedTile65536 3244486912 3244617984 14 5930 56960 32 _ _ (2190021 / 100000) (273753 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3244617984 :
    ThetaLowerSegment 3244617984 3244749056 (32445358801903 / 10000) (32446682453013 / 10000) := by
  exact
    packedTile65536 3244617984 3244749056 14 6044 56961 32 _ _ (87601 / 4000) (547507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3244749056 :
    ThetaLowerSegment 3244749056 3244880128 (32446682453013 / 10000) (6489598418071 / 2000) := by
  exact
    packedTile65536 3244749056 3244880128 14 5980 56962 32 _ _ (2190029 / 100000) (136877 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3244880128 :
    ThetaLowerSegment 3244880128 3245011200 (6489598418071 / 2000) (6489861222031 / 2000) := by
  exact
    packedTile65536 3244880128 3245011200 14 6000 56963 32 _ _ (2190033 / 100000) (547509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245011200 :
    ThetaLowerSegment 3245011200 3245142272 (6489861222031 / 2000) (162253083141479 / 50000) := by
  exact
    packedTile65536 3245011200 3245142272 14 5984 56964 32 _ _ (2190037 / 100000) (54751 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245142272 :
    ThetaLowerSegment 3245142272 3245273344 (162253083141479 / 50000) (4056491386363 / 1250) := by
  exact
    packedTile65536 3245142272 3245273344 14 6002 56966 32 _ _ (2190041 / 100000) (547511 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245273344 :
    ThetaLowerSegment 3245273344 3245404416 (4056491386363 / 1250) (64906481037619 / 20000) := by
  exact
    packedTile65536 3245273344 3245404416 14 5979 56967 32 _ _ (438009 / 20000) (68439 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245404416 :
    ThetaLowerSegment 3245404416 3245535488 (64906481037619 / 20000)
      (324545598043271 / 100000) := by
  exact
    packedTile65536 3245404416 3245535488 14 6024 56968 32 _ _ (2190049 / 100000) (547513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245535488 :
    ThetaLowerSegment 3245535488 3245666560 (324545598043271 / 100000) (8113964790693 / 2500) := by
  exact
    packedTile65536 3245535488 3245666560 14 5933 56969 32 _ _ (2190053 / 100000) (273757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245666560 :
    ThetaLowerSegment 3245666560 3245797632 (8113964790693 / 2500) (64914317923203 / 20000) := by
  exact
    packedTile65536 3245666560 3245797632 14 5935 56970 32 _ _ (2190057 / 100000) (109503 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245797632 :
    ThetaLowerSegment 3245797632 3245928704 (64914317923203 / 20000) (81146161142409 / 25000) := by
  exact
    packedTile65536 3245797632 3245928704 14 5961 56971 32 _ _ (2190061 / 100000) (136879 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245928704 :
    ThetaLowerSegment 3245928704 3246059776 (81146161142409 / 25000)
      (324597874752301 / 100000) := by
  exact
    packedTile65536 3245928704 3246059776 14 6041 56973 32 _ _ (438013 / 20000) (547517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3246059776 :
    ThetaLowerSegment 3246059776 3246190848 (324597874752301 / 100000)
      (32461114876051 / 10000) := by
  exact
    packedTile65536 3246059776 3246190848 14 6061 56974 32 _ _ (2190069 / 100000) (273759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3246190848 :
    ThetaLowerSegment 3246190848 3246321920 (32461114876051 / 10000) (162312074516919 / 50000) := by
  exact
    packedTile65536 3246190848 3246321920 14 5936 56975 32 _ _ (2190073 / 100000) (547519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3246321920 :
    ThetaLowerSegment 3246321920 3246452992 (162312074516919 / 50000)
      (324637239124067 / 100000) := by
  exact
    packedTile65536 3246321920 3246452992 14 5977 56976 32 _ _ (2190077 / 100000) (13688 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3246452992 :
    ThetaLowerSegment 3246452992 3246584064 (324637239124067 / 100000)
      (324650256965531 / 100000) := by
  exact
    packedTile65536 3246452992 3246584064 14 5944 56977 32 _ _ (2190081 / 100000) (547521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3246584064 :
    ThetaLowerSegment 3246584064 3246715136 (324650256965531 / 100000)
      (81165803924619 / 25000) := by
  exact
    packedTile65536 3246584064 3246715136 14 5917 56978 32 _ _ (438017 / 20000) (273761 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3246715136 :
    ThetaLowerSegment 3246715136 3246846208 (81165803924619 / 25000) (64935271684513 / 20000) := by
  exact
    packedTile65536 3246715136 3246846208 14 6001 56979 32 _ _ (2190089 / 100000) (547523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3246846208 :
    ThetaLowerSegment 3246846208 3246977280 (64935271684513 / 20000) (162344750585329 / 50000) := by
  exact
    packedTile65536 3246846208 3246977280 14 6001 56981 32 _ _ (2190093 / 100000) (136881 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3246977280 :
    ThetaLowerSegment 3246977280 3247108352 (162344750585329 / 50000) (81175634706013 / 25000) := by
  exact
    packedTile65536 3246977280 3247108352 14 5953 56982 32 _ _ (1095049 / 50000) (2190101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3247108352 :
    ThetaLowerSegment 3247108352 3247239424 (81175634706013 / 25000) (162357864904199 / 50000) := by
  exact
    packedTile65536 3247108352 3247239424 14 6023 56983 32 _ _ (1095051 / 50000) (438021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3247239424 :
    ThetaLowerSegment 3247239424 3247370496 (162357864904199 / 50000)
      (162364520636333 / 50000) := by
  exact
    packedTile65536 3247239424 3247370496 14 6078 56984 32 _ _ (1095053 / 50000) (2190109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3247370496 :
    ThetaLowerSegment 3247370496 3247501568 (162364520636333 / 50000) (81185514274099 / 25000) := by
  exact
    packedTile65536 3247370496 3247501568 14 5943 56985 32 _ _ (219011 / 10000) (2190113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3247501568 :
    ThetaLowerSegment 3247501568 3247632640 (81185514274099 / 25000) (40594386034337 / 12500) := by
  exact
    packedTile65536 3247501568 3247632640 14 5950 56986 32 _ _ (1095057 / 50000) (2190117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3247632640 :
    ThetaLowerSegment 3247632640 3247763712 (40594386034337 / 12500) (81192027679081 / 25000) := by
  exact
    packedTile65536 3247632640 3247763712 14 5946 56988 32 _ _ (1095059 / 50000) (2190121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3247763712 :
    ThetaLowerSegment 3247763712 3247894784 (81192027679081 / 25000) (162390620248857 / 50000) := by
  exact
    packedTile65536 3247763712 3247894784 14 5995 56989 32 _ _ (1095061 / 50000) (17521 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3247894784 :
    ThetaLowerSegment 3247894784 3248025856 (162390620248857 / 50000)
      (162397162155219 / 50000) := by
  exact
    packedTile65536 3247894784 3248025856 14 5974 56990 32 _ _ (1095063 / 50000) (2190129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3248025856 :
    ThetaLowerSegment 3248025856 3248156928 (162397162155219 / 50000) (81201916098067 / 25000) := by
  exact
    packedTile65536 3248025856 3248156928 14 6091 56991 32 _ _ (219013 / 10000) (2190133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3248156928 :
    ThetaLowerSegment 3248156928 3248288000 (81201916098067 / 25000) (81205200204 / 25) := by
  exact
    packedTile65536 3248156928 3248288000 14 5998 56992 32 _ _ (1095067 / 50000) (2190137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3248288000 :
    ThetaLowerSegment 3248288000 3248419072 (81205200204 / 25) (20302122447819 / 6250) := by
  exact
    packedTile65536 3248288000 3248419072 14 6008 56993 32 _ _ (1095069 / 50000) (2190141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3248419072 :
    ThetaLowerSegment 3248419072 3248550144 (20302122447819 / 6250) (10151480088567 / 3125) := by
  exact
    packedTile65536 3248419072 3248550144 14 6120 56994 32 _ _ (1095071 / 50000) (438029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3248550144 :
    ThetaLowerSegment 3248550144 3248681216 (10151480088567 / 3125) (32486054970321 / 10000) := by
  exact
    packedTile65536 3248550144 3248681216 14 6021 56996 32 _ _ (1095073 / 50000) (2190149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3248681216 :
    ThetaLowerSegment 3248681216 3248812288 (32486054970321 / 10000) (32487358547601 / 10000) := by
  exact
    packedTile65536 3248681216 3248812288 14 5952 56997 32 _ _ (43803 / 2000) (2190153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3248812288 :
    ThetaLowerSegment 3248812288 3248943360 (32487358547601 / 10000) (20305419168039 / 6250) := by
  exact
    packedTile65536 3248812288 3248943360 14 5991 56998 32 _ _ (1095077 / 50000) (2190157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3248943360 :
    ThetaLowerSegment 3248943360 3249074432 (20305419168039 / 6250) (81224884158547 / 25000) := by
  exact
    packedTile65536 3248943360 3249074432 14 5858 56999 32 _ _ (1095079 / 50000) (2190161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249074432 :
    ThetaLowerSegment 3249074432 3249205504 (81224884158547 / 25000) (81228173781871 / 25000) := by
  exact
    packedTile65536 3249074432 3249205504 14 6008 57000 32 _ _ (1095081 / 50000) (438033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249205504 :
    ThetaLowerSegment 3249205504 3249336576 (81228173781871 / 25000) (162462783366533 / 50000) := by
  exact
    packedTile65536 3249205504 3249336576 14 5877 57001 32 _ _ (1095083 / 50000) (2190169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249336576 :
    ThetaLowerSegment 3249336576 3249467648 (162462783366533 / 50000) (81234644633259 / 25000) := by
  exact
    packedTile65536 3249336576 3249467648 14 5941 57002 32 _ _ (219017 / 10000) (2190173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249467648 :
    ThetaLowerSegment 3249467648 3249598720 (81234644633259 / 25000) (162475797368559 / 50000) := by
  exact
    packedTile65536 3249467648 3249598720 14 5943 57004 32 _ _ (1095087 / 50000) (2190177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249598720 :
    ThetaLowerSegment 3249598720 3249729792 (162475797368559 / 50000) (8124115602651 / 2500) := by
  exact
    packedTile65536 3249598720 3249729792 14 5949 57005 32 _ _ (1095089 / 50000) (2190181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249729792 :
    ThetaLowerSegment 3249729792 3249860864 (8124115602651 / 2500) (162488903405749 / 50000) := by
  exact
    packedTile65536 3249729792 3249860864 14 6019 57006 32 _ _ (1095091 / 50000) (438037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249860864 :
    ThetaLowerSegment 3249860864 3249991936 (162488903405749 / 50000)
      (162495445491331 / 50000) := by
  exact
    packedTile65536 3249860864 3249991936 14 5974 57007 32 _ _ (1095093 / 50000) (2190189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249991936 :
    ThetaLowerSegment 3249991936 3250123008 (162495445491331 / 50000)
      (162501917502781 / 50000) := by
  exact
    packedTile65536 3249991936 3250123008 14 5910 57008 32 _ _ (219019 / 10000) (2190193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3250123008 :
    ThetaLowerSegment 3250123008 3250254080 (162501917502781 / 50000) (32501700245189 / 10000) := by
  exact
    packedTile65536 3250123008 3250254080 14 6012 57009 32 _ _ (1095097 / 50000) (2190197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3250254080 :
    ThetaLowerSegment 3250254080 3250385152 (32501700245189 / 10000) (162515152857271 / 50000) := by
  exact
    packedTile65536 3250254080 3250385152 14 6074 57010 32 _ _ (1095099 / 50000) (2190201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3250385152 :
    ThetaLowerSegment 3250385152 3250516224 (162515152857271 / 50000) (40630404857169 / 12500) := by
  exact
    packedTile65536 3250385152 3250516224 14 5905 57012 32 _ _ (1095101 / 50000) (438041 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3250516224 :
    ThetaLowerSegment 3250516224 3250647296 (40630404857169 / 12500) (32505638666397 / 10000) := by
  exact
    packedTile65536 3250516224 3250647296 14 6003 57013 32 _ _ (1095103 / 50000) (2190209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3250647296 :
    ThetaLowerSegment 3250647296 3250778368 (32505638666397 / 10000) (16253471687247 / 5000) := by
  exact
    packedTile65536 3250647296 3250778368 14 5957 57014 32 _ _ (219021 / 10000) (2190213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3250778368 :
    ThetaLowerSegment 3250778368 3250909440 (16253471687247 / 5000) (32508252685021 / 10000) := by
  exact
    packedTile65536 3250778368 3250909440 14 5978 57015 32 _ _ (438043 / 20000) (1095109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3250909440 :
    ThetaLowerSegment 3250909440 3251040512 (32508252685021 / 10000)
      (325095403147711 / 100000) := by
  exact
    packedTile65536 3250909440 3251040512 14 5879 57016 32 _ _ (2190219 / 100000) (1095111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3251040512 :
    ThetaLowerSegment 3251040512 3251171584 (325095403147711 / 100000) (16255436313711 / 5000) := by
  exact
    packedTile65536 3251040512 3251171584 14 6083 57017 32 _ _ (2190223 / 100000) (1095113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3251171584 :
    ThetaLowerSegment 3251171584 3251302656 (16255436313711 / 5000) (81280471289509 / 25000) := by
  exact
    packedTile65536 3251171584 3251302656 14 6008 57019 32 _ _ (2190227 / 100000) (219023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3251302656 :
    ThetaLowerSegment 3251302656 3251433728 (81280471289509 / 25000) (162567541745021 / 50000) := by
  exact
    packedTile65536 3251302656 3251433728 14 6026 57020 32 _ _ (2190231 / 100000) (1095117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3251433728 :
    ThetaLowerSegment 3251433728 3251564800 (162567541745021 / 50000) (20321775281207 / 6250) := by
  exact
    packedTile65536 3251433728 3251564800 14 6082 57021 32 _ _ (438047 / 20000) (1095119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3251564800 :
    ThetaLowerSegment 3251564800 3251695872 (20321775281207 / 6250) (40645204192859 / 12500) := by
  exact
    packedTile65536 3251564800 3251695872 14 6040 57022 32 _ _ (2190239 / 100000) (1095121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3251695872 :
    ThetaLowerSegment 3251695872 3251826944 (40645204192859 / 12500)
      (325174882322779 / 100000) := by
  exact
    packedTile65536 3251695872 3251826944 14 6049 57023 32 _ _ (2190243 / 100000) (1095123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3251826944 :
    ThetaLowerSegment 3251826944 3251958016 (325174882322779 / 100000)
      (325187826682549 / 100000) := by
  exact
    packedTile65536 3251826944 3251958016 14 5910 57024 32 _ _ (2190247 / 100000) (8761 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3251958016 :
    ThetaLowerSegment 3251958016 3252089088 (325187826682549 / 100000)
      (65040187505007 / 20000) := by
  exact
    packedTile65536 3251958016 3252089088 14 5986 57025 32 _ _ (2190251 / 100000) (1095127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3252089088 :
    ThetaLowerSegment 3252089088 3252220160 (65040187505007 / 20000) (32521405496223 / 10000) := by
  exact
    packedTile65536 3252089088 3252220160 14 5989 57027 32 _ _ (438051 / 20000) (1095129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3252220160 :
    ThetaLowerSegment 3252220160 3252351232 (32521405496223 / 10000) (162613585116561 / 50000) := by
  exact
    packedTile65536 3252220160 3252351232 14 5988 57028 32 _ _ (2190259 / 100000) (1095131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3252351232 :
    ThetaLowerSegment 3252351232 3252482304 (162613585116561 / 50000)
      (325240340284541 / 100000) := by
  exact
    packedTile65536 3252351232 3252482304 14 6013 57029 32 _ _ (2190263 / 100000) (1095133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3252482304 :
    ThetaLowerSegment 3252482304 3252613376 (325240340284541 / 100000)
      (162626731087069 / 50000) := by
  exact
    packedTile65536 3252482304 3252613376 14 5991 57030 32 _ _ (2190267 / 100000) (219027 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3252613376 :
    ThetaLowerSegment 3252613376 3252744448 (162626731087069 / 50000) (81316645474357 / 25000) := by
  exact
    packedTile65536 3252613376 3252744448 14 5990 57031 32 _ _ (2190271 / 100000) (1095137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3252744448 :
    ThetaLowerSegment 3252744448 3252875520 (81316645474357 / 25000)
      (325279629365603 / 100000) := by
  exact
    packedTile65536 3252744448 3252875520 14 5957 57032 32 _ _ (87611 / 4000) (1095139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3252875520 :
    ThetaLowerSegment 3252875520 3253006592 (325279629365603 / 100000)
      (325292849889647 / 100000) := by
  exact
    packedTile65536 3252875520 3253006592 14 6036 57033 32 _ _ (2190279 / 100000) (1095141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253006592 :
    ThetaLowerSegment 3253006592 3253137664 (325292849889647 / 100000)
      (325306083579533 / 100000) := by
  exact
    packedTile65536 3253006592 3253137664 14 6042 57035 32 _ _ (2190283 / 100000) (1095143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253137664 :
    ThetaLowerSegment 3253137664 3253268736 (325306083579533 / 100000)
      (40664878248177 / 12500) := by
  exact
    packedTile65536 3253137664 3253268736 14 5909 57036 32 _ _ (2190287 / 100000) (219029 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253268736 :
    ThetaLowerSegment 3253268736 3253399808 (40664878248177 / 12500)
      (325332200585781 / 100000) := by
  exact
    packedTile65536 3253268736 3253399808 14 6015 57037 32 _ _ (2190291 / 100000) (1095147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253399808 :
    ThetaLowerSegment 3253399808 3253530880 (325332200585781 / 100000)
      (325345373019911 / 100000) := by
  exact
    packedTile65536 3253399808 3253530880 14 6014 57038 32 _ _ (438059 / 20000) (1095149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253530880 :
    ThetaLowerSegment 3253530880 3253661952 (325345373019911 / 100000)
      (325358295784011 / 100000) := by
  exact
    packedTile65536 3253530880 3253661952 14 5900 57039 32 _ _ (2190299 / 100000) (1095151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253661952 :
    ThetaLowerSegment 3253661952 3253793024 (325358295784011 / 100000)
      (325371472646859 / 100000) := by
  exact
    packedTile65536 3253661952 3253793024 14 6016 57040 32 _ _ (2190303 / 100000) (1095153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253793024 :
    ThetaLowerSegment 3253793024 3253924096 (325371472646859 / 100000) (8134614431341 / 2500) := by
  exact
    packedTile65536 3253793024 3253924096 14 5983 57042 32 _ _ (2190307 / 100000) (219031 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253924096 :
    ThetaLowerSegment 3253924096 3254055168 (8134614431341 / 2500) (325397808922391 / 100000) := by
  exact
    packedTile65536 3253924096 3254055168 14 6041 57043 32 _ _ (2190311 / 100000) (1095157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3254055168 :
    ThetaLowerSegment 3254055168 3254186240 (325397808922391 / 100000)
      (81352702110479 / 25000) := by
  exact
    packedTile65536 3254055168 3254186240 14 5935 57044 32 _ _ (438063 / 20000) (1095159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3254186240 :
    ThetaLowerSegment 3254186240 3254317312 (81352702110479 / 25000)
      (325424114629841 / 100000) := by
  exact
    packedTile65536 3254186240 3254317312 14 6075 57045 32 _ _ (2190319 / 100000) (1095161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3254317312 :
    ThetaLowerSegment 3254317312 3254448384 (325424114629841 / 100000)
      (162718605285529 / 50000) := by
  exact
    packedTile65536 3254317312 3254448384 14 5979 57046 32 _ _ (2190323 / 100000) (1095163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3254448384 :
    ThetaLowerSegment 3254448384 3254579456 (162718605285529 / 50000) (65090070944677 / 20000) := by
  exact
    packedTile65536 3254448384 3254579456 14 6001 57047 32 _ _ (2190327 / 100000) (219033 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3254579456 :
    ThetaLowerSegment 3254579456 3254710528 (65090070944677 / 20000) (32546370479083 / 10000) := by
  exact
    packedTile65536 3254579456 3254710528 14 6095 57048 32 _ _ (2190331 / 100000) (1095167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3254710528 :
    ThetaLowerSegment 3254710528 3254841600 (32546370479083 / 10000) (65095347018749 / 20000) := by
  exact
    packedTile65536 3254710528 3254841600 14 5949 57050 32 _ _ (438067 / 20000) (1095169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3254841600 :
    ThetaLowerSegment 3254841600 3254972672 (65095347018749 / 20000) (40686198774167 / 12500) := by
  exact
    packedTile65536 3254841600 3254972672 14 5869 57051 32 _ _ (2190339 / 100000) (1095171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3254972672 :
    ThetaLowerSegment 3254972672 3255103744 (40686198774167 / 12500) (162751403361499 / 50000) := by
  exact
    packedTile65536 3254972672 3255103744 14 6034 57052 32 _ _ (2190343 / 100000) (1095173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3255103744 :
    ThetaLowerSegment 3255103744 3255234816 (162751403361499 / 50000)
      (325515854620077 / 100000) := by
  exact
    packedTile65536 3255103744 3255234816 14 5957 57053 32 _ _ (2190347 / 100000) (43807 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3255234816 :
    ThetaLowerSegment 3255234816 3255365888 (325515854620077 / 100000)
      (325529112820733 / 100000) := by
  exact
    packedTile65536 3255234816 3255365888 14 6053 57054 32 _ _ (136897 / 6250) (438071 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3255365888 :
    ThetaLowerSegment 3255365888 3255496960 (325529112820733 / 100000)
      (325542222101393 / 100000) := by
  exact
    packedTile65536 3255365888 3255496960 14 5985 57055 32 _ _ (547589 / 25000) (2190359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3255496960 :
    ThetaLowerSegment 3255496960 3255628032 (325542222101393 / 100000)
      (325555162748273 / 100000) := by
  exact
    packedTile65536 3255496960 3255628032 14 5908 57056 32 _ _ (54759 / 2500) (2190363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3255628032 :
    ThetaLowerSegment 3255628032 3255759104 (325555162748273 / 100000)
      (325568580918137 / 100000) := by
  exact
    packedTile65536 3255628032 3255759104 14 6126 57058 32 _ _ (547591 / 25000) (2190367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3255759104 :
    ThetaLowerSegment 3255759104 3255890176 (325568580918137 / 100000)
      (325581712174297 / 100000) := by
  exact
    packedTile65536 3255759104 3255890176 14 5995 57059 32 _ _ (68449 / 3125) (2190371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3255890176 :
    ThetaLowerSegment 3255890176 3256021248 (325581712174297 / 100000)
      (325594834692949 / 100000) := by
  exact
    packedTile65536 3255890176 3256021248 14 5991 57060 32 _ _ (547593 / 25000) (17523 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3256021248 :
    ThetaLowerSegment 3256021248 3256152320 (325594834692949 / 100000)
      (325607895905037 / 100000) := by
  exact
    packedTile65536 3256021248 3256152320 14 5963 57061 32 _ _ (273797 / 12500) (2190379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3256152320 :
    ThetaLowerSegment 3256152320 3256283392 (325607895905037 / 100000)
      (325620965902497 / 100000) := by
  exact
    packedTile65536 3256152320 3256283392 14 5967 57062 32 _ _ (109519 / 5000) (2190383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3256283392 :
    ThetaLowerSegment 3256283392 3256414464 (325620965902497 / 100000) (13025361436953 / 4000) := by
  exact
    packedTile65536 3256283392 3256414464 14 5967 57063 32 _ _ (136899 / 6250) (2190387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3256414464 :
    ThetaLowerSegment 3256414464 3256545536 (13025361436953 / 4000) (325647105969021 / 100000) := by
  exact
    packedTile65536 3256414464 3256545536 14 5967 57065 32 _ _ (547597 / 25000) (2190391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3256545536 :
    ThetaLowerSegment 3256545536 3256676608 (325647105969021 / 100000)
      (325660138801421 / 100000) := by
  exact
    packedTile65536 3256545536 3256676608 14 5950 57066 32 _ _ (273799 / 12500) (438079 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3256676608 :
    ThetaLowerSegment 3256676608 3256807680 (325660138801421 / 100000)
      (325673329366133 / 100000) := by
  exact
    packedTile65536 3256676608 3256807680 14 6022 57067 32 _ _ (547599 / 25000) (2190399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3256807680 :
    ThetaLowerSegment 3256807680 3256938752 (325673329366133 / 100000)
      (325686417006133 / 100000) := by
  exact
    packedTile65536 3256807680 3256938752 14 5975 57068 32 _ _ (2738 / 125) (2190403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3256938752 :
    ThetaLowerSegment 3256938752 3257069824 (325686417006133 / 100000)
      (325699311914481 / 100000) := by
  exact
    packedTile65536 3256938752 3257069824 14 5887 57069 32 _ _ (547601 / 25000) (2190407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257069824 :
    ThetaLowerSegment 3257069824 3257200896 (325699311914481 / 100000)
      (325712189323113 / 100000) := by
  exact
    packedTile65536 3257069824 3257200896 14 5879 57070 32 _ _ (273801 / 12500) (2190411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257200896 :
    ThetaLowerSegment 3257200896 3257331968 (325712189323113 / 100000)
      (325725395317061 / 100000) := by
  exact
    packedTile65536 3257200896 3257331968 14 6029 57071 32 _ _ (547603 / 25000) (438083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257331968 :
    ThetaLowerSegment 3257331968 3257463040 (325725395317061 / 100000)
      (325738632000949 / 100000) := by
  exact
    packedTile65536 3257331968 3257463040 14 6043 57073 32 _ _ (136901 / 6250) (2190419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257463040 :
    ThetaLowerSegment 3257463040 3257594112 (325738632000949 / 100000)
      (325751794234729 / 100000) := by
  exact
    packedTile65536 3257463040 3257594112 14 6009 57074 32 _ _ (109521 / 5000) (2190423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257594112 :
    ThetaLowerSegment 3257594112 3257725184 (325751794234729 / 100000)
      (325764960873393 / 100000) := by
  exact
    packedTile65536 3257594112 3257725184 14 6011 57075 32 _ _ (273803 / 12500) (2190427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257725184 :
    ThetaLowerSegment 3257725184 3257856256 (325764960873393 / 100000)
      (325778026776413 / 100000) := by
  exact
    packedTile65536 3257725184 3257856256 14 5965 57076 32 _ _ (547607 / 25000) (2190431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257856256 :
    ThetaLowerSegment 3257856256 3257987328 (325778026776413 / 100000)
      (325791213177053 / 100000) := by
  exact
    packedTile65536 3257856256 3257987328 14 6020 57077 32 _ _ (68451 / 3125) (438087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257987328 :
    ThetaLowerSegment 3257987328 3258118400 (325791213177053 / 100000)
      (325804274746921 / 100000) := by
  exact
    packedTile65536 3257987328 3258118400 14 5963 57078 32 _ _ (547609 / 25000) (2190439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3258118400 :
    ThetaLowerSegment 3258118400 3258249472 (325804274746921 / 100000)
      (325817358245041 / 100000) := by
  exact
    packedTile65536 3258118400 3258249472 14 5973 57079 32 _ _ (54761 / 2500) (2190443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3258249472 :
    ThetaLowerSegment 3258249472 3258380544 (325817358245041 / 100000)
      (65166155380997 / 20000) := by
  exact
    packedTile65536 3258249472 3258380544 14 6126 57081 32 _ _ (547611 / 25000) (2190447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3258380544 :
    ThetaLowerSegment 3258380544 3258511616 (65166155380997 / 20000)
      (325843709309977 / 100000) := by
  exact
    packedTile65536 3258380544 3258511616 14 5904 57082 32 _ _ (136903 / 6250) (2190451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3258511616 :
    ThetaLowerSegment 3258511616 3258642688 (325843709309977 / 100000)
      (325856731547117 / 100000) := by
  exact
    packedTile65536 3258511616 3258642688 14 5945 57083 32 _ _ (547613 / 25000) (438091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3258642688 :
    ThetaLowerSegment 3258642688 3258773760 (325856731547117 / 100000)
      (325869819521717 / 100000) := by
  exact
    packedTile65536 3258642688 3258773760 14 5975 57084 32 _ _ (273807 / 12500) (2190459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3258773760 :
    ThetaLowerSegment 3258773760 3258904832 (325869819521717 / 100000)
      (325882865901477 / 100000) := by
  exact
    packedTile65536 3258773760 3258904832 14 5956 57085 32 _ _ (109523 / 5000) (2190463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3258904832 :
    ThetaLowerSegment 3258904832 3259035904 (325882865901477 / 100000)
      (325895899162277 / 100000) := by
  exact
    packedTile65536 3258904832 3259035904 14 5950 57086 32 _ _ (68452 / 3125) (2190467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3259035904 :
    ThetaLowerSegment 3259035904 3259166976 (325895899162277 / 100000)
      (65181837308233 / 20000) := by
  exact
    packedTile65536 3259035904 3259166976 14 6066 57087 32 _ _ (547617 / 25000) (2190471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3259166976 :
    ThetaLowerSegment 3259166976 3259298048 (65181837308233 / 20000)
      (325922392896853 / 100000) := by
  exact
    packedTile65536 3259166976 3259298048 14 6029 57089 32 _ _ (273809 / 12500) (87619 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3259298048 :
    ThetaLowerSegment 3259298048 3259429120 (325922392896853 / 100000)
      (325935522609997 / 100000) := by
  exact
    packedTile65536 3259298048 3259429120 14 5994 57090 32 _ _ (547619 / 25000) (2190479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3259429120 :
    ThetaLowerSegment 3259429120 3259560192 (325935522609997 / 100000)
      (325948836347437 / 100000) := by
  exact
    packedTile65536 3259429120 3259560192 14 6078 57091 32 _ _ (27381 / 1250) (2190483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3259560192 :
    ThetaLowerSegment 3259560192 3259691264 (325948836347437 / 100000)
      (325961942013209 / 100000) := by
  exact
    packedTile65536 3259560192 3259691264 14 5983 57092 32 _ _ (547621 / 25000) (2190487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3259691264 :
    ThetaLowerSegment 3259691264 3259822336 (325961942013209 / 100000)
      (325975095893649 / 100000) := by
  exact
    packedTile65536 3259691264 3259822336 14 6005 57093 32 _ _ (273811 / 12500) (2190491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3259822336 :
    ThetaLowerSegment 3259822336 3259953408 (325975095893649 / 100000)
      (325988170940397 / 100000) := by
  exact
    packedTile65536 3259822336 3259953408 14 5969 57094 32 _ _ (547623 / 25000) (438099 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3259953408 :
    ThetaLowerSegment 3259953408 3260084480 (325988170940397 / 100000) (13040051943317 / 4000) := by
  exact
    packedTile65536 3259953408 3260084480 14 5993 57096 32 _ _ (68453 / 3125) (2190499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3260084480 :
    ThetaLowerSegment 3260084480 3260215552 (13040051943317 / 4000) (13040572493737 / 4000) := by
  exact
    packedTile65536 3260084480 3260215552 14 5941 57097 32 _ _ (4381 / 200) (2190503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3260215552 :
    ThetaLowerSegment 3260215552 3260346624 (13040572493737 / 4000) (326027551749601 / 100000) := by
  exact
    packedTile65536 3260215552 3260346624 14 6044 57098 32 _ _ (273813 / 12500) (2190507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3260346624 :
    ThetaLowerSegment 3260346624 3260477696 (326027551749601 / 100000)
      (326040629082361 / 100000) := by
  exact
    packedTile65536 3260346624 3260477696 14 5970 57099 32 _ _ (547627 / 25000) (2190511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3260477696 :
    ThetaLowerSegment 3260477696 3260608768 (326040629082361 / 100000)
      (65210744354517 / 20000) := by
  exact
    packedTile65536 3260477696 3260608768 14 5977 57100 32 _ _ (136907 / 6250) (438103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3260608768 :
    ThetaLowerSegment 3260608768 3260739840 (65210744354517 / 20000)
      (326066704960917 / 100000) := by
  exact
    packedTile65536 3260608768 3260739840 14 5927 57101 32 _ _ (547629 / 25000) (2190519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3260739840 :
    ThetaLowerSegment 3260739840 3260870912 (326066704960917 / 100000)
      (326079869986117 / 100000) := by
  exact
    packedTile65536 3260739840 3260870912 14 6010 57102 32 _ _ (54763 / 2500) (2190523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3260870912 :
    ThetaLowerSegment 3260870912 3261001984 (326079869986117 / 100000)
      (326092986849817 / 100000) := by
  exact
    packedTile65536 3260870912 3261001984 14 5988 57104 32 _ _ (87621 / 4000) (68454 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3261001984 :
    ThetaLowerSegment 3261001984 3261133056 (326092986849817 / 100000)
      (163052982867071 / 50000) := by
  exact
    packedTile65536 3261001984 3261133056 14 5925 57105 32 _ _ (2190529 / 100000) (547633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3261133056 :
    ThetaLowerSegment 3261133056 3261264128 (163052982867071 / 50000) (65223809081337 / 20000) := by
  exact
    packedTile65536 3261133056 3261264128 14 5971 57106 32 _ _ (2190533 / 100000) (273817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3261264128 :
    ThetaLowerSegment 3261264128 3261395200 (65223809081337 / 20000) (16306615455411 / 5000) := by
  exact
    packedTile65536 3261264128 3261395200 14 6055 57107 32 _ _ (2190537 / 100000) (109527 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3261395200 :
    ThetaLowerSegment 3261395200 3261526272 (16306615455411 / 5000) (10192036897723 / 3125) := by
  exact
    packedTile65536 3261395200 3261526272 14 5876 57108 32 _ _ (2190541 / 100000) (136909 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3261526272 :
    ThetaLowerSegment 3261526272 3261657344 (10192036897723 / 3125) (163079067805133 / 50000) := by
  exact
    packedTile65536 3261526272 3261657344 14 5914 57109 32 _ _ (438109 / 20000) (547637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3261657344 :
    ThetaLowerSegment 3261657344 3261788416 (163079067805133 / 50000)
      (326171473863127 / 100000) := by
  exact
    packedTile65536 3261657344 3261788416 14 6089 57110 32 _ _ (2190549 / 100000) (273819 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3261788416 :
    ThetaLowerSegment 3261788416 3261919488 (326171473863127 / 100000)
      (326184446317993 / 100000) := by
  exact
    packedTile65536 3261788416 3261919488 14 5922 57112 32 _ _ (2190553 / 100000) (547639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3261919488 :
    ThetaLowerSegment 3261919488 3262050560 (326184446317993 / 100000)
      (326197563373309 / 100000) := by
  exact
    packedTile65536 3261919488 3262050560 14 5988 57113 32 _ _ (2190557 / 100000) (13691 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3262050560 :
    ThetaLowerSegment 3262050560 3262181632 (326197563373309 / 100000) (20388160819693 / 6250) := by
  exact
    packedTile65536 3262050560 3262181632 14 5939 57114 32 _ _ (2190561 / 100000) (547641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3262181632 :
    ThetaLowerSegment 3262181632 3262312704 (20388160819693 / 6250) (40777953610311 / 12500) := by
  exact
    packedTile65536 3262181632 3262312704 14 5960 57115 32 _ _ (438113 / 20000) (273821 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3262312704 :
    ThetaLowerSegment 3262312704 3262443776 (40777953610311 / 12500) (65247329486811 / 20000) := by
  exact
    packedTile65536 3262312704 3262443776 14 5943 57116 32 _ _ (2190569 / 100000) (547643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3262443776 :
    ThetaLowerSegment 3262443776 3262574848 (65247329486811 / 20000) (65249936268681 / 20000) := by
  exact
    packedTile65536 3262443776 3262574848 14 5950 57117 32 _ _ (2190573 / 100000) (136911 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3262574848 :
    ThetaLowerSegment 3262574848 3262705920 (65249936268681 / 20000) (20391426961071 / 6250) := by
  exact
    packedTile65536 3262574848 3262705920 14 6003 57118 32 _ _ (2190577 / 100000) (109529 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3262705920 :
    ThetaLowerSegment 3262705920 3262836992 (20391426961071 / 6250) (81569009049851 / 25000) := by
  exact
    packedTile65536 3262705920 3262836992 14 6028 57120 32 _ _ (2190581 / 100000) (273823 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3262836992 :
    ThetaLowerSegment 3262836992 3262968064 (81569009049851 / 25000) (40786141987213 / 12500) := by
  exact
    packedTile65536 3262836992 3262968064 14 5980 57121 32 _ _ (438117 / 20000) (547647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3262968064 :
    ThetaLowerSegment 3262968064 3263099136 (40786141987213 / 12500) (163151041139347 / 50000) := by
  exact
    packedTile65536 3262968064 3263099136 14 5910 57122 32 _ _ (2190589 / 100000) (68456 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3263099136 :
    ThetaLowerSegment 3263099136 3263230208 (163151041139347 / 50000)
      (326315136022381 / 100000) := by
  exact
    packedTile65536 3263099136 3263230208 14 5959 57123 32 _ _ (2190593 / 100000) (547649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3263230208 :
    ThetaLowerSegment 3263230208 3263361280 (326315136022381 / 100000)
      (326328310272739 / 100000) := by
  exact
    packedTile65536 3263230208 3263361280 14 6014 57124 32 _ _ (2190597 / 100000) (10953 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3263361280 :
    ThetaLowerSegment 3263361280 3263492352 (326328310272739 / 100000)
      (163170655744837 / 50000) := by
  exact
    packedTile65536 3263361280 3263492352 14 5935 57125 32 _ _ (2190601 / 100000) (547651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3263492352 :
    ThetaLowerSegment 3263492352 3263623424 (163170655744837 / 50000) (81588676212161 / 25000) := by
  exact
    packedTile65536 3263492352 3263623424 14 6114 57126 32 _ _ (438121 / 20000) (136913 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3263623424 :
    ThetaLowerSegment 3263623424 3263754496 (81588676212161 / 25000)
      (326367784974983 / 100000) := by
  exact
    packedTile65536 3263623424 3263754496 14 5971 57128 32 _ _ (2190609 / 100000) (547653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3263754496 :
    ThetaLowerSegment 3263754496 3263885568 (326367784974983 / 100000)
      (326380902365627 / 100000) := by
  exact
    packedTile65536 3263754496 3263885568 14 5988 57129 32 _ _ (2190613 / 100000) (273827 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3263885568 :
    ThetaLowerSegment 3263885568 3264016640 (326380902365627 / 100000) (20399612134167 / 6250) := by
  exact
    packedTile65536 3263885568 3264016640 14 5885 57130 32 _ _ (2190617 / 100000) (109531 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3264016640 :
    ThetaLowerSegment 3264016640 3264147712 (20399612134167 / 6250) (326406887488389 / 100000) := by
  exact
    packedTile65536 3264016640 3264147712 14 5977 57131 32 _ _ (2190621 / 100000) (68457 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3264147712 :
    ThetaLowerSegment 3264147712 3264278784 (326406887488389 / 100000)
      (40802487201283 / 12500) := by
  exact
    packedTile65536 3264147712 3264278784 14 5939 57132 32 _ _ (701 / 32) (547657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3264278784 :
    ThetaLowerSegment 3264278784 3264409856 (40802487201283 / 12500) (81608280061727 / 25000) := by
  exact
    packedTile65536 3264278784 3264409856 14 6036 57133 32 _ _ (2190629 / 100000) (273829 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3264409856 :
    ThetaLowerSegment 3264409856 3264540928 (81608280061727 / 25000) (81611530961099 / 25000) := by
  exact
    packedTile65536 3264409856 3264540928 14 5936 57135 32 _ _ (2190633 / 100000) (547659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3264540928 :
    ThetaLowerSegment 3264540928 3264672000 (81611530961099 / 25000)
      (326459147181361 / 100000) := by
  exact
    packedTile65536 3264540928 3264672000 14 5945 57136 32 _ _ (2190637 / 100000) (27383 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3264672000 :
    ThetaLowerSegment 3264672000 3264803072 (326459147181361 / 100000)
      (81618043730847 / 25000) := by
  exact
    packedTile65536 3264672000 3264803072 14 5947 57137 32 _ _ (2190641 / 100000) (547661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3264803072 :
    ThetaLowerSegment 3264803072 3264934144 (81618043730847 / 25000) (81621347223507 / 25000) := by
  exact
    packedTile65536 3264803072 3264934144 14 6032 57138 32 _ _ (438129 / 20000) (273831 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3264934144 :
    ThetaLowerSegment 3264934144 3265065216 (81621347223507 / 25000)
      (326498574410359 / 100000) := by
  exact
    packedTile65536 3264934144 3265065216 14 6019 57139 32 _ _ (2190649 / 100000) (547663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265065216 :
    ThetaLowerSegment 3265065216 3265196288 (326498574410359 / 100000)
      (326511564982649 / 100000) := by
  exact
    packedTile65536 3265065216 3265196288 14 5930 57140 32 _ _ (2190653 / 100000) (68458 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265196288 :
    ThetaLowerSegment 3265196288 3265327360 (326511564982649 / 100000)
      (40815592723063 / 12500) := by
  exact
    packedTile65536 3265196288 3265327360 14 6015 57141 32 _ _ (2190657 / 100000) (109533 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265327360 :
    ThetaLowerSegment 3265327360 3265458432 (40815592723063 / 12500) (65307568825589 / 20000) := by
  exact
    packedTile65536 3265327360 3265458432 14 5981 57143 32 _ _ (2190661 / 100000) (273833 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265458432 :
    ThetaLowerSegment 3265458432 3265589504 (65307568825589 / 20000) (32655095525797 / 10000) := by
  exact
    packedTile65536 3265458432 3265589504 14 5985 57144 32 _ _ (438133 / 20000) (547667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265589504 :
    ThetaLowerSegment 3265589504 3265720576 (32655095525797 / 10000) (163281992678591 / 50000) := by
  exact
    packedTile65536 3265589504 3265720576 14 5948 57145 32 _ _ (2190669 / 100000) (136917 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265720576 :
    ThetaLowerSegment 3265720576 3265851648 (163281992678591 / 50000)
      (326577249882197 / 100000) := by
  exact
    packedTile65536 3265720576 3265851648 14 6055 57146 32 _ _ (2190673 / 100000) (547669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265851648 :
    ThetaLowerSegment 3265851648 3265982720 (326577249882197 / 100000)
      (32659028221967 / 10000) := by
  exact
    packedTile65536 3265851648 3265982720 14 5949 57147 32 _ _ (2190677 / 100000) (54767 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265982720 :
    ThetaLowerSegment 3265982720 3266113792 (32659028221967 / 10000)
      (326603586225383 / 100000) := by
  exact
    packedTile65536 3265982720 3266113792 14 6073 57148 32 _ _ (2190681 / 100000) (547671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3266113792 :
    ThetaLowerSegment 3266113792 3266244864 (326603586225383 / 100000)
      (326616633945243 / 100000) := by
  exact
    packedTile65536 3266113792 3266244864 14 5956 57149 32 _ _ (438137 / 20000) (68459 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3266244864 :
    ThetaLowerSegment 3266244864 3266375936 (326616633945243 / 100000)
      (163314962427703 / 50000) := by
  exact
    packedTile65536 3266244864 3266375936 14 6067 57151 32 _ _ (2190689 / 100000) (547673 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3266375936 :
    ThetaLowerSegment 3266375936 3266507008 (163314962427703 / 50000) (20415175656977 / 6250) := by
  exact
    packedTile65536 3266375936 3266507008 14 5882 57152 32 _ _ (2190693 / 100000) (273837 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3266507008 :
    ThetaLowerSegment 3266507008 3266638080 (20415175656977 / 6250) (326655878019237 / 100000) := by
  exact
    packedTile65536 3266507008 3266638080 14 5965 57153 32 _ _ (2190697 / 100000) (21907 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3266638080 :
    ThetaLowerSegment 3266638080 3266769152 (326655878019237 / 100000)
      (163334402672919 / 50000) := by
  exact
    packedTile65536 3266638080 3266769152 14 5901 57154 32 _ _ (2190701 / 100000) (136919 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3266769152 :
    ThetaLowerSegment 3266769152 3266900224 (163334402672919 / 50000)
      (163340944118049 / 50000) := by
  exact
    packedTile65536 3266769152 3266900224 14 5972 57155 32 _ _ (438141 / 20000) (547677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3266900224 :
    ThetaLowerSegment 3266900224 3267031296 (163340944118049 / 50000) (40836887276421 / 12500) := by
  exact
    packedTile65536 3266900224 3267031296 14 6030 57156 32 _ _ (2190709 / 100000) (273839 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3267031296 :
    ThetaLowerSegment 3267031296 3267162368 (40836887276421 / 12500) (10209630934758 / 3125) := by
  exact
    packedTile65536 3267031296 3267162368 14 5976 57157 32 _ _ (2190713 / 100000) (547679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3267162368 :
    ThetaLowerSegment 3267162368 3267293440 (10209630934758 / 3125) (326721375837879 / 100000) := by
  exact
    packedTile65536 3267162368 3267293440 14 6019 57159 32 _ _ (2190717 / 100000) (13692 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3267293440 :
    ThetaLowerSegment 3267293440 3267424512 (326721375837879 / 100000)
      (326734353669083 / 100000) := by
  exact
    packedTile65536 3267293440 3267424512 14 5924 57160 32 _ _ (2190721 / 100000) (547681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3267424512 :
    ThetaLowerSegment 3267424512 3267555584 (326734353669083 / 100000)
      (81686859717377 / 25000) := by
  exact
    packedTile65536 3267424512 3267555584 14 5973 57161 32 _ _ (87629 / 4000) (273841 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3267555584 :
    ThetaLowerSegment 3267555584 3267686656 (81686859717377 / 25000)
      (326760405794459 / 100000) := by
  exact
    packedTile65536 3267555584 3267686656 14 5919 57162 32 _ _ (2190729 / 100000) (547683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3267686656 :
    ThetaLowerSegment 3267686656 3267817728 (326760405794459 / 100000) (8169335304407 / 2500) := by
  exact
    packedTile65536 3267686656 3267817728 14 5937 57163 32 _ _ (2190733 / 100000) (136921 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3267817728 :
    ThetaLowerSegment 3267817728 3267948800 (8169335304407 / 2500) (20424156501287 / 6250) := by
  exact
    packedTile65536 3267817728 3267948800 14 5976 57164 32 _ _ (2190737 / 100000) (109537 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3267948800 :
    ThetaLowerSegment 3267948800 3268079872 (20424156501287 / 6250) (326799584935103 / 100000) := by
  exact
    packedTile65536 3267948800 3268079872 14 5971 57165 32 _ _ (2190741 / 100000) (273843 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3268079872 :
    ThetaLowerSegment 3268079872 3268210944 (326799584935103 / 100000)
      (326812663682753 / 100000) := by
  exact
    packedTile65536 3268079872 3268210944 14 5970 57167 32 _ _ (438149 / 20000) (547687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3268210944 :
    ThetaLowerSegment 3268210944 3268342016 (326812663682753 / 100000)
      (65365143233059 / 20000) := by
  exact
    packedTile65536 3268210944 3268342016 14 5958 57168 32 _ _ (2190749 / 100000) (68461 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3268342016 :
    ThetaLowerSegment 3268342016 3268473088 (65365143233059 / 20000) (163419433627777 / 50000) := by
  exact
    packedTile65536 3268342016 3268473088 14 6003 57169 32 _ _ (2190753 / 100000) (547689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3268473088 :
    ThetaLowerSegment 3268473088 3268604160 (163419433627777 / 50000) (65370355477311 / 20000) := by
  exact
    packedTile65536 3268473088 3268604160 14 5893 57170 32 _ _ (2190757 / 100000) (54769 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3268604160 :
    ThetaLowerSegment 3268604160 3268735232 (65370355477311 / 20000) (10214529701014 / 3125) := by
  exact
    packedTile65536 3268604160 3268735232 14 6013 57171 32 _ _ (2190761 / 100000) (547691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3268735232 :
    ThetaLowerSegment 3268735232 3268866304 (10214529701014 / 3125) (326878272474413 / 100000) := by
  exact
    packedTile65536 3268735232 3268866304 14 6081 57172 32 _ _ (438153 / 20000) (136923 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3268866304 :
    ThetaLowerSegment 3268866304 3268997376 (326878272474413 / 100000)
      (326891167340747 / 100000) := by
  exact
    packedTile65536 3268866304 3268997376 14 5886 57174 32 _ _ (2190769 / 100000) (547693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3268997376 :
    ThetaLowerSegment 3268997376 3269128448 (326891167340747 / 100000)
      (163452181183263 / 50000) := by
  exact
    packedTile65536 3268997376 3269128448 14 6023 57175 32 _ _ (2190773 / 100000) (273847 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3269128448 :
    ThetaLowerSegment 3269128448 3269259520 (163452181183263 / 50000) (81729380043297 / 25000) := by
  exact
    packedTile65536 3269128448 3269259520 14 6006 57176 32 _ _ (2190777 / 100000) (109539 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3269259520 :
    ThetaLowerSegment 3269259520 3269390592 (81729380043297 / 25000)
      (326930785352143 / 100000) := by
  exact
    packedTile65536 3269259520 3269390592 14 6055 57177 32 _ _ (2190781 / 100000) (68462 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3269390592 :
    ThetaLowerSegment 3269390592 3269521664 (326930785352143 / 100000)
      (326943763562483 / 100000) := by
  exact
    packedTile65536 3269390592 3269521664 14 5924 57178 32 _ _ (438157 / 20000) (547697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3269521664 :
    ThetaLowerSegment 3269521664 3269652736 (326943763562483 / 100000)
      (163478339131819 / 50000) := by
  exact
    packedTile65536 3269521664 3269652736 14 5895 57179 32 _ _ (2190789 / 100000) (273849 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3269652736 :
    ThetaLowerSegment 3269652736 3269783808 (163478339131819 / 50000)
      (163484876458131 / 50000) := by
  exact
    packedTile65536 3269652736 3269783808 14 5968 57180 32 _ _ (2190793 / 100000) (547699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3269783808 :
    ThetaLowerSegment 3269783808 3269914880 (163484876458131 / 50000)
      (326982746533269 / 100000) := by
  exact
    packedTile65536 3269783808 3269914880 14 5931 57182 32 _ _ (2190797 / 100000) (5477 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3269914880 :
    ThetaLowerSegment 3269914880 3270045952 (326982746533269 / 100000)
      (81748932852699 / 25000) := by
  exact
    packedTile65536 3269914880 3270045952 14 5927 57183 32 _ _ (2190801 / 100000) (547701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3270045952 :
    ThetaLowerSegment 3270045952 3270177024 (81748932852699 / 25000) (163504383350273 / 50000) := by
  exact
    packedTile65536 3270045952 3270177024 14 5950 57184 32 _ _ (438161 / 20000) (273851 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3270177024 :
    ThetaLowerSegment 3270177024 3270308096 (163504383350273 / 50000)
      (327021830494613 / 100000) := by
  exact
    packedTile65536 3270177024 3270308096 14 5963 57185 32 _ _ (2190809 / 100000) (547703 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3270308096 :
    ThetaLowerSegment 3270308096 3270439168 (327021830494613 / 100000)
      (327034935943961 / 100000) := by
  exact
    packedTile65536 3270308096 3270439168 14 5982 57186 32 _ _ (1095407 / 50000) (2190817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3270439168 :
    ThetaLowerSegment 3270439168 3270570240 (327034935943961 / 100000)
      (327048056752963 / 100000) := by
  exact
    packedTile65536 3270439168 3270570240 14 5989 57187 32 _ _ (1095409 / 50000) (2190821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3270570240 :
    ThetaLowerSegment 3270570240 3270701312 (327048056752963 / 100000)
      (327061155677701 / 100000) := by
  exact
    packedTile65536 3270570240 3270701312 14 5979 57188 32 _ _ (1095411 / 50000) (87633 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3270701312 :
    ThetaLowerSegment 3270701312 3270832384 (327061155677701 / 100000)
      (65414850925271 / 20000) := by
  exact
    packedTile65536 3270701312 3270832384 14 5979 57190 32 _ _ (1095413 / 50000) (2190829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3270832384 :
    ThetaLowerSegment 3270832384 3270963456 (65414850925271 / 20000) (65417471157951 / 20000) := by
  exact
    packedTile65536 3270832384 3270963456 14 5980 57191 32 _ _ (219083 / 10000) (2190833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3270963456 :
    ThetaLowerSegment 3270963456 3271094528 (65417471157951 / 20000) (65420111112921 / 20000) := by
  exact
    packedTile65536 3270963456 3271094528 14 6025 57192 32 _ _ (1095417 / 50000) (2190837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3271094528 :
    ThetaLowerSegment 3271094528 3271225600 (65420111112921 / 20000)
      (327113672111711 / 100000) := by
  exact
    packedTile65536 3271094528 3271225600 14 5987 57193 32 _ _ (1095419 / 50000) (2190841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3271225600 :
    ThetaLowerSegment 3271225600 3271356672 (327113672111711 / 100000)
      (327126692285717 / 100000) := by
  exact
    packedTile65536 3271225600 3271356672 14 5943 57194 32 _ _ (1095421 / 50000) (438169 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3271356672 :
    ThetaLowerSegment 3271356672 3271487744 (327126692285717 / 100000)
      (327139692765881 / 100000) := by
  exact
    packedTile65536 3271356672 3271487744 14 5934 57195 32 _ _ (1095423 / 50000) (2190849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3271487744 :
    ThetaLowerSegment 3271487744 3271618816 (327139692765881 / 100000)
      (327152763376981 / 100000) := by
  exact
    packedTile65536 3271487744 3271618816 14 5966 57196 32 _ _ (43817 / 2000) (2190853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3271618816 :
    ThetaLowerSegment 3271618816 3271749888 (327152763376981 / 100000)
      (65433217192031 / 20000) := by
  exact
    packedTile65536 3271618816 3271749888 14 6081 57198 32 _ _ (1095427 / 50000) (2190857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3271749888 :
    ThetaLowerSegment 3271749888 3271880960 (65433217192031 / 20000)
      (327179248635019 / 100000) := by
  exact
    packedTile65536 3271749888 3271880960 14 6008 57199 32 _ _ (1095429 / 50000) (2190861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3271880960 :
    ThetaLowerSegment 3271880960 3272012032 (327179248635019 / 100000)
      (65438471312473 / 20000) := by
  exact
    packedTile65536 3271880960 3272012032 14 5983 57200 32 _ _ (1095431 / 50000) (438173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3272012032 :
    ThetaLowerSegment 3272012032 3272143104 (65438471312473 / 20000)
      (327205438223251 / 100000) := by
  exact
    packedTile65536 3272012032 3272143104 14 5971 57201 32 _ _ (1095433 / 50000) (2190869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3272143104 :
    ThetaLowerSegment 3272143104 3272274176 (327205438223251 / 100000)
      (327218614115431 / 100000) := by
  exact
    packedTile65536 3272143104 3272274176 14 6014 57202 32 _ _ (219087 / 10000) (2190873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3272274176 :
    ThetaLowerSegment 3272274176 3272405248 (327218614115431 / 100000)
      (327231693633211 / 100000) := by
  exact
    packedTile65536 3272274176 3272405248 14 5970 57203 32 _ _ (1095437 / 50000) (2190877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3272405248 :
    ThetaLowerSegment 3272405248 3272536320 (327231693633211 / 100000)
      (327244753456969 / 100000) := by
  exact
    packedTile65536 3272405248 3272536320 14 5961 57204 32 _ _ (1095439 / 50000) (2190881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3272536320 :
    ThetaLowerSegment 3272536320 3272667392 (327244753456969 / 100000)
      (327257833022509 / 100000) := by
  exact
    packedTile65536 3272536320 3272667392 14 5970 57206 32 _ _ (1095441 / 50000) (438177 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3272667392 :
    ThetaLowerSegment 3272667392 3272798464 (327257833022509 / 100000)
      (327271092264581 / 100000) := by
  exact
    packedTile65536 3272667392 3272798464 14 6052 57207 32 _ _ (1095443 / 50000) (2190889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3272798464 :
    ThetaLowerSegment 3272798464 3272929536 (327271092264581 / 100000)
      (327284209123011 / 100000) := by
  exact
    packedTile65536 3272798464 3272929536 14 5987 57208 32 _ _ (219089 / 10000) (2190893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3272929536 :
    ThetaLowerSegment 3272929536 3273060608 (327284209123011 / 100000)
      (327297122252247 / 100000) := by
  exact
    packedTile65536 3272929536 3273060608 14 5894 57209 32 _ _ (1095447 / 50000) (2190897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273060608 :
    ThetaLowerSegment 3273060608 3273191680 (327297122252247 / 100000)
      (65462049584433 / 20000) := by
  exact
    packedTile65536 3273060608 3273191680 14 5991 57210 32 _ _ (1095449 / 50000) (2190901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273191680 :
    ThetaLowerSegment 3273191680 3273322752 (65462049584433 / 20000)
      (327323198343887 / 100000) := by
  exact
    packedTile65536 3273191680 3273322752 14 5911 57211 32 _ _ (1095451 / 50000) (438181 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273322752 :
    ThetaLowerSegment 3273322752 3273339136 (327323198343887 / 100000)
      (327324867814259 / 100000) := by
  exact
    packedTile65536 3273322752 3273339136 11 762 57212 32 _ _ (1095453 / 50000) (2190909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273339136 :
    ThetaLowerSegment 3273339136 3273341184 (327324867814259 / 100000)
      (65465009055529 / 20000) := by
  exact
    packedTile65536 3273339136 3273341184 8 81 57213 32 _ _ (1095453 / 50000) (2190909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3241341184_3273341184 :
    ThetaLowerSegment 3241341184 3273341184 (162062909616841 / 50000) (65465009055529 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3241341184 cell3241472256)
                  (ThetaLowerSegment.join cell3241603328 cell3241734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3241865472 cell3241996544)
                  (ThetaLowerSegment.join cell3242127616 cell3242258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3242389760 cell3242520832)
                  (ThetaLowerSegment.join cell3242651904 cell3242782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3242914048 cell3243045120)
                  (ThetaLowerSegment.join cell3243176192 cell3243307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3243438336 cell3243569408)
                  (ThetaLowerSegment.join cell3243700480 cell3243831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3243962624 cell3244093696)
                  (ThetaLowerSegment.join cell3244224768 cell3244355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3244486912 cell3244617984)
                  (ThetaLowerSegment.join cell3244749056 cell3244880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3245011200 cell3245142272)
                  (ThetaLowerSegment.join cell3245273344 cell3245404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3245535488 cell3245666560)
                  (ThetaLowerSegment.join cell3245797632 cell3245928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3246059776 cell3246190848)
                  (ThetaLowerSegment.join cell3246321920 cell3246452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3246584064 cell3246715136)
                  (ThetaLowerSegment.join cell3246846208 cell3246977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3247108352 cell3247239424)
                  (ThetaLowerSegment.join cell3247370496 cell3247501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3247632640 cell3247763712)
                  (ThetaLowerSegment.join cell3247894784 cell3248025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3248156928 cell3248288000)
                  (ThetaLowerSegment.join cell3248419072 cell3248550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3248681216 cell3248812288)
                  (ThetaLowerSegment.join cell3248943360 cell3249074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3249205504 cell3249336576)
                  (ThetaLowerSegment.join cell3249467648 cell3249598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3249729792 cell3249860864)
                  (ThetaLowerSegment.join cell3249991936 cell3250123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3250254080 cell3250385152)
                  (ThetaLowerSegment.join cell3250516224 cell3250647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3250778368 cell3250909440)
                  (ThetaLowerSegment.join cell3251040512 cell3251171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3251302656 cell3251433728)
                  (ThetaLowerSegment.join cell3251564800 cell3251695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3251826944 cell3251958016)
                  (ThetaLowerSegment.join cell3252089088 cell3252220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3252351232 cell3252482304)
                  (ThetaLowerSegment.join cell3252613376 cell3252744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3252875520 cell3253006592)
                  (ThetaLowerSegment.join cell3253137664 cell3253268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3253399808 cell3253530880)
                  (ThetaLowerSegment.join cell3253661952 cell3253793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3253924096 cell3254055168)
                  (ThetaLowerSegment.join cell3254186240 cell3254317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3254448384 cell3254579456)
                  (ThetaLowerSegment.join cell3254710528 cell3254841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3254972672 cell3255103744)
                  (ThetaLowerSegment.join cell3255234816 cell3255365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3255496960 cell3255628032)
                  (ThetaLowerSegment.join cell3255759104 cell3255890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3256021248 cell3256152320)
                  (ThetaLowerSegment.join cell3256283392 cell3256414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3256545536 cell3256676608)
                  (ThetaLowerSegment.join cell3256807680 cell3256938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3257069824 cell3257200896)
                  (ThetaLowerSegment.join cell3257331968 cell3257463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3257594112 cell3257725184)
                  (ThetaLowerSegment.join cell3257856256 cell3257987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3258118400 cell3258249472)
                  (ThetaLowerSegment.join cell3258380544 cell3258511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3258642688 cell3258773760)
                  (ThetaLowerSegment.join cell3258904832 cell3259035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3259166976 cell3259298048)
                  (ThetaLowerSegment.join cell3259429120 cell3259560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3259691264 cell3259822336)
                  (ThetaLowerSegment.join cell3259953408 cell3260084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3260215552 cell3260346624)
                  (ThetaLowerSegment.join cell3260477696 cell3260608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3260739840 cell3260870912)
                  (ThetaLowerSegment.join cell3261001984 cell3261133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3261264128 cell3261395200)
                  (ThetaLowerSegment.join cell3261526272 cell3261657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3261788416 cell3261919488)
                  (ThetaLowerSegment.join cell3262050560 cell3262181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3262312704 cell3262443776)
                  (ThetaLowerSegment.join cell3262574848 cell3262705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3262836992 cell3262968064)
                  (ThetaLowerSegment.join cell3263099136 cell3263230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3263361280 cell3263492352)
                  (ThetaLowerSegment.join cell3263623424 cell3263754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3263885568 cell3264016640)
                  (ThetaLowerSegment.join cell3264147712 cell3264278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3264409856 cell3264540928)
                  (ThetaLowerSegment.join cell3264672000 cell3264803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3264934144 cell3265065216)
                  (ThetaLowerSegment.join cell3265196288 cell3265327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3265458432 cell3265589504)
                  (ThetaLowerSegment.join cell3265720576 cell3265851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3265982720 cell3266113792)
                  (ThetaLowerSegment.join cell3266244864 cell3266375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3266507008 cell3266638080)
                  (ThetaLowerSegment.join cell3266769152 cell3266900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3267031296 cell3267162368)
                  (ThetaLowerSegment.join cell3267293440 cell3267424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3267555584 cell3267686656)
                  (ThetaLowerSegment.join cell3267817728 cell3267948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3268079872 cell3268210944)
                  (ThetaLowerSegment.join cell3268342016 cell3268473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3268604160 cell3268735232)
                  (ThetaLowerSegment.join cell3268866304 cell3268997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3269128448 cell3269259520)
                  (ThetaLowerSegment.join cell3269390592 cell3269521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3269652736 cell3269783808)
                  (ThetaLowerSegment.join cell3269914880 cell3270045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3270177024 cell3270308096)
                  (ThetaLowerSegment.join cell3270439168 cell3270570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3270701312 cell3270832384)
                  (ThetaLowerSegment.join cell3270963456 cell3271094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3271225600 cell3271356672)
                  (ThetaLowerSegment.join cell3271487744 cell3271618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3271749888 cell3271880960)
                  (ThetaLowerSegment.join cell3272012032 cell3272143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3272274176 cell3272405248)
                  (ThetaLowerSegment.join cell3272536320 cell3272667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3272798464 cell3272929536)
                (ThetaLowerSegment.join cell3273060608 cell3273191680))
              (ThetaLowerSegment.join cell3273322752 cell3273339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
