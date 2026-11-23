/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 393341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell361341184 :
    ThetaLowerSegment 361341184 361373952 (36131060492137 / 100000) (36134333545789 / 100000) := by
  exact
    packedTile32768 361341184 361373952 12 1661 19008 28 _ _ (492633 / 25000) (394107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361373952 :
    ThetaLowerSegment 361373952 361406720 (36134333545789 / 100000) (7227523293419 / 20000) := by
  exact
    packedTile32768 361373952 361406720 12 1666 19009 28 _ _ (1970541 / 100000) (123159 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361406720 :
    ThetaLowerSegment 361406720 361439488 (7227523293419 / 20000) (7228187368769 / 20000) := by
  exact
    packedTile32768 361406720 361439488 12 1685 19010 28 _ _ (39411 / 2000) (1970553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361439488 :
    ThetaLowerSegment 361439488 361472256 (7228187368769 / 20000) (36144259206319 / 100000) := by
  exact
    packedTile32768 361439488 361472256 12 1686 19011 28 _ _ (1970559 / 100000) (985281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361472256 :
    ThetaLowerSegment 361472256 361505024 (36144259206319 / 100000) (36147506702383 / 100000) := by
  exact
    packedTile32768 361472256 361505024 12 1648 19012 28 _ _ (246321 / 12500) (1970571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361505024 :
    ThetaLowerSegment 361505024 361537792 (36147506702383 / 100000) (36150781801357 / 100000) := by
  exact
    packedTile32768 361505024 361537792 12 1662 19013 28 _ _ (1970577 / 100000) (98529 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361537792 :
    ThetaLowerSegment 361537792 361570560 (36150781801357 / 100000) (36154015532983 / 100000) := by
  exact
    packedTile32768 361537792 361570560 12 1641 19014 28 _ _ (985293 / 50000) (1970589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361570560 :
    ThetaLowerSegment 361570560 361603328 (36154015532983 / 100000) (36157322191393 / 100000) := by
  exact
    packedTile32768 361570560 361603328 12 1678 19015 28 _ _ (394119 / 20000) (985299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361603328 :
    ThetaLowerSegment 361603328 361636096 (36157322191393 / 100000) (36160695865441 / 100000) := by
  exact
    packedTile32768 361603328 361636096 12 1712 19015 28 _ _ (492651 / 25000) (1970607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361636096 :
    ThetaLowerSegment 361636096 361701632 (36160695865441 / 100000) (18083635900511 / 50000) := by
  exact
    packedTile32768 361636096 361701632 13 3337 19016 28 _ _ (1970613 / 100000) (246327 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361701632 :
    ThetaLowerSegment 361701632 361767168 (18083635900511 / 50000) (18086939665059 / 50000) := by
  exact
    packedTile32768 361701632 361767168 13 3353 19018 28 _ _ (246329 / 12500) (394127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361767168 :
    ThetaLowerSegment 361767168 361832704 (18086939665059 / 50000) (4522550026371 / 12500) := by
  exact
    packedTile32768 361767168 361832704 13 3309 19020 28 _ _ (39413 / 2000) (1970653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361832704 :
    ThetaLowerSegment 361832704 361898240 (4522550026371 / 12500) (2261674319789 / 6250) := by
  exact
    packedTile32768 361832704 361898240 13 3242 19021 28 _ _ (492667 / 25000) (1970671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361898240 :
    ThetaLowerSegment 361898240 361931008 (2261674319789 / 6250) (3618998359863 / 10000) := by
  exact
    packedTile32768 361898240 361931008 12 1621 19023 28 _ _ (985343 / 50000) (1970689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361931008 :
    ThetaLowerSegment 361931008 361963776 (3618998359863 / 10000) (45241632738 / 125) := by
  exact
    packedTile32768 361931008 361963776 12 1686 19024 28 _ _ (394139 / 20000) (985349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361963776 :
    ThetaLowerSegment 361963776 361996544 (45241632738 / 125) (1131142925551 / 3125) := by
  exact
    packedTile32768 361963776 361996544 12 1658 19025 28 _ _ (123169 / 6250) (1970707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361996544 :
    ThetaLowerSegment 361996544 362029312 (1131142925551 / 3125) (18099944178449 / 50000) := by
  exact
    packedTile32768 361996544 362029312 12 1682 19026 28 _ _ (1970713 / 100000) (492679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362029312 :
    ThetaLowerSegment 362029312 362062080 (18099944178449 / 50000) (9050786490091 / 25000) := by
  exact
    packedTile32768 362029312 362062080 12 1653 19027 28 _ _ (985361 / 50000) (78829 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362062080 :
    ThetaLowerSegment 362062080 362094848 (9050786490091 / 25000) (7241299634759 / 20000) := by
  exact
    packedTile32768 362062080 362094848 12 1701 19027 28 _ _ (1970731 / 100000) (985367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362094848 :
    ThetaLowerSegment 362094848 362127616 (7241299634759 / 20000) (289678661327 / 800) := by
  exact
    packedTile32768 362094848 362127616 12 1692 19028 28 _ _ (98537 / 5000) (1970743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362127616 :
    ThetaLowerSegment 362127616 362193152 (289678661327 / 800) (2263520639083 / 6250) := by
  exact
    packedTile32768 362127616 362193152 13 3297 19029 28 _ _ (1970749 / 100000) (61586 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362193152 :
    ThetaLowerSegment 362193152 362225920 (2263520639083 / 6250) (18109838293847 / 50000) := by
  exact
    packedTile32768 362193152 362225920 12 1698 19031 28 _ _ (1970767 / 100000) (197077 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362225920 :
    ThetaLowerSegment 362225920 362291456 (18109838293847 / 50000) (18113134416707 / 50000) := by
  exact
    packedTile32768 362225920 362291456 13 3345 19032 28 _ _ (246347 / 12500) (1970779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362291456 :
    ThetaLowerSegment 362291456 362356992 (18113134416707 / 50000) (905821725563 / 2500) := by
  exact
    packedTile32768 362291456 362356992 13 3349 19033 28 _ _ (985397 / 50000) (1970797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362356992 :
    ThetaLowerSegment 362356992 362422528 (905821725563 / 2500) (9059851059607 / 25000) := by
  exact
    packedTile32768 362356992 362422528 13 3316 19035 28 _ _ (1970813 / 100000) (61588 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362422528 :
    ThetaLowerSegment 362422528 362488064 (9059851059607 / 25000) (2265370234211 / 6250) := by
  exact
    packedTile32768 362422528 362488064 13 3308 19037 28 _ _ (1970831 / 100000) (985417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362488064 :
    ThetaLowerSegment 362488064 362553600 (2265370234211 / 6250) (18126255162367 / 50000) := by
  exact
    packedTile32768 362488064 362553600 13 3342 19039 28 _ _ (1970849 / 100000) (492713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362553600 :
    ThetaLowerSegment 362553600 362619136 (18126255162367 / 50000) (36259012214967 / 100000) := by
  exact
    packedTile32768 362553600 362619136 13 3299 19040 28 _ _ (1970867 / 100000) (197087 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362619136 :
    ThetaLowerSegment 362619136 362684672 (36259012214967 / 100000) (18132772849371 / 50000) := by
  exact
    packedTile32768 362619136 362684672 13 3315 19042 28 _ _ (394177 / 20000) (246361 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362684672 :
    ThetaLowerSegment 362684672 362750208 (18132772849371 / 50000) (36272095009411 / 100000) := by
  exact
    packedTile32768 362684672 362750208 13 3323 19044 28 _ _ (1970903 / 100000) (985453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362750208 :
    ThetaLowerSegment 362750208 362815744 (36272095009411 / 100000) (36278535979239 / 100000) := by
  exact
    packedTile32768 362750208 362815744 13 3268 19046 28 _ _ (1970921 / 100000) (492731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362815744 :
    ThetaLowerSegment 362815744 362848512 (36278535979239 / 100000) (36281929936197 / 100000) := by
  exact
    packedTile32768 362815744 362848512 12 1722 19047 28 _ _ (1970939 / 100000) (985471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362848512 :
    ThetaLowerSegment 362848512 362914048 (36281929936197 / 100000) (36288439977441 / 100000) := by
  exact
    packedTile32768 362848512 362914048 13 3303 19048 28 _ _ (492737 / 25000) (1970951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362914048 :
    ThetaLowerSegment 362914048 362979584 (36288439977441 / 100000) (36294997381323 / 100000) := by
  exact
    packedTile32768 362914048 362979584 13 3327 19050 28 _ _ (985483 / 50000) (1970969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell362979584 :
    ThetaLowerSegment 362979584 363045120 (36294997381323 / 100000) (36301592293787 / 100000) := by
  exact
    packedTile32768 362979584 363045120 13 3346 19052 28 _ _ (246373 / 12500) (1970987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363045120 :
    ThetaLowerSegment 363045120 363110656 (36301592293787 / 100000) (36308106455397 / 100000) := by
  exact
    packedTile32768 363045120 363110656 13 3305 19053 28 _ _ (985501 / 50000) (394201 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363110656 :
    ThetaLowerSegment 363110656 363176192 (36308106455397 / 100000) (36314764560957 / 100000) := by
  exact
    packedTile32768 363110656 363176192 13 3378 19055 28 _ _ (98551 / 5000) (1971023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363176192 :
    ThetaLowerSegment 363176192 363241728 (36314764560957 / 100000) (36321440466663 / 100000) := by
  exact
    packedTile32768 363176192 363241728 13 3387 19057 28 _ _ (985519 / 50000) (1971041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363241728 :
    ThetaLowerSegment 363241728 363307264 (36321440466663 / 100000) (7265603576107 / 20000) := by
  exact
    packedTile32768 363241728 363307264 13 3337 19058 28 _ _ (123191 / 6250) (1971059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363307264 :
    ThetaLowerSegment 363307264 363372800 (7265603576107 / 20000) (7266904484947 / 20000) := by
  exact
    packedTile32768 363307264 363372800 13 3300 19060 28 _ _ (985537 / 50000) (1971077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363372800 :
    ThetaLowerSegment 363372800 363438336 (7266904484947 / 20000) (36341127554027 / 100000) := by
  exact
    packedTile32768 363372800 363438336 13 3351 19062 28 _ _ (492773 / 25000) (394219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363438336 :
    ThetaLowerSegment 363438336 363503872 (36341127554027 / 100000) (18173836806829 / 50000) := by
  exact
    packedTile32768 363438336 363503872 13 3321 19064 28 _ _ (1971111 / 100000) (985557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363503872 :
    ThetaLowerSegment 363503872 363569408 (18173836806829 / 50000) (7270828966033 / 20000) := by
  exact
    packedTile32768 363503872 363569408 13 3283 19065 28 _ _ (1971129 / 100000) (492783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363569408 :
    ThetaLowerSegment 363569408 363634944 (7270828966033 / 20000) (36360740288027 / 100000) := by
  exact
    packedTile32768 363569408 363634944 13 3346 19067 28 _ _ (1971147 / 100000) (39423 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363634944 :
    ThetaLowerSegment 363634944 363700480 (36360740288027 / 100000) (36367221478547 / 100000) := by
  exact
    packedTile32768 363634944 363700480 13 3288 19069 28 _ _ (394233 / 20000) (61599 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363700480 :
    ThetaLowerSegment 363700480 363766016 (36367221478547 / 100000) (9093464612927 / 25000) := by
  exact
    packedTile32768 363700480 363766016 13 3367 19070 28 _ _ (1971183 / 100000) (985593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363766016 :
    ThetaLowerSegment 363766016 363831552 (9093464612927 / 25000) (36380365386209 / 100000) := by
  exact
    packedTile32768 363766016 363831552 13 3301 19072 28 _ _ (1971201 / 100000) (492801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363831552 :
    ThetaLowerSegment 363831552 363897088 (36380365386209 / 100000) (7277391428509 / 20000) := by
  exact
    packedTile32768 363831552 363897088 13 3344 19074 28 _ _ (1971219 / 100000) (985611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363897088 :
    ThetaLowerSegment 363897088 363962624 (7277391428509 / 20000) (36393426742379 / 100000) := by
  exact
    packedTile32768 363897088 363962624 13 3282 19076 28 _ _ (1971237 / 100000) (49281 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell363962624 :
    ThetaLowerSegment 363962624 364028160 (36393426742379 / 100000) (18199962985057 / 50000) := by
  exact
    packedTile32768 363962624 364028160 13 3297 19077 28 _ _ (394251 / 20000) (985629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364028160 :
    ThetaLowerSegment 364028160 364093696 (18199962985057 / 50000) (4550812274287 / 12500) := by
  exact
    packedTile32768 364028160 364093696 13 3334 19079 28 _ _ (1971273 / 100000) (492819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364093696 :
    ThetaLowerSegment 364093696 364159232 (4550812274287 / 12500) (18206570722483 / 50000) := by
  exact
    packedTile32768 364093696 364159232 13 3370 19081 28 _ _ (1971291 / 100000) (985647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364159232 :
    ThetaLowerSegment 364159232 364224768 (18206570722483 / 50000) (36419790670223 / 100000) := by
  exact
    packedTile32768 364159232 364224768 13 3373 19082 28 _ _ (1971309 / 100000) (123207 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364224768 :
    ThetaLowerSegment 364224768 364290304 (36419790670223 / 100000) (18213097755823 / 50000) := by
  exact
    packedTile32768 364224768 364290304 13 3249 19084 28 _ _ (1971327 / 100000) (197133 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364290304 :
    ThetaLowerSegment 364290304 364355840 (18213097755823 / 50000) (18216362303143 / 50000) := by
  exact
    packedTile32768 364290304 364355840 13 3312 19086 28 _ _ (394269 / 20000) (492837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364355840 :
    ThetaLowerSegment 364355840 364421376 (18216362303143 / 50000) (9109814425817 / 25000) := by
  exact
    packedTile32768 364355840 364421376 13 3314 19088 28 _ _ (1971363 / 100000) (985683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364421376 :
    ThetaLowerSegment 364421376 364486912 (9109814425817 / 25000) (36445788888521 / 100000) := by
  exact
    packedTile32768 364421376 364486912 13 3313 19089 28 _ _ (1971381 / 100000) (246423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364486912 :
    ThetaLowerSegment 364486912 364552448 (36445788888521 / 100000) (36452262962837 / 100000) := by
  exact
    packedTile32768 364486912 364552448 13 3284 19091 28 _ _ (1971399 / 100000) (985701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364552448 :
    ThetaLowerSegment 364552448 364617984 (36452262962837 / 100000) (18229444447687 / 50000) := by
  exact
    packedTile32768 364552448 364617984 13 3361 19093 28 _ _ (1971417 / 100000) (98571 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364617984 :
    ThetaLowerSegment 364617984 364683520 (18229444447687 / 50000) (2279083467989 / 6250) := by
  exact
    packedTile32768 364617984 364683520 13 3270 19094 28 _ _ (394287 / 20000) (985719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364683520 :
    ThetaLowerSegment 364683520 364716288 (2279083467989 / 6250) (1139643263824 / 3125) := by
  exact
    packedTile32768 364683520 364716288 12 1648 19096 28 _ _ (1971453 / 100000) (61608 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364716288 :
    ThetaLowerSegment 364716288 364749056 (1139643263824 / 3125) (18235953177919 / 50000) := by
  exact
    packedTile32768 364716288 364749056 12 1685 19097 28 _ _ (985731 / 50000) (394293 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364749056 :
    ThetaLowerSegment 364749056 364781824 (18235953177919 / 50000) (36475184912111 / 100000) := by
  exact
    packedTile32768 364749056 364781824 12 1663 19098 28 _ _ (1971471 / 100000) (985737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364781824 :
    ThetaLowerSegment 364781824 364814592 (36475184912111 / 100000) (9119594184153 / 25000) := by
  exact
    packedTile32768 364781824 364814592 12 1619 19099 28 _ _ (1971479 / 100000) (985741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364814592 :
    ThetaLowerSegment 364814592 364847360 (9119594184153 / 25000) (9120402001361 / 25000) := by
  exact
    packedTile32768 364814592 364847360 12 1639 19100 28 _ _ (61609 / 3125) (1971491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364847360 :
    ThetaLowerSegment 364847360 364880128 (9120402001361 / 25000) (18242485689663 / 50000) := by
  exact
    packedTile32768 364847360 364880128 12 1706 19100 28 _ _ (1971497 / 100000) (3943 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364880128 :
    ThetaLowerSegment 364880128 364912896 (18242485689663 / 50000) (9122058555439 / 25000) := by
  exact
    packedTile32768 364880128 364912896 12 1655 19101 28 _ _ (985753 / 50000) (1971509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364912896 :
    ThetaLowerSegment 364912896 364945664 (9122058555439 / 25000) (9122882648709 / 25000) := by
  exact
    packedTile32768 364912896 364945664 12 1672 19102 28 _ _ (394303 / 20000) (985759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364945664 :
    ThetaLowerSegment 364945664 364978432 (9122882648709 / 25000) (9123709703027 / 25000) := by
  exact
    packedTile32768 364945664 364978432 12 1678 19103 28 _ _ (492881 / 25000) (1971527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell364978432 :
    ThetaLowerSegment 364978432 365011200 (9123709703027 / 25000) (18249045920779 / 50000) := by
  exact
    packedTile32768 364978432 365011200 12 1650 19104 28 _ _ (1971533 / 100000) (123221 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365011200 :
    ThetaLowerSegment 365011200 365043968 (18249045920779 / 50000) (4562676243343 / 12500) := by
  exact
    packedTile32768 365011200 365043968 12 1683 19105 28 _ _ (985771 / 50000) (394309 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365043968 :
    ThetaLowerSegment 365043968 365109504 (4562676243343 / 12500) (456349838011 / 1250) := by
  exact
    packedTile32768 365043968 365109504 13 3336 19106 28 _ _ (1971551 / 100000) (985777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365109504 :
    ThetaLowerSegment 365109504 365175040 (456349838011 / 1250) (456432643909 / 1250) := by
  exact
    packedTile32768 365109504 365175040 13 3360 19107 28 _ _ (1971569 / 100000) (492893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365175040 :
    ThetaLowerSegment 365175040 365240576 (456432643909 / 1250) (4565132818173 / 12500) := by
  exact
    packedTile32768 365175040 365240576 13 3272 19109 28 _ _ (1971587 / 100000) (197159 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365240576 :
    ThetaLowerSegment 365240576 365306112 (4565132818173 / 12500) (36527598415959 / 100000) := by
  exact
    packedTile32768 365240576 365306112 13 3315 19111 28 _ _ (394321 / 20000) (246451 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365306112 :
    ThetaLowerSegment 365306112 365338880 (36527598415959 / 100000) (1826548198821 / 5000) := by
  exact
    packedTile32768 365306112 365338880 12 1707 19112 28 _ _ (1971623 / 100000) (985813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365338880 :
    ThetaLowerSegment 365338880 365404416 (1826548198821 / 5000) (9134404065697 / 25000) := by
  exact
    packedTile32768 365338880 365404416 13 3374 19113 28 _ _ (123227 / 6250) (394327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365404416 :
    ThetaLowerSegment 365404416 365469952 (9134404065697 / 25000) (4568020760511 / 12500) := by
  exact
    packedTile32768 365404416 365469952 13 3322 19115 28 _ _ (39433 / 2000) (1971653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365469952 :
    ThetaLowerSegment 365469952 365535488 (4568020760511 / 12500) (1142213324331 / 3125) := by
  exact
    packedTile32768 365469952 365535488 13 3378 19117 28 _ _ (492917 / 25000) (1971671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365535488 :
    ThetaLowerSegment 365535488 365601024 (1142213324331 / 3125) (9139357881673 / 25000) := by
  exact
    packedTile32768 365535488 365601024 13 3350 19118 28 _ _ (985843 / 50000) (1971689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365601024 :
    ThetaLowerSegment 365601024 365666560 (9139357881673 / 25000) (9140991438437 / 25000) := by
  exact
    packedTile32768 365601024 365666560 13 3314 19120 28 _ _ (246463 / 12500) (1971707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365666560 :
    ThetaLowerSegment 365666560 365732096 (9140991438437 / 25000) (9142620080809 / 25000) := by
  exact
    packedTile32768 365666560 365732096 13 3304 19122 28 _ _ (985861 / 50000) (78869 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365732096 :
    ThetaLowerSegment 365732096 365797632 (9142620080809 / 25000) (9144276342409 / 25000) := by
  exact
    packedTile32768 365732096 365797632 13 3360 19124 28 _ _ (98587 / 5000) (1971743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365797632 :
    ThetaLowerSegment 365797632 365863168 (9144276342409 / 25000) (9145891212211 / 25000) := by
  exact
    packedTile32768 365797632 365863168 13 3276 19125 28 _ _ (985879 / 50000) (1971761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365863168 :
    ThetaLowerSegment 365863168 365928704 (9145891212211 / 25000) (36589998750669 / 100000) := by
  exact
    packedTile32768 365863168 365928704 13 3263 19127 28 _ _ (78871 / 4000) (985889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365928704 :
    ThetaLowerSegment 365928704 365994240 (36589998750669 / 100000) (36596600313633 / 100000) := by
  exact
    packedTile32768 365928704 365994240 13 3348 19129 28 _ _ (1971793 / 100000) (492949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell365994240 :
    ThetaLowerSegment 365994240 366059776 (36596600313633 / 100000) (36603182218751 / 100000) := by
  exact
    packedTile32768 365994240 366059776 13 3338 19130 28 _ _ (1971811 / 100000) (985907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366059776 :
    ThetaLowerSegment 366059776 366125312 (36603182218751 / 100000) (18304930401787 / 50000) := by
  exact
    packedTile32768 366059776 366125312 13 3387 19132 28 _ _ (1971829 / 100000) (246479 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366125312 :
    ThetaLowerSegment 366125312 366190848 (18304930401787 / 50000) (36616421138543 / 100000) := by
  exact
    packedTile32768 366125312 366190848 13 3327 19134 28 _ _ (1971847 / 100000) (39437 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366190848 :
    ThetaLowerSegment 366190848 366256384 (36616421138543 / 100000) (36622987448993 / 100000) := by
  exact
    packedTile32768 366190848 366256384 13 3330 19136 28 _ _ (394373 / 20000) (492967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366256384 :
    ThetaLowerSegment 366256384 366321920 (36622987448993 / 100000) (36629510437957 / 100000) := by
  exact
    packedTile32768 366256384 366321920 13 3308 19137 28 _ _ (1971883 / 100000) (985943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366321920 :
    ThetaLowerSegment 366321920 366387456 (36629510437957 / 100000) (36636061093079 / 100000) := by
  exact
    packedTile32768 366321920 366387456 13 3322 19139 28 _ _ (1971901 / 100000) (61622 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366387456 :
    ThetaLowerSegment 366387456 366452992 (36636061093079 / 100000) (3664270448819 / 10000) := by
  exact
    packedTile32768 366387456 366452992 13 3369 19141 28 _ _ (1971919 / 100000) (985961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366452992 :
    ThetaLowerSegment 366452992 366518528 (3664270448819 / 10000) (7329852235743 / 20000) := by
  exact
    packedTile32768 366452992 366518528 13 3325 19142 28 _ _ (1971937 / 100000) (98597 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366518528 :
    ThetaLowerSegment 366518528 366584064 (7329852235743 / 20000) (36655853420937 / 100000) := by
  exact
    packedTile32768 366518528 366584064 13 3343 19144 28 _ _ (985977 / 50000) (1971957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366584064 :
    ThetaLowerSegment 366584064 366649600 (36655853420937 / 100000) (36662343180789 / 100000) := by
  exact
    packedTile32768 366584064 366649600 13 3291 19146 28 _ _ (492993 / 25000) (78879 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366649600 :
    ThetaLowerSegment 366649600 366715136 (36662343180789 / 100000) (36668888215599 / 100000) := by
  exact
    packedTile32768 366649600 366715136 13 3319 19148 28 _ _ (197199 / 10000) (1971993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366715136 :
    ThetaLowerSegment 366715136 366780672 (36668888215599 / 100000) (36675462890271 / 100000) := by
  exact
    packedTile32768 366715136 366780672 13 3334 19149 28 _ _ (246501 / 12500) (1972011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366780672 :
    ThetaLowerSegment 366780672 366846208 (36675462890271 / 100000) (36682002128487 / 100000) := by
  exact
    packedTile32768 366780672 366846208 13 3316 19151 28 _ _ (986013 / 50000) (1972029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366846208 :
    ThetaLowerSegment 366846208 366911744 (36682002128487 / 100000) (36688586783403 / 100000) := by
  exact
    packedTile32768 366846208 366911744 13 3339 19153 28 _ _ (493011 / 25000) (1972047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366911744 :
    ThetaLowerSegment 366911744 366977280 (36688586783403 / 100000) (36695179386669 / 100000) := by
  exact
    packedTile32768 366911744 366977280 13 3343 19154 28 _ _ (986031 / 50000) (394413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell366977280 :
    ThetaLowerSegment 366977280 367042816 (36695179386669 / 100000) (36701671474029 / 100000) := by
  exact
    packedTile32768 366977280 367042816 13 3292 19156 28 _ _ (24651 / 1250) (1972083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367042816 :
    ThetaLowerSegment 367042816 367108352 (36701671474029 / 100000) (7341639034181 / 20000) := by
  exact
    packedTile32768 367042816 367108352 13 3308 19158 28 _ _ (1972097 / 100000) (19721 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367108352 :
    ThetaLowerSegment 367108352 367173888 (7341639034181 / 20000) (7342954829309 / 20000) := by
  exact
    packedTile32768 367108352 367173888 13 3336 19160 28 _ _ (394423 / 20000) (986059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367173888 :
    ThetaLowerSegment 367173888 367239424 (7342954829309 / 20000) (36721309795307 / 100000) := by
  exact
    packedTile32768 367173888 367239424 13 3314 19161 28 _ _ (1972133 / 100000) (246517 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367239424 :
    ThetaLowerSegment 367239424 367304960 (36721309795307 / 100000) (36727869169533 / 100000) := by
  exact
    packedTile32768 367239424 367304960 13 3326 19163 28 _ _ (1972151 / 100000) (986077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367304960 :
    ThetaLowerSegment 367304960 367370496 (36727869169533 / 100000) (18367252759109 / 50000) := by
  exact
    packedTile32768 367304960 367370496 13 3365 19165 28 _ _ (1972169 / 100000) (493043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367370496 :
    ThetaLowerSegment 367370496 367436032 (18367252759109 / 50000) (18370518700781 / 50000) := by
  exact
    packedTile32768 367370496 367436032 13 3312 19166 28 _ _ (1972187 / 100000) (197219 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367436032 :
    ThetaLowerSegment 367436032 367501568 (18370518700781 / 50000) (18373791573319 / 50000) := by
  exact
    packedTile32768 367436032 367501568 13 3319 19168 28 _ _ (493051 / 25000) (1972207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367501568 :
    ThetaLowerSegment 367501568 367567104 (18373791573319 / 50000) (18377093072947 / 50000) := by
  exact
    packedTile32768 367501568 367567104 13 3348 19170 28 _ _ (986111 / 50000) (78889 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367567104 :
    ThetaLowerSegment 367567104 367632640 (18377093072947 / 50000) (18380388685987 / 50000) := by
  exact
    packedTile32768 367567104 367632640 13 3342 19172 28 _ _ (24653 / 1250) (1972243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367632640 :
    ThetaLowerSegment 367632640 367698176 (18380388685987 / 50000) (18383682356847 / 50000) := by
  exact
    packedTile32768 367632640 367698176 13 3340 19173 28 _ _ (986129 / 50000) (1972261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367698176 :
    ThetaLowerSegment 367698176 367763712 (18383682356847 / 50000) (3677394422643 / 10000) := by
  exact
    packedTile32768 367698176 367763712 13 3336 19175 28 _ _ (493069 / 25000) (1972279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367763712 :
    ThetaLowerSegment 367763712 367829248 (3677394422643 / 10000) (9195123553701 / 25000) := by
  exact
    packedTile32768 367763712 367829248 13 3321 19177 28 _ _ (986147 / 50000) (1972297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367829248 :
    ThetaLowerSegment 367829248 367894784 (9195123553701 / 25000) (18393499448241 / 50000) := by
  exact
    packedTile32768 367829248 367894784 13 3298 19178 28 _ _ (1972311 / 100000) (986157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367894784 :
    ThetaLowerSegment 367894784 367960320 (18393499448241 / 50000) (36793470107931 / 100000) := by
  exact
    packedTile32768 367894784 367960320 13 3281 19180 28 _ _ (1972329 / 100000) (493083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell367960320 :
    ThetaLowerSegment 367960320 368025856 (36793470107931 / 100000) (36800073525687 / 100000) := by
  exact
    packedTile32768 367960320 368025856 13 3348 19182 28 _ _ (1972347 / 100000) (39447 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368025856 :
    ThetaLowerSegment 368025856 368091392 (36800073525687 / 100000) (36806669114247 / 100000) := by
  exact
    packedTile32768 368025856 368091392 13 3344 19184 28 _ _ (394473 / 20000) (123273 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368091392 :
    ThetaLowerSegment 368091392 368156928 (36806669114247 / 100000) (36813134585721 / 100000) := by
  exact
    packedTile32768 368091392 368156928 13 3278 19185 28 _ _ (1972383 / 100000) (986193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368156928 :
    ThetaLowerSegment 368156928 368222464 (36813134585721 / 100000) (36819633643721 / 100000) := by
  exact
    packedTile32768 368156928 368222464 13 3295 19187 28 _ _ (4931 / 250) (1972403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368222464 :
    ThetaLowerSegment 368222464 368288000 (36819633643721 / 100000) (7365223790821 / 20000) := by
  exact
    packedTile32768 368222464 368288000 13 3288 19189 28 _ _ (986209 / 50000) (1972421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368288000 :
    ThetaLowerSegment 368288000 368353536 (7365223790821 / 20000) (36832596433929 / 100000) := by
  exact
    packedTile32768 368288000 368353536 13 3284 19190 28 _ _ (493109 / 25000) (1972439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368353536 :
    ThetaLowerSegment 368353536 368419072 (36832596433929 / 100000) (36839206127283 / 100000) := by
  exact
    packedTile32768 368353536 368419072 13 3351 19192 28 _ _ (986227 / 50000) (1972457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368419072 :
    ThetaLowerSegment 368419072 368484608 (36839206127283 / 100000) (7369155286303 / 20000) := by
  exact
    packedTile32768 368419072 368484608 13 3331 19194 28 _ _ (246559 / 12500) (78899 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368484608 :
    ThetaLowerSegment 368484608 368550144 (7369155286303 / 20000) (3685223633299 / 10000) := by
  exact
    packedTile32768 368484608 368550144 13 3275 19195 28 _ _ (1972489 / 100000) (493123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368550144 :
    ThetaLowerSegment 368550144 368615680 (3685223633299 / 10000) (3685882450637 / 10000) := by
  exact
    packedTile32768 368550144 368615680 13 3340 19197 28 _ _ (1972507 / 100000) (197251 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368615680 :
    ThetaLowerSegment 368615680 368681216 (3685882450637 / 10000) (7373078997429 / 20000) := by
  exact
    packedTile32768 368615680 368681216 13 3331 19199 28 _ _ (78901 / 4000) (123283 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368681216 :
    ThetaLowerSegment 368681216 368746752 (7373078997429 / 20000) (36871908324131 / 100000) := by
  exact
    packedTile32768 368681216 368746752 13 3302 19201 28 _ _ (1972543 / 100000) (986273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368746752 :
    ThetaLowerSegment 368746752 368812288 (36871908324131 / 100000) (18439255242899 / 50000) := by
  exact
    packedTile32768 368746752 368812288 13 3347 19202 28 _ _ (1972561 / 100000) (493141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368812288 :
    ThetaLowerSegment 368812288 368877824 (18439255242899 / 50000) (2305315845439 / 6250) := by
  exact
    packedTile32768 368812288 368877824 13 3317 19204 28 _ _ (986289 / 50000) (1972581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368877824 :
    ThetaLowerSegment 368877824 368943360 (2305315845439 / 6250) (4611454756559 / 12500) := by
  exact
    packedTile32768 368877824 368943360 13 3338 19206 28 _ _ (493149 / 25000) (1972599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell368943360 :
    ThetaLowerSegment 368943360 369008896 (4611454756559 / 12500) (368981516239 / 1000) := by
  exact
    packedTile32768 368943360 369008896 13 3302 19207 28 _ _ (986307 / 50000) (1972617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369008896 :
    ThetaLowerSegment 369008896 369074432 (368981516239 / 1000) (9226162368427 / 25000) := by
  exact
    packedTile32768 369008896 369074432 13 3294 19209 28 _ _ (246579 / 12500) (394527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369074432 :
    ThetaLowerSegment 369074432 369139968 (9226162368427 / 25000) (36911137516269 / 100000) := by
  exact
    packedTile32768 369074432 369139968 13 3289 19211 28 _ _ (1972649 / 100000) (493163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369139968 :
    ThetaLowerSegment 369139968 369205504 (36911137516269 / 100000) (922941824051 / 2500) := by
  exact
    packedTile32768 369139968 369205504 13 3313 19213 28 _ _ (1972667 / 100000) (197267 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369205504 :
    ThetaLowerSegment 369205504 369271040 (922941824051 / 2500) (3692428145679 / 10000) := by
  exact
    packedTile32768 369205504 369271040 13 3350 19214 28 _ _ (394537 / 20000) (123293 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369271040 :
    ThetaLowerSegment 369271040 369336576 (3692428145679 / 10000) (7386148411823 / 20000) := by
  exact
    packedTile32768 369271040 369336576 13 3275 19216 28 _ _ (1972703 / 100000) (986353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369336576 :
    ThetaLowerSegment 369336576 369402112 (7386148411823 / 20000) (7387437387071 / 20000) := by
  exact
    packedTile32768 369336576 369402112 13 3267 19218 28 _ _ (24659 / 1250) (1972723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369402112 :
    ThetaLowerSegment 369402112 369467648 (7387437387071 / 20000) (36943839007891 / 100000) := by
  exact
    packedTile32768 369402112 369467648 13 3372 19219 28 _ _ (986369 / 50000) (1972741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369467648 :
    ThetaLowerSegment 369467648 369533184 (36943839007891 / 100000) (36950483250099 / 100000) := by
  exact
    packedTile32768 369467648 369533184 13 3368 19221 28 _ _ (493189 / 25000) (1972759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369533184 :
    ThetaLowerSegment 369533184 369598720 (36950483250099 / 100000) (36957022995909 / 100000) := by
  exact
    packedTile32768 369533184 369598720 13 3315 19223 28 _ _ (986387 / 50000) (1972777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369598720 :
    ThetaLowerSegment 369598720 369664256 (36957022995909 / 100000) (36963399056421 / 100000) := by
  exact
    packedTile32768 369598720 369664256 13 3232 19224 28 _ _ (1972791 / 100000) (986397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369664256 :
    ThetaLowerSegment 369664256 369729792 (36963399056421 / 100000) (18484987214409 / 50000) := by
  exact
    packedTile32768 369664256 369729792 13 3333 19226 28 _ _ (1972809 / 100000) (493203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369729792 :
    ThetaLowerSegment 369729792 369795328 (18484987214409 / 50000) (36976553806863 / 100000) := by
  exact
    packedTile32768 369729792 369795328 13 3335 19228 28 _ _ (1972827 / 100000) (197283 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369795328 :
    ThetaLowerSegment 369795328 369860864 (36976553806863 / 100000) (9245800080417 / 25000) := by
  exact
    packedTile32768 369795328 369860864 13 3369 19230 28 _ _ (394569 / 20000) (123303 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369860864 :
    ThetaLowerSegment 369860864 369926400 (9245800080417 / 25000) (1849491062327 / 5000) := by
  exact
    packedTile32768 369860864 369926400 13 3356 19231 28 _ _ (986431 / 50000) (394573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369926400 :
    ThetaLowerSegment 369926400 369991936 (1849491062327 / 5000) (1849819448203 / 5000) := by
  exact
    packedTile32768 369926400 369991936 13 3329 19233 28 _ _ (24661 / 1250) (1972883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell369991936 :
    ThetaLowerSegment 369991936 370057472 (1849819448203 / 5000) (2312681960303 / 6250) := by
  exact
    packedTile32768 369991936 370057472 13 3306 19235 28 _ _ (986449 / 50000) (1972901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370057472 :
    ThetaLowerSegment 370057472 370123008 (2312681960303 / 6250) (37009333203173 / 100000) := by
  exact
    packedTile32768 370057472 370123008 13 3255 19236 28 _ _ (394583 / 20000) (986459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370123008 :
    ThetaLowerSegment 370123008 370188544 (37009333203173 / 100000) (925400980061 / 2500) := by
  exact
    packedTile32768 370123008 370188544 13 3399 19238 28 _ _ (1972933 / 100000) (246617 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370188544 :
    ThetaLowerSegment 370188544 370254080 (925400980061 / 2500) (1851127497037 / 5000) := by
  exact
    packedTile32768 370188544 370254080 13 3300 19240 28 _ _ (1972951 / 100000) (986477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370254080 :
    ThetaLowerSegment 370254080 370319616 (1851127497037 / 5000) (18514524450313 / 50000) := by
  exact
    packedTile32768 370254080 370319616 13 3294 19241 28 _ _ (1972969 / 100000) (493243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370319616 :
    ThetaLowerSegment 370319616 370385152 (18514524450313 / 50000) (231472236134 / 625) := by
  exact
    packedTile32768 370319616 370385152 13 3299 19243 28 _ _ (986493 / 50000) (1972989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370385152 :
    ThetaLowerSegment 370385152 370450688 (231472236134 / 625) (2315128306913 / 6250) := by
  exact
    packedTile32768 370385152 370450688 13 3292 19245 28 _ _ (493251 / 25000) (1973007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370450688 :
    ThetaLowerSegment 370450688 370516224 (2315128306913 / 6250) (9262157741489 / 25000) := by
  exact
    packedTile32768 370450688 370516224 13 3334 19247 28 _ _ (986511 / 50000) (78921 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370516224 :
    ThetaLowerSegment 370516224 370581760 (9262157741489 / 25000) (2315944401627 / 6250) := by
  exact
    packedTile32768 370516224 370581760 13 3284 19248 28 _ _ (1973039 / 100000) (986521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370581760 :
    ThetaLowerSegment 370581760 370647296 (2315944401627 / 6250) (18530860083491 / 50000) := by
  exact
    packedTile32768 370581760 370647296 13 3350 19250 28 _ _ (1973057 / 100000) (98653 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370647296 :
    ThetaLowerSegment 370647296 370712832 (18530860083491 / 50000) (18534080141891 / 50000) := by
  exact
    packedTile32768 370647296 370712832 13 3264 19252 28 _ _ (78923 / 4000) (986539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370712832 :
    ThetaLowerSegment 370712832 370745600 (18534080141891 / 50000) (741427489013 / 2000) := by
  exact
    packedTile32768 370712832 370745600 12 1629 19253 28 _ _ (493273 / 25000) (394619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370745600 :
    ThetaLowerSegment 370745600 370778368 (741427489013 / 2000) (37074663610017 / 100000) := by
  exact
    packedTile32768 370745600 370778368 12 1667 19254 28 _ _ (1973101 / 100000) (123319 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370778368 :
    ThetaLowerSegment 370778368 370811136 (37074663610017 / 100000) (37077921214627 / 100000) := by
  exact
    packedTile32768 370778368 370811136 12 1651 19255 28 _ _ (197311 / 10000) (1973113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370811136 :
    ThetaLowerSegment 370811136 370843904 (37077921214627 / 100000) (7416236161443 / 20000) := by
  exact
    packedTile32768 370811136 370843904 12 1652 19256 28 _ _ (1973119 / 100000) (986561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370843904 :
    ThetaLowerSegment 370843904 370876672 (7416236161443 / 20000) (37084424629647 / 100000) := by
  exact
    packedTile32768 370843904 370876672 12 1644 19257 28 _ _ (246641 / 12500) (1973131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370876672 :
    ThetaLowerSegment 370876672 370909440 (37084424629647 / 100000) (18543845085691 / 50000) := by
  exact
    packedTile32768 370876672 370909440 12 1655 19258 28 _ _ (1973137 / 100000) (98657 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370909440 :
    ThetaLowerSegment 370909440 370942208 (18543845085691 / 50000) (18545494634911 / 50000) := by
  exact
    packedTile32768 370909440 370942208 12 1672 19259 28 _ _ (394629 / 20000) (493287 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370942208 :
    ThetaLowerSegment 370942208 370974976 (18545494634911 / 50000) (18547108674883 / 50000) := by
  exact
    packedTile32768 370942208 370974976 12 1636 19259 28 _ _ (986577 / 50000) (1973157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell370974976 :
    ThetaLowerSegment 370974976 371007744 (18547108674883 / 50000) (18548750346499 / 50000) := by
  exact
    packedTile32768 370974976 371007744 12 1664 19260 28 _ _ (1973163 / 100000) (986583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371007744 :
    ThetaLowerSegment 371007744 371040512 (18548750346499 / 50000) (18550383146329 / 50000) := by
  exact
    packedTile32768 371007744 371040512 12 1655 19261 28 _ _ (493293 / 25000) (78927 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371040512 :
    ThetaLowerSegment 371040512 371073280 (18550383146329 / 50000) (7420819009801 / 20000) := by
  exact
    packedTile32768 371040512 371073280 12 1687 19262 28 _ _ (1973181 / 100000) (61662 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371073280 :
    ThetaLowerSegment 371073280 371106048 (7420819009801 / 20000) (7421479633813 / 20000) := by
  exact
    packedTile32768 371073280 371106048 12 1674 19263 28 _ _ (197319 / 10000) (1973193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371106048 :
    ThetaLowerSegment 371106048 371138816 (7421479633813 / 20000) (37110697356121 / 100000) := by
  exact
    packedTile32768 371106048 371138816 12 1672 19264 28 _ _ (986599 / 50000) (1973201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371138816 :
    ThetaLowerSegment 371138816 371171584 (37110697356121 / 100000) (9278497659651 / 25000) := by
  exact
    packedTile32768 371138816 371171584 12 1669 19264 28 _ _ (1973207 / 100000) (197321 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371171584 :
    ThetaLowerSegment 371171584 371204352 (9278497659651 / 25000) (9279307664819 / 25000) := by
  exact
    packedTile32768 371171584 371204352 12 1642 19265 28 _ _ (61663 / 3125) (1973219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371204352 :
    ThetaLowerSegment 371204352 371237120 (9279307664819 / 25000) (18560270865413 / 50000) := by
  exact
    packedTile32768 371204352 371237120 12 1678 19266 28 _ _ (78929 / 4000) (493307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371237120 :
    ThetaLowerSegment 371237120 371269888 (18560270865413 / 50000) (18561928381973 / 50000) := by
  exact
    packedTile32768 371237120 371269888 12 1680 19267 28 _ _ (986617 / 50000) (1973237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371269888 :
    ThetaLowerSegment 371269888 371302656 (18561928381973 / 50000) (18563514868541 / 50000) := by
  exact
    packedTile32768 371269888 371302656 12 1608 19268 28 _ _ (986621 / 50000) (394649 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371302656 :
    ThetaLowerSegment 371302656 371335424 (18563514868541 / 50000) (37130386237033 / 100000) := by
  exact
    packedTile32768 371302656 371335424 12 1701 19269 28 _ _ (1973251 / 100000) (986627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371335424 :
    ThetaLowerSegment 371335424 371368192 (37130386237033 / 100000) (37133648035813 / 100000) := by
  exact
    packedTile32768 371335424 371368192 12 1653 19270 28 _ _ (98663 / 5000) (1973263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371368192 :
    ThetaLowerSegment 371368192 371400960 (37133648035813 / 100000) (1160526089539 / 3125) := by
  exact
    packedTile32768 371368192 371400960 12 1615 19270 28 _ _ (1973269 / 100000) (246659 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371400960 :
    ThetaLowerSegment 371400960 371433728 (1160526089539 / 3125) (3714018746457 / 10000) := by
  exact
    packedTile32768 371400960 371433728 12 1699 19271 28 _ _ (986639 / 50000) (1973281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371433728 :
    ThetaLowerSegment 371433728 371466496 (3714018746457 / 10000) (18571719720773 / 50000) := by
  exact
    packedTile32768 371433728 371466496 12 1648 19272 28 _ _ (1973287 / 100000) (197329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371466496 :
    ThetaLowerSegment 371466496 371499264 (18571719720773 / 50000) (37146776283391 / 100000) := by
  exact
    packedTile32768 371466496 371499264 12 1691 19273 28 _ _ (394659 / 20000) (986649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371499264 :
    ThetaLowerSegment 371499264 371532032 (37146776283391 / 100000) (37149992768911 / 100000) := by
  exact
    packedTile32768 371499264 371532032 12 1630 19274 28 _ _ (246663 / 12500) (1973307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371532032 :
    ThetaLowerSegment 371532032 371564800 (37149992768911 / 100000) (37153276361743 / 100000) := by
  exact
    packedTile32768 371532032 371564800 12 1664 19275 28 _ _ (1973313 / 100000) (493329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371564800 :
    ThetaLowerSegment 371564800 371597568 (37153276361743 / 100000) (37156488929959 / 100000) := by
  exact
    packedTile32768 371564800 371597568 12 1628 19276 28 _ _ (986661 / 50000) (78933 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371597568 :
    ThetaLowerSegment 371597568 371630336 (37156488929959 / 100000) (7431951353219 / 20000) := by
  exact
    packedTile32768 371597568 371630336 12 1656 19276 28 _ _ (1973331 / 100000) (986667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371630336 :
    ThetaLowerSegment 371630336 371663104 (7431951353219 / 20000) (7432608870107 / 20000) := by
  exact
    packedTile32768 371630336 371663104 12 1666 19277 28 _ _ (98667 / 5000) (1973343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371663104 :
    ThetaLowerSegment 371663104 371695872 (7432608870107 / 20000) (37166254987731 / 100000) := by
  exact
    packedTile32768 371663104 371695872 12 1627 19278 28 _ _ (493337 / 25000) (1973351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371695872 :
    ThetaLowerSegment 371695872 371728640 (37166254987731 / 100000) (2323094315839 / 6250) := by
  exact
    packedTile32768 371695872 371728640 12 1649 19279 28 _ _ (1973357 / 100000) (24667 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371728640 :
    ThetaLowerSegment 371728640 371761408 (2323094315839 / 6250) (18586460501619 / 50000) := by
  exact
    packedTile32768 371728640 371761408 12 1729 19280 28 _ _ (986683 / 50000) (1973369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371761408 :
    ThetaLowerSegment 371761408 371794176 (18586460501619 / 50000) (37176250086863 / 100000) := by
  exact
    packedTile32768 371761408 371794176 12 1687 19281 28 _ _ (15787 / 800) (986689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371794176 :
    ThetaLowerSegment 371794176 371826944 (37176250086863 / 100000) (37179547611527 / 100000) := by
  exact
    packedTile32768 371794176 371826944 12 1671 19281 28 _ _ (246673 / 12500) (1973387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371826944 :
    ThetaLowerSegment 371826944 371859712 (37179547611527 / 100000) (37182837255991 / 100000) := by
  exact
    packedTile32768 371826944 371859712 12 1667 19282 28 _ _ (123337 / 6250) (394679 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371859712 :
    ThetaLowerSegment 371859712 371892480 (37182837255991 / 100000) (18593063457729 / 50000) := by
  exact
    packedTile32768 371859712 371892480 12 1667 19283 28 _ _ (1973401 / 100000) (493351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371892480 :
    ThetaLowerSegment 371892480 371925248 (18593063457729 / 50000) (18594697441209 / 50000) := by
  exact
    packedTile32768 371892480 371925248 12 1656 19284 28 _ _ (197341 / 10000) (1973413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371925248 :
    ThetaLowerSegment 371925248 371958016 (18594697441209 / 50000) (929818643697 / 2500) := by
  exact
    packedTile32768 371925248 371958016 12 1698 19285 28 _ _ (1973419 / 100000) (986711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell371958016 :
    ThetaLowerSegment 371958016 372023552 (929818643697 / 2500) (232494992859 / 625) := by
  exact
    packedTile32768 371958016 372023552 13 3270 19286 28 _ _ (493357 / 25000) (1973431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372023552 :
    ThetaLowerSegment 372023552 372056320 (232494992859 / 625) (3720250240437 / 10000) := by
  exact
    packedTile32768 372023552 372056320 12 1674 19287 28 _ _ (394689 / 20000) (246681 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372056320 :
    ThetaLowerSegment 372056320 372089088 (3720250240437 / 10000) (18602845753017 / 50000) := by
  exact
    packedTile32768 372056320 372089088 12 1616 19288 28 _ _ (986727 / 50000) (1973457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372089088 :
    ThetaLowerSegment 372089088 372121856 (18602845753017 / 50000) (1860452517003 / 5000) := by
  exact
    packedTile32768 372089088 372121856 12 1702 19289 28 _ _ (1973463 / 100000) (986733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372121856 :
    ThetaLowerSegment 372121856 372154624 (1860452517003 / 5000) (9303080095791 / 25000) := by
  exact
    packedTile32768 372121856 372154624 12 1657 19290 28 _ _ (61671 / 3125) (78939 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372154624 :
    ThetaLowerSegment 372154624 372187392 (9303080095791 / 25000) (9303910930871 / 25000) := by
  exact
    packedTile32768 372154624 372187392 12 1684 19291 28 _ _ (49337 / 2500) (1973483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372187392 :
    ThetaLowerSegment 372187392 372220160 (9303910930871 / 25000) (18609457884123 / 50000) := by
  exact
    packedTile32768 372187392 372220160 12 1658 19292 28 _ _ (1973489 / 100000) (493373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372220160 :
    ThetaLowerSegment 372220160 372252928 (18609457884123 / 50000) (18611068258491 / 50000) := by
  exact
    packedTile32768 372220160 372252928 12 1632 19293 28 _ _ (986749 / 50000) (1973501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372252928 :
    ThetaLowerSegment 372252928 372285696 (18611068258491 / 50000) (3722549937291 / 10000) := by
  exact
    packedTile32768 372252928 372285696 12 1704 19293 28 _ _ (1973507 / 100000) (197351 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372285696 :
    ThetaLowerSegment 372285696 372351232 (3722549937291 / 10000) (18616029670047 / 50000) := by
  exact
    packedTile32768 372285696 372351232 13 3324 19294 28 _ _ (493379 / 25000) (1973519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372351232 :
    ThetaLowerSegment 372351232 372416768 (18616029670047 / 50000) (7447705321547 / 20000) := by
  exact
    packedTile32768 372351232 372416768 13 3277 19296 28 _ _ (1973533 / 100000) (61673 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372416768 :
    ThetaLowerSegment 372416768 372449536 (7447705321547 / 20000) (18620929967687 / 50000) := by
  exact
    packedTile32768 372416768 372449536 12 1689 19298 28 _ _ (1973551 / 100000) (986777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372449536 :
    ThetaLowerSegment 372449536 372515072 (18620929967687 / 50000) (18624139963027 / 50000) := by
  exact
    packedTile32768 372449536 372515072 13 3253 19298 28 _ _ (49339 / 2500) (1973563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372515072 :
    ThetaLowerSegment 372515072 372547840 (18624139963027 / 50000) (9312886055603 / 25000) := by
  exact
    packedTile32768 372515072 372547840 12 1654 19300 28 _ _ (1973577 / 100000) (98679 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372547840 :
    ThetaLowerSegment 372547840 372580608 (9312886055603 / 25000) (4656845145949 / 12500) := by
  exact
    packedTile32768 372547840 372580608 12 1630 19301 28 _ _ (986793 / 50000) (1973589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372580608 :
    ThetaLowerSegment 372580608 372613376 (4656845145949 / 12500) (9314509333823 / 25000) := by
  exact
    packedTile32768 372580608 372613376 12 1660 19302 28 _ _ (394719 / 20000) (986799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372613376 :
    ThetaLowerSegment 372613376 372646144 (9314509333823 / 25000) (2328831231419 / 6250) := by
  exact
    packedTile32768 372613376 372646144 12 1653 19303 28 _ _ (493401 / 25000) (1973607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372646144 :
    ThetaLowerSegment 372646144 372678912 (2328831231419 / 6250) (4658074454343 / 12500) := by
  exact
    packedTile32768 372646144 372678912 12 1670 19304 28 _ _ (493403 / 25000) (394723 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372678912 :
    ThetaLowerSegment 372678912 372711680 (4658074454343 / 12500) (37267850135773 / 100000) := by
  exact
    packedTile32768 372678912 372711680 12 1649 19304 28 _ _ (1973621 / 100000) (246703 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372711680 :
    ThetaLowerSegment 372711680 372744448 (37267850135773 / 100000) (37271086888973 / 100000) := by
  exact
    packedTile32768 372711680 372744448 12 1640 19305 28 _ _ (197363 / 10000) (1973633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372744448 :
    ThetaLowerSegment 372744448 372777216 (37271086888973 / 100000) (37274414444327 / 100000) := by
  exact
    packedTile32768 372744448 372777216 12 1686 19306 28 _ _ (1973639 / 100000) (986821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372777216 :
    ThetaLowerSegment 372777216 372809984 (37274414444327 / 100000) (37277668989879 / 100000) := by
  exact
    packedTile32768 372777216 372809984 12 1649 19307 28 _ _ (123353 / 6250) (1973651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372809984 :
    ThetaLowerSegment 372809984 372842752 (37277668989879 / 100000) (11929890483 / 32) := by
  exact
    packedTile32768 372809984 372842752 12 1641 19308 28 _ _ (246707 / 12500) (1973659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372842752 :
    ThetaLowerSegment 372842752 372875520 (11929890483 / 32) (3728411891233 / 10000) := by
  exact
    packedTile32768 372842752 372875520 12 1627 19309 28 _ _ (394733 / 20000) (493417 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372875520 :
    ThetaLowerSegment 372875520 372908288 (3728411891233 / 10000) (3728747415813 / 10000) := by
  exact
    packedTile32768 372875520 372908288 12 1700 19309 28 _ _ (986837 / 50000) (1973677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372908288 :
    ThetaLowerSegment 372908288 372941056 (3728747415813 / 10000) (37290689287737 / 100000) := by
  exact
    packedTile32768 372908288 372941056 12 1629 19310 28 _ _ (1973683 / 100000) (986843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372941056 :
    ThetaLowerSegment 372941056 372973824 (37290689287737 / 100000) (7458812465473 / 20000) := by
  exact
    packedTile32768 372941056 372973824 12 1709 19311 28 _ _ (493423 / 25000) (394739 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell372973824 :
    ThetaLowerSegment 372973824 373006592 (7458812465473 / 20000) (7459463786473 / 20000) := by
  exact
    packedTile32768 372973824 373006592 12 1650 19312 28 _ _ (19737 / 1000) (1973703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373006592 :
    ThetaLowerSegment 373006592 373039360 (7459463786473 / 20000) (18650314421179 / 50000) := by
  exact
    packedTile32768 373006592 373039360 12 1677 19313 28 _ _ (1973709 / 100000) (123357 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373039360 :
    ThetaLowerSegment 373039360 373072128 (18650314421179 / 50000) (18651958528273 / 50000) := by
  exact
    packedTile32768 373039360 373072128 12 1666 19314 28 _ _ (986859 / 50000) (1973721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373072128 :
    ThetaLowerSegment 373072128 373104896 (18651958528273 / 50000) (746143553071 / 2000) := by
  exact
    packedTile32768 373072128 373104896 12 1652 19315 28 _ _ (1973727 / 100000) (197373 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373104896 :
    ThetaLowerSegment 373104896 373137664 (746143553071 / 2000) (18655184592331 / 50000) := by
  exact
    packedTile32768 373104896 373137664 12 1617 19315 28 _ _ (246717 / 12500) (1973739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373137664 :
    ThetaLowerSegment 373137664 373170432 (18655184592331 / 50000) (18656840563547 / 50000) := by
  exact
    packedTile32768 373137664 373170432 12 1678 19316 28 _ _ (123359 / 6250) (1973747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373170432 :
    ThetaLowerSegment 373170432 373203200 (18656840563547 / 50000) (3731698124211 / 10000) := by
  exact
    packedTile32768 373170432 373203200 12 1672 19317 28 _ _ (1973753 / 100000) (493439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373203200 :
    ThetaLowerSegment 373203200 373235968 (3731698124211 / 10000) (1166259348001 / 3125) := by
  exact
    packedTile32768 373203200 373235968 12 1681 19318 28 _ _ (986881 / 50000) (394753 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373235968 :
    ThetaLowerSegment 373235968 373268736 (1166259348001 / 3125) (37323514408991 / 100000) := by
  exact
    packedTile32768 373235968 373268736 12 1629 19319 28 _ _ (1973771 / 100000) (986887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373268736 :
    ThetaLowerSegment 373268736 373301504 (37323514408991 / 100000) (37326747458993 / 100000) := by
  exact
    packedTile32768 373268736 373301504 12 1638 19320 28 _ _ (1973779 / 100000) (986891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373301504 :
    ThetaLowerSegment 373301504 373334272 (37326747458993 / 100000) (7466014263597 / 20000) := by
  exact
    packedTile32768 373301504 373334272 12 1684 19321 28 _ _ (493447 / 25000) (1973791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373334272 :
    ThetaLowerSegment 373334272 373367040 (7466014263597 / 20000) (18666714373341 / 50000) := by
  exact
    packedTile32768 373334272 373367040 12 1701 19321 28 _ _ (1973797 / 100000) (9869 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373367040 :
    ThetaLowerSegment 373367040 373399808 (18666714373341 / 50000) (18668366448963 / 50000) := by
  exact
    packedTile32768 373367040 373399808 12 1674 19322 28 _ _ (986903 / 50000) (1973809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373399808 :
    ThetaLowerSegment 373399808 373432576 (18668366448963 / 50000) (37339971928341 / 100000) := by
  exact
    packedTile32768 373399808 373432576 12 1641 19323 28 _ _ (394763 / 20000) (986909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373432576 :
    ThetaLowerSegment 373432576 373465344 (37339971928341 / 100000) (37343272160397 / 100000) := by
  exact
    packedTile32768 373432576 373465344 12 1672 19324 28 _ _ (1973823 / 100000) (986913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373465344 :
    ThetaLowerSegment 373465344 373498112 (37343272160397 / 100000) (37346513192541 / 100000) := by
  exact
    packedTile32768 373465344 373498112 12 1642 19325 28 _ _ (246729 / 12500) (394767 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373498112 :
    ThetaLowerSegment 373498112 373530880 (37346513192541 / 100000) (18674927452677 / 50000) := by
  exact
    packedTile32768 373498112 373530880 12 1693 19326 28 _ _ (1973841 / 100000) (493461 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373530880 :
    ThetaLowerSegment 373530880 373563648 (18674927452677 / 50000) (9338285341401 / 25000) := by
  exact
    packedTile32768 373530880 373563648 12 1665 19326 28 _ _ (39477 / 2000) (1973853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373563648 :
    ThetaLowerSegment 373563648 373596416 (9338285341401 / 25000) (4669549778913 / 12500) := by
  exact
    packedTile32768 373563648 373596416 12 1650 19327 28 _ _ (986929 / 50000) (1973861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373596416 :
    ThetaLowerSegment 373596416 373629184 (4669549778913 / 12500) (37359633399317 / 100000) := by
  exact
    packedTile32768 373596416 373629184 12 1639 19328 28 _ _ (1973867 / 100000) (197387 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373629184 :
    ThetaLowerSegment 373629184 373661952 (37359633399317 / 100000) (37362981093013 / 100000) := by
  exact
    packedTile32768 373629184 373661952 12 1696 19329 28 _ _ (493469 / 25000) (1973879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373661952 :
    ThetaLowerSegment 373661952 373694720 (37362981093013 / 100000) (18683137753539 / 50000) := by
  exact
    packedTile32768 373661952 373694720 12 1669 19330 28 _ _ (394777 / 20000) (61684 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373694720 :
    ThetaLowerSegment 373694720 373727488 (18683137753539 / 50000) (37369605464569 / 100000) := by
  exact
    packedTile32768 373694720 373727488 12 1687 19331 28 _ _ (1973893 / 100000) (246737 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373727488 :
    ThetaLowerSegment 373727488 373760256 (37369605464569 / 100000) (298983341377 / 800) := by
  exact
    packedTile32768 373727488 373760256 12 1678 19332 28 _ _ (986951 / 50000) (394781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373760256 :
    ThetaLowerSegment 373760256 373825792 (298983341377 / 800) (18689702958791 / 50000) := by
  exact
    packedTile32768 373760256 373825792 13 3287 19332 28 _ _ (1973911 / 100000) (986957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373825792 :
    ThetaLowerSegment 373825792 373858560 (18689702958791 / 50000) (7476511656439 / 20000) := by
  exact
    packedTile32768 373825792 373858560 12 1597 19334 28 _ _ (1973929 / 100000) (493483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373858560 :
    ThetaLowerSegment 373858560 373891328 (7476511656439 / 20000) (37385728425017 / 100000) := by
  exact
    packedTile32768 373858560 373891328 12 1606 19335 28 _ _ (1973937 / 100000) (98697 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373891328 :
    ThetaLowerSegment 373891328 373924096 (37385728425017 / 100000) (37389018992999 / 100000) := by
  exact
    packedTile32768 373891328 373924096 12 1667 19336 28 _ _ (986973 / 50000) (1973949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373924096 :
    ThetaLowerSegment 373924096 373956864 (37389018992999 / 100000) (18696129126577 / 50000) := by
  exact
    packedTile32768 373924096 373956864 12 1641 19337 28 _ _ (394791 / 20000) (986979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373956864 :
    ThetaLowerSegment 373956864 373989632 (18696129126577 / 50000) (3739551331979 / 10000) := by
  exact
    packedTile32768 373956864 373989632 12 1649 19337 28 _ _ (493491 / 25000) (1973967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell373989632 :
    ThetaLowerSegment 373989632 374022400 (3739551331979 / 10000) (18699391108711 / 50000) := by
  exact
    packedTile32768 373989632 374022400 12 1656 19338 28 _ _ (493493 / 25000) (78959 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374022400 :
    ThetaLowerSegment 374022400 374055168 (18699391108711 / 50000) (37402132063179 / 100000) := by
  exact
    packedTile32768 374022400 374055168 12 1697 19339 28 _ _ (1973981 / 100000) (61687 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374055168 :
    ThetaLowerSegment 374055168 374087936 (37402132063179 / 100000) (37405351640869 / 100000) := by
  exact
    packedTile32768 374055168 374087936 12 1631 19340 28 _ _ (197399 / 10000) (1973993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374087936 :
    ThetaLowerSegment 374087936 374120704 (37405351640869 / 100000) (9352175379293 / 25000) := by
  exact
    packedTile32768 374087936 374120704 12 1697 19341 28 _ _ (1973999 / 100000) (987001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374120704 :
    ThetaLowerSegment 374120704 374153472 (9352175379293 / 25000) (37412031666981 / 100000) := by
  exact
    packedTile32768 374120704 374153472 12 1687 19342 28 _ _ (1974007 / 100000) (197401 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374153472 :
    ThetaLowerSegment 374153472 374186240 (37412031666981 / 100000) (37415304585509 / 100000) := by
  exact
    packedTile32768 374153472 374186240 12 1658 19343 28 _ _ (61688 / 3125) (1974019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374186240 :
    ThetaLowerSegment 374186240 374219008 (37415304585509 / 100000) (18709307512717 / 50000) := by
  exact
    packedTile32768 374186240 374219008 12 1677 19343 28 _ _ (78961 / 4000) (493507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374219008 :
    ThetaLowerSegment 374219008 374251776 (18709307512717 / 50000) (18710912402359 / 50000) := by
  exact
    packedTile32768 374219008 374251776 12 1626 19344 28 _ _ (987017 / 50000) (1974037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374251776 :
    ThetaLowerSegment 374251776 374284544 (18710912402359 / 50000) (9356288753393 / 25000) := by
  exact
    packedTile32768 374251776 374284544 12 1687 19345 28 _ _ (987021 / 50000) (394809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374284544 :
    ThetaLowerSegment 374284544 374317312 (9356288753393 / 25000) (37428489185711 / 100000) := by
  exact
    packedTile32768 374284544 374317312 12 1689 19346 28 _ _ (1974051 / 100000) (987027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374317312 :
    ThetaLowerSegment 374317312 374350080 (37428489185711 / 100000) (37431730592231 / 100000) := by
  exact
    packedTile32768 374317312 374350080 12 1642 19347 28 _ _ (98703 / 5000) (1974063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374350080 :
    ThetaLowerSegment 374350080 374382848 (37431730592231 / 100000) (37435062820703 / 100000) := by
  exact
    packedTile32768 374350080 374382848 12 1688 19348 28 _ _ (1974069 / 100000) (246759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374382848 :
    ThetaLowerSegment 374382848 374415616 (37435062820703 / 100000) (748768809329 / 2000) := by
  exact
    packedTile32768 374382848 374415616 12 1711 19348 28 _ _ (1974077 / 100000) (12338 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374415616 :
    ThetaLowerSegment 374415616 374448384 (748768809329 / 2000) (2340102528741 / 6250) := by
  exact
    packedTile32768 374415616 374448384 12 1621 19349 28 _ _ (987043 / 50000) (1974089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374448384 :
    ThetaLowerSegment 374448384 374481152 (2340102528741 / 6250) (37444998395451 / 100000) := by
  exact
    packedTile32768 374448384 374481152 12 1701 19350 28 _ _ (394819 / 20000) (987049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374481152 :
    ThetaLowerSegment 374481152 374546688 (37444998395451 / 100000) (7490322723591 / 20000) := by
  exact
    packedTile32768 374481152 374546688 13 3351 19351 28 _ _ (246763 / 12500) (1974107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374546688 :
    ThetaLowerSegment 374546688 374612224 (7490322723591 / 20000) (37458262457483 / 100000) := by
  exact
    packedTile32768 374546688 374612224 13 3368 19353 28 _ _ (1974121 / 100000) (493531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374612224 :
    ThetaLowerSegment 374612224 374677760 (37458262457483 / 100000) (18732369803771 / 50000) := by
  exact
    packedTile32768 374612224 374677760 13 3281 19354 28 _ _ (1974139 / 100000) (987071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374677760 :
    ThetaLowerSegment 374677760 374743296 (18732369803771 / 50000) (18735685398773 / 50000) := by
  exact
    packedTile32768 374677760 374743296 13 3359 19356 28 _ _ (493539 / 25000) (1974159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374743296 :
    ThetaLowerSegment 374743296 374808832 (18735685398773 / 50000) (9369464976871 / 25000) := by
  exact
    packedTile32768 374743296 374808832 13 3287 19358 28 _ _ (987087 / 50000) (1974177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374808832 :
    ThetaLowerSegment 374808832 374874368 (9369464976871 / 25000) (18742248568813 / 50000) := by
  exact
    packedTile32768 374808832 374874368 13 3362 19359 28 _ _ (1974191 / 100000) (987097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374874368 :
    ThetaLowerSegment 374874368 374939904 (18742248568813 / 50000) (7498214645561 / 20000) := by
  exact
    packedTile32768 374874368 374939904 13 3331 19361 28 _ _ (1974209 / 100000) (493553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell374939904 :
    ThetaLowerSegment 374939904 375005440 (7498214645561 / 20000) (37497710575617 / 100000) := by
  exact
    packedTile32768 374939904 375005440 13 3362 19363 28 _ _ (987113 / 50000) (1974229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375005440 :
    ThetaLowerSegment 375005440 375070976 (37497710575617 / 100000) (7500883416497 / 20000) := by
  exact
    packedTile32768 375005440 375070976 13 3397 19365 28 _ _ (493561 / 25000) (1974247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375070976 :
    ThetaLowerSegment 375070976 375136512 (7500883416497 / 20000) (3751098150031 / 10000) := by
  exact
    packedTile32768 375070976 375136512 13 3325 19366 28 _ _ (1974261 / 100000) (246783 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375136512 :
    ThetaLowerSegment 375136512 375202048 (3751098150031 / 10000) (18758752259063 / 50000) := by
  exact
    packedTile32768 375136512 375202048 13 3304 19368 28 _ _ (1974279 / 100000) (987141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375202048 :
    ThetaLowerSegment 375202048 375267584 (18758752259063 / 50000) (18762049333383 / 50000) := by
  exact
    packedTile32768 375202048 375267584 13 3340 19370 28 _ _ (246787 / 12500) (1974299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375267584 :
    ThetaLowerSegment 375267584 375333120 (18762049333383 / 50000) (1501224003179 / 4000) := by
  exact
    packedTile32768 375267584 375333120 13 3293 19371 28 _ _ (1974313 / 100000) (493579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375333120 :
    ThetaLowerSegment 375333120 375398656 (1501224003179 / 4000) (37537099577127 / 100000) := by
  exact
    packedTile32768 375333120 375398656 13 3292 19373 28 _ _ (1974331 / 100000) (987167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375398656 :
    ThetaLowerSegment 375398656 375464192 (37537099577127 / 100000) (37543650463791 / 100000) := by
  exact
    packedTile32768 375398656 375464192 13 3318 19375 28 _ _ (493587 / 25000) (1974351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375464192 :
    ThetaLowerSegment 375464192 375529728 (37543650463791 / 100000) (37550229051303 / 100000) := by
  exact
    packedTile32768 375464192 375529728 13 3332 19376 28 _ _ (987183 / 50000) (1974369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375529728 :
    ThetaLowerSegment 375529728 375595264 (37550229051303 / 100000) (9389193532737 / 25000) := by
  exact
    packedTile32768 375529728 375595264 13 3315 19378 28 _ _ (1974383 / 100000) (987193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375595264 :
    ThetaLowerSegment 375595264 375660800 (9389193532737 / 25000) (9390824387963 / 25000) := by
  exact
    packedTile32768 375595264 375660800 13 3304 19380 28 _ _ (1974401 / 100000) (493601 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375660800 :
    ThetaLowerSegment 375660800 375726336 (9390824387963 / 25000) (4696225160593 / 12500) := by
  exact
    packedTile32768 375660800 375726336 13 3294 19381 28 _ _ (987209 / 50000) (1974421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375726336 :
    ThetaLowerSegment 375726336 375791872 (4696225160593 / 12500) (187882532347 / 500) := by
  exact
    packedTile32768 375726336 375791872 13 3396 19383 28 _ _ (493609 / 25000) (1974439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375791872 :
    ThetaLowerSegment 375791872 375857408 (187882532347 / 500) (37583035985471 / 100000) := by
  exact
    packedTile32768 375791872 375857408 13 3307 19385 28 _ _ (1974453 / 100000) (246807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375857408 :
    ThetaLowerSegment 375857408 375922944 (37583035985471 / 100000) (4698696682369 / 12500) := by
  exact
    packedTile32768 375857408 375922944 13 3311 19387 28 _ _ (1974471 / 100000) (987237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375922944 :
    ThetaLowerSegment 375922944 375988480 (4698696682369 / 12500) (1174878344992 / 3125) := by
  exact
    packedTile32768 375922944 375988480 13 3309 19388 28 _ _ (246811 / 12500) (1974491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell375988480 :
    ThetaLowerSegment 375988480 376054016 (1174878344992 / 3125) (18801348968717 / 50000) := by
  exact
    packedTile32768 375988480 376054016 13 3338 19390 28 _ _ (394901 / 20000) (493627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376054016 :
    ThetaLowerSegment 376054016 376119552 (18801348968717 / 50000) (37609172398351 / 100000) := by
  exact
    packedTile32768 376054016 376119552 13 3279 19392 28 _ _ (1974523 / 100000) (987263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376119552 :
    ThetaLowerSegment 376119552 376185088 (37609172398351 / 100000) (37615725896611 / 100000) := by
  exact
    packedTile32768 376119552 376185088 13 3319 19393 28 _ _ (98727 / 5000) (1974543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376185088 :
    ThetaLowerSegment 376185088 376250624 (37615725896611 / 100000) (7524455496011 / 20000) := by
  exact
    packedTile32768 376185088 376250624 13 3318 19395 28 _ _ (987279 / 50000) (1974561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376250624 :
    ThetaLowerSegment 376250624 376316160 (7524455496011 / 20000) (7525772932451 / 20000) := by
  exact
    packedTile32768 376250624 376316160 13 3336 19397 28 _ _ (78983 / 4000) (987289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376316160 :
    ThetaLowerSegment 376316160 376381696 (7525772932451 / 20000) (37635455853689 / 100000) := by
  exact
    packedTile32768 376316160 376381696 13 3338 19398 28 _ _ (1974593 / 100000) (493649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376381696 :
    ThetaLowerSegment 376381696 376447232 (37635455853689 / 100000) (37642047101869 / 100000) := by
  exact
    packedTile32768 376381696 376447232 13 3338 19400 28 _ _ (197461 / 10000) (1974613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376447232 :
    ThetaLowerSegment 376447232 376512768 (37642047101869 / 100000) (18824308342949 / 50000) := by
  exact
    packedTile32768 376447232 376512768 13 3327 19402 28 _ _ (1974627 / 100000) (197463 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376512768 :
    ThetaLowerSegment 376512768 376578304 (18824308342949 / 50000) (37655233721293 / 100000) := by
  exact
    packedTile32768 376512768 376578304 13 3351 19403 28 _ _ (394929 / 20000) (246831 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376578304 :
    ThetaLowerSegment 376578304 376643840 (37655233721293 / 100000) (7532362264083 / 20000) := by
  exact
    packedTile32768 376578304 376643840 13 3331 19405 28 _ _ (987331 / 50000) (394933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376643840 :
    ThetaLowerSegment 376643840 376709376 (7532362264083 / 20000) (1506734453359 / 4000) := by
  exact
    packedTile32768 376643840 376709376 13 3317 19407 28 _ _ (49367 / 2500) (1974683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376709376 :
    ThetaLowerSegment 376709376 376774912 (1506734453359 / 4000) (37674960771349 / 100000) := by
  exact
    packedTile32768 376709376 376774912 13 3342 19409 28 _ _ (1974697 / 100000) (19747 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376774912 :
    ThetaLowerSegment 376774912 376840448 (37674960771349 / 100000) (37681538543683 / 100000) := by
  exact
    packedTile32768 376774912 376840448 13 3331 19410 28 _ _ (987357 / 50000) (1974717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376840448 :
    ThetaLowerSegment 376840448 376905984 (37681538543683 / 100000) (7537609452071 / 20000) := by
  exact
    packedTile32768 376840448 376905984 13 3296 19412 28 _ _ (493683 / 25000) (394947 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376905984 :
    ThetaLowerSegment 376905984 376971520 (7537609452071 / 20000) (9423677022183 / 25000) := by
  exact
    packedTile32768 376905984 376971520 13 3373 19414 28 _ _ (1974749 / 100000) (61711 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell376971520 :
    ThetaLowerSegment 376971520 377037056 (9423677022183 / 25000) (37701155702987 / 100000) := by
  exact
    packedTile32768 376971520 377037056 13 3265 19415 28 _ _ (1974767 / 100000) (197477 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377037056 :
    ThetaLowerSegment 377037056 377102592 (37701155702987 / 100000) (7541551086223 / 20000) := by
  exact
    packedTile32768 377037056 377102592 13 3342 19417 28 _ _ (61712 / 3125) (1974787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377102592 :
    ThetaLowerSegment 377102592 377168128 (7541551086223 / 20000) (9428582385911 / 25000) := by
  exact
    packedTile32768 377102592 377168128 13 3329 19419 28 _ _ (1974801 / 100000) (493701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377168128 :
    ThetaLowerSegment 377168128 377233664 (9428582385911 / 25000) (4715105805793 / 12500) := by
  exact
    packedTile32768 377168128 377233664 13 3300 19420 28 _ _ (1974819 / 100000) (987411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377233664 :
    ThetaLowerSegment 377233664 377299200 (4715105805793 / 12500) (4715932274659 / 12500) := by
  exact
    packedTile32768 377233664 377299200 13 3348 19422 28 _ _ (493709 / 25000) (1974839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377299200 :
    ThetaLowerSegment 377299200 377364736 (4715932274659 / 12500) (37734052231439 / 100000) := by
  exact
    packedTile32768 377299200 377364736 13 3339 19424 28 _ _ (1974853 / 100000) (246857 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377364736 :
    ThetaLowerSegment 377364736 377430272 (37734052231439 / 100000) (18870313288499 / 50000) := by
  exact
    packedTile32768 377364736 377430272 13 3329 19425 28 _ _ (1974871 / 100000) (987437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377430272 :
    ThetaLowerSegment 377430272 377495808 (18870313288499 / 50000) (18873561979259 / 50000) := by
  exact
    packedTile32768 377430272 377495808 13 3290 19427 28 _ _ (246861 / 12500) (1974891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377495808 :
    ThetaLowerSegment 377495808 377561344 (18873561979259 / 50000) (235960713874 / 625) := by
  exact
    packedTile32768 377495808 377561344 13 3337 19429 28 _ _ (987453 / 50000) (1974909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377561344 :
    ThetaLowerSegment 377561344 377626880 (235960713874 / 625) (37760233440663 / 100000) := by
  exact
    packedTile32768 377561344 377626880 13 3301 19430 28 _ _ (1974923 / 100000) (987463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377626880 :
    ThetaLowerSegment 377626880 377692416 (37760233440663 / 100000) (37766841589903 / 100000) := by
  exact
    packedTile32768 377626880 377692416 13 3346 19432 28 _ _ (98747 / 5000) (1974943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377692416 :
    ThetaLowerSegment 377692416 377757952 (37766841589903 / 100000) (37773390550631 / 100000) := by
  exact
    packedTile32768 377692416 377757952 13 3316 19434 28 _ _ (987479 / 50000) (1974961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377757952 :
    ThetaLowerSegment 377757952 377823488 (37773390550631 / 100000) (37780026466631 / 100000) := by
  exact
    packedTile32768 377757952 377823488 13 3360 19435 28 _ _ (78999 / 4000) (987489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377823488 :
    ThetaLowerSegment 377823488 377889024 (37780026466631 / 100000) (37786579490087 / 100000) := by
  exact
    packedTile32768 377823488 377889024 13 3318 19437 28 _ _ (123437 / 6250) (394999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377889024 :
    ThetaLowerSegment 377889024 377954560 (37786579490087 / 100000) (37793176023487 / 100000) := by
  exact
    packedTile32768 377889024 377954560 13 3340 19439 28 _ _ (197501 / 10000) (1975013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell377954560 :
    ThetaLowerSegment 377954560 378020096 (37793176023487 / 100000) (7559967952917 / 20000) := by
  exact
    packedTile32768 377954560 378020096 13 3374 19441 28 _ _ (1975027 / 100000) (197503 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378020096 :
    ThetaLowerSegment 378020096 378085632 (7559967952917 / 20000) (37806513438261 / 100000) := by
  exact
    packedTile32768 378020096 378085632 13 3379 19442 28 _ _ (493761 / 25000) (1975047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378085632 :
    ThetaLowerSegment 378085632 378151168 (37806513438261 / 100000) (37813082494473 / 100000) := by
  exact
    packedTile32768 378085632 378151168 13 3326 19444 28 _ _ (987531 / 50000) (395013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378151168 :
    ThetaLowerSegment 378151168 378216704 (37813082494473 / 100000) (2363728595779 / 6250) := by
  exact
    packedTile32768 378151168 378216704 13 3329 19446 28 _ _ (1975079 / 100000) (987541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378216704 :
    ThetaLowerSegment 378216704 378282240 (2363728595779 / 6250) (4728262783839 / 12500) := by
  exact
    packedTile32768 378216704 378282240 13 3263 19447 28 _ _ (246887 / 12500) (1975099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378282240 :
    ThetaLowerSegment 378282240 378347776 (4728262783839 / 12500) (18916392040687 / 50000) := by
  exact
    packedTile32768 378282240 378347776 13 3383 19449 28 _ _ (987557 / 50000) (1975117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378347776 :
    ThetaLowerSegment 378347776 378413312 (18916392040687 / 50000) (18919722111553 / 50000) := by
  exact
    packedTile32768 378347776 378413312 13 3372 19451 28 _ _ (1975131 / 100000) (987567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378413312 :
    ThetaLowerSegment 378413312 378478848 (18919722111553 / 50000) (18923036409897 / 50000) := by
  exact
    packedTile32768 378413312 378478848 13 3356 19452 28 _ _ (493787 / 25000) (1975151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378478848 :
    ThetaLowerSegment 378478848 378544384 (18923036409897 / 50000) (9463131421779 / 25000) := by
  exact
    packedTile32768 378478848 378544384 13 3267 19454 28 _ _ (987583 / 50000) (1975169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378544384 :
    ThetaLowerSegment 378544384 378609920 (9463131421779 / 25000) (37858962808513 / 100000) := by
  exact
    packedTile32768 378544384 378609920 13 3259 19456 28 _ _ (1975183 / 100000) (987593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378609920 :
    ThetaLowerSegment 378609920 378675456 (37858962808513 / 100000) (37865445414913 / 100000) := by
  exact
    packedTile32768 378609920 378675456 13 3282 19457 28 _ _ (2469 / 125) (1975203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378675456 :
    ThetaLowerSegment 378675456 378740992 (37865445414913 / 100000) (37872005113891 / 100000) := by
  exact
    packedTile32768 378675456 378740992 13 3321 19459 28 _ _ (987609 / 50000) (1975221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378740992 :
    ThetaLowerSegment 378740992 378806528 (37872005113891 / 100000) (37878602398791 / 100000) := by
  exact
    packedTile32768 378740992 378806528 13 3340 19461 28 _ _ (395047 / 20000) (987619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378806528 :
    ThetaLowerSegment 378806528 378872064 (37878602398791 / 100000) (7577048639203 / 20000) := by
  exact
    packedTile32768 378806528 378872064 13 3362 19462 28 _ _ (493813 / 25000) (395051 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378872064 :
    ThetaLowerSegment 378872064 378937600 (7577048639203 / 20000) (37891737880487 / 100000) := by
  exact
    packedTile32768 378872064 378937600 13 3288 19464 28 _ _ (1975269 / 100000) (246909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell378937600 :
    ThetaLowerSegment 378937600 379003136 (37891737880487 / 100000) (37898311635623 / 100000) := by
  exact
    packedTile32768 378937600 379003136 13 3328 19466 28 _ _ (1975287 / 100000) (197529 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379003136 :
    ThetaLowerSegment 379003136 379068672 (37898311635623 / 100000) (37904877546119 / 100000) := by
  exact
    packedTile32768 379003136 379068672 13 3324 19468 28 _ _ (246913 / 12500) (1975307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379068672 :
    ThetaLowerSegment 379068672 379134208 (37904877546119 / 100000) (7582281591469 / 20000) := by
  exact
    packedTile32768 379068672 379134208 13 3306 19469 28 _ _ (1975321 / 100000) (493831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379134208 :
    ThetaLowerSegment 379134208 379199744 (7582281591469 / 20000) (9479495965219 / 25000) := by
  exact
    packedTile32768 379134208 379199744 13 3329 19471 28 _ _ (1975339 / 100000) (987671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379199744 :
    ThetaLowerSegment 379199744 379265280 (9479495965219 / 25000) (1896221571143 / 5000) := by
  exact
    packedTile32768 379199744 379265280 13 3264 19473 28 _ _ (493839 / 25000) (1975359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379265280 :
    ThetaLowerSegment 379265280 379330816 (1896221571143 / 5000) (37930987685847 / 100000) := by
  exact
    packedTile32768 379265280 379330816 13 3319 19474 28 _ _ (1975373 / 100000) (123461 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379330816 :
    ThetaLowerSegment 379330816 379396352 (37930987685847 / 100000) (37937461038877 / 100000) := by
  exact
    packedTile32768 379330816 379396352 13 3277 19476 28 _ _ (197539 / 10000) (1975393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379396352 :
    ThetaLowerSegment 379396352 379461888 (37937461038877 / 100000) (37944098409757 / 100000) := by
  exact
    packedTile32768 379396352 379461888 13 3360 19478 28 _ _ (123463 / 6250) (1975411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379461888 :
    ThetaLowerSegment 379461888 379527424 (37944098409757 / 100000) (18975317545541 / 50000) := by
  exact
    packedTile32768 379461888 379527424 13 3309 19479 28 _ _ (79017 / 4000) (493857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379527424 :
    ThetaLowerSegment 379527424 379592960 (18975317545541 / 50000) (759145214471 / 2000) := by
  exact
    packedTile32768 379527424 379592960 13 3354 19481 28 _ _ (987721 / 50000) (395089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379592960 :
    ThetaLowerSegment 379592960 379658496 (759145214471 / 2000) (3796380542253 / 10000) := by
  exact
    packedTile32768 379592960 379658496 13 3313 19483 28 _ _ (98773 / 5000) (1975463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379658496 :
    ThetaLowerSegment 379658496 379724032 (3796380542253 / 10000) (7594090580527 / 20000) := by
  exact
    packedTile32768 379658496 379724032 13 3365 19484 29 _ _ (1975477 / 100000) (49387 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379724032 :
    ThetaLowerSegment 379724032 379789568 (7594090580527 / 20000) (37977009567221 / 100000) := by
  exact
    packedTile32768 379724032 379789568 13 3319 19486 29 _ _ (987747 / 50000) (1975497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379789568 :
    ThetaLowerSegment 379789568 379855104 (37977009567221 / 100000) (37983532704543 / 100000) := by
  exact
    packedTile32768 379789568 379855104 13 3302 19488 29 _ _ (1975511 / 100000) (987757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379855104 :
    ThetaLowerSegment 379855104 379920640 (37983532704543 / 100000) (37990055901301 / 100000) := by
  exact
    packedTile32768 379855104 379920640 13 3302 19489 29 _ _ (1975529 / 100000) (493883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379920640 :
    ThetaLowerSegment 379920640 379986176 (37990055901301 / 100000) (37996628542843 / 100000) := by
  exact
    packedTile32768 379920640 379986176 13 3327 19491 29 _ _ (987773 / 50000) (1975549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell379986176 :
    ThetaLowerSegment 379986176 380051712 (37996628542843 / 100000) (7600662769607 / 20000) := by
  exact
    packedTile32768 379986176 380051712 13 3384 19493 29 _ _ (1975563 / 100000) (987783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380051712 :
    ThetaLowerSegment 380051712 380117248 (7600662769607 / 20000) (7601957169623 / 20000) := by
  exact
    packedTile32768 380051712 380117248 13 3276 19494 29 _ _ (98779 / 5000) (1975583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380117248 :
    ThetaLowerSegment 380117248 380182784 (7601957169623 / 20000) (38016358662661 / 100000) := by
  exact
    packedTile32768 380117248 380182784 13 3327 19496 29 _ _ (987799 / 50000) (1975601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380182784 :
    ThetaLowerSegment 380182784 380248320 (38016358662661 / 100000) (38022886094621 / 100000) := by
  exact
    packedTile32768 380182784 380248320 13 3304 19498 29 _ _ (395123 / 20000) (987809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380248320 :
    ThetaLowerSegment 380248320 380313856 (38022886094621 / 100000) (38029482729869 / 100000) := by
  exact
    packedTile32768 380248320 380313856 13 3339 19499 29 _ _ (123477 / 6250) (395127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380313856 :
    ThetaLowerSegment 380313856 380379392 (38029482729869 / 100000) (2377257927341 / 6250) := by
  exact
    packedTile32768 380313856 380379392 13 3363 19501 29 _ _ (1975649 / 100000) (493913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380379392 :
    ThetaLowerSegment 380379392 380444928 (2377257927341 / 6250) (9510702134967 / 25000) := by
  exact
    packedTile32768 380379392 380444928 13 3382 19503 29 _ _ (987833 / 50000) (1975669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380444928 :
    ThetaLowerSegment 380444928 380510464 (9510702134967 / 25000) (4756167765857 / 12500) := by
  exact
    packedTile32768 380444928 380510464 13 3307 19504 29 _ _ (493921 / 25000) (1975687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380510464 :
    ThetaLowerSegment 380510464 380576000 (4756167765857 / 12500) (9513969436441 / 25000) := by
  exact
    packedTile32768 380510464 380576000 13 3308 19506 29 _ _ (1975701 / 100000) (246963 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380576000 :
    ThetaLowerSegment 380576000 380641536 (9513969436441 / 25000) (3806249047391 / 10000) := by
  exact
    packedTile32768 380576000 380641536 13 3347 19508 29 _ _ (987859 / 50000) (1975721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380641536 :
    ThetaLowerSegment 380641536 380707072 (3806249047391 / 10000) (951728124801 / 2500) := by
  exact
    packedTile32768 380641536 380707072 13 3358 19510 29 _ _ (395147 / 20000) (987869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380707072 :
    ThetaLowerSegment 380707072 380772608 (951728124801 / 2500) (9518934953271 / 25000) := by
  exact
    packedTile32768 380707072 380772608 13 3348 19511 29 _ _ (1975753 / 100000) (493939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380772608 :
    ThetaLowerSegment 380772608 380838144 (9518934953271 / 25000) (19041138818007 / 50000) := by
  exact
    packedTile32768 380772608 380838144 13 3309 19513 29 _ _ (197577 / 10000) (1975773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380838144 :
    ThetaLowerSegment 380838144 380903680 (19041138818007 / 50000) (19044390963409 / 50000) := by
  exact
    packedTile32768 380838144 380903680 13 3292 19515 29 _ _ (1975787 / 100000) (197579 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380903680 :
    ThetaLowerSegment 380903680 380969216 (19044390963409 / 50000) (19047646100499 / 50000) := by
  exact
    packedTile32768 380903680 380969216 13 3295 19516 29 _ _ (493951 / 25000) (1975807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell380969216 :
    ThetaLowerSegment 380969216 381034752 (19047646100499 / 50000) (38101834144329 / 100000) := by
  exact
    packedTile32768 380969216 381034752 13 3311 19518 29 _ _ (1975821 / 100000) (123489 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381034752 :
    ThetaLowerSegment 381034752 381100288 (38101834144329 / 100000) (19054223638731 / 50000) := by
  exact
    packedTile32768 381034752 381100288 13 3347 19520 29 _ _ (1975839 / 100000) (987921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381100288 :
    ThetaLowerSegment 381100288 381165824 (19054223638731 / 50000) (19057478861491 / 50000) := by
  exact
    packedTile32768 381100288 381165824 13 3295 19521 29 _ _ (123491 / 6250) (1975859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381165824 :
    ThetaLowerSegment 381165824 381231360 (19057478861491 / 50000) (38121432658803 / 100000) := by
  exact
    packedTile32768 381165824 381231360 13 3277 19523 29 _ _ (1975873 / 100000) (493969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381231360 :
    ThetaLowerSegment 381231360 381296896 (38121432658803 / 100000) (38127974830593 / 100000) := by
  exact
    packedTile32768 381231360 381296896 13 3311 19525 29 _ _ (197589 / 10000) (1975893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381296896 :
    ThetaLowerSegment 381296896 381362432 (38127974830593 / 100000) (19067321758359 / 50000) := by
  exact
    packedTile32768 381296896 381362432 13 3375 19526 29 _ _ (1975907 / 100000) (197591 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381362432 :
    ThetaLowerSegment 381362432 381427968 (19067321758359 / 50000) (38141213467343 / 100000) := by
  exact
    packedTile32768 381362432 381427968 13 3325 19528 29 _ _ (79037 / 4000) (246991 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381427968 :
    ThetaLowerSegment 381427968 381493504 (38141213467343 / 100000) (38147694557103 / 100000) := by
  exact
    packedTile32768 381427968 381493504 13 3280 19530 29 _ _ (987971 / 50000) (395189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381493504 :
    ThetaLowerSegment 381493504 381559040 (38147694557103 / 100000) (38154262644819 / 100000) := by
  exact
    packedTile32768 381493504 381559040 13 3324 19531 29 _ _ (1975959 / 100000) (987981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381559040 :
    ThetaLowerSegment 381559040 381624576 (38154262644819 / 100000) (38160771509763 / 100000) := by
  exact
    packedTile32768 381559040 381624576 13 3294 19533 29 _ _ (246997 / 12500) (1975979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381624576 :
    ThetaLowerSegment 381624576 381690112 (38160771509763 / 100000) (7633479798057 / 20000) := by
  exact
    packedTile32768 381624576 381690112 13 3354 19535 29 _ _ (1975993 / 100000) (493999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381690112 :
    ThetaLowerSegment 381690112 381755648 (7633479798057 / 20000) (7634784755061 / 20000) := by
  exact
    packedTile32768 381690112 381755648 13 3302 19536 29 _ _ (197601 / 10000) (1976013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381755648 :
    ThetaLowerSegment 381755648 381821184 (7634784755061 / 20000) (38180551373217 / 100000) := by
  exact
    packedTile32768 381755648 381821184 13 3354 19538 29 _ _ (494007 / 25000) (1976031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381821184 :
    ThetaLowerSegment 381821184 381886720 (38180551373217 / 100000) (19093509484251 / 50000) := by
  exact
    packedTile32768 381821184 381886720 13 3273 19540 29 _ _ (395209 / 20000) (123503 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381886720 :
    ThetaLowerSegment 381886720 381952256 (19093509484251 / 50000) (477419224963 / 1250) := by
  exact
    packedTile32768 381886720 381952256 13 3299 19541 29 _ _ (988031 / 50000) (395213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell381952256 :
    ThetaLowerSegment 381952256 382017792 (477419224963 / 1250) (4775004418099 / 12500) := by
  exact
    packedTile32768 381952256 382017792 13 3288 19543 29 _ _ (1976079 / 100000) (988041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382017792 :
    ThetaLowerSegment 382017792 382083328 (4775004418099 / 12500) (4775812641363 / 12500) := by
  exact
    packedTile32768 382017792 382083328 13 3272 19545 29 _ _ (61753 / 3125) (1976099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382083328 :
    ThetaLowerSegment 382083328 382148864 (4775812641363 / 12500) (38213071706629 / 100000) := by
  exact
    packedTile32768 382083328 382148864 13 3325 19546 29 _ _ (1976113 / 100000) (494029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382148864 :
    ThetaLowerSegment 382148864 382214400 (38213071706629 / 100000) (38219612700239 / 100000) := by
  exact
    packedTile32768 382148864 382214400 13 3310 19548 29 _ _ (1976131 / 100000) (988067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382214400 :
    ThetaLowerSegment 382214400 382279936 (38219612700239 / 100000) (38226222915299 / 100000) := by
  exact
    packedTile32768 382214400 382279936 13 3345 19550 29 _ _ (494037 / 25000) (1976151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382279936 :
    ThetaLowerSegment 382279936 382345472 (38226222915299 / 100000) (38232914209989 / 100000) := by
  exact
    packedTile32768 382279936 382345472 13 3386 19551 29 _ _ (395233 / 20000) (247021 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382345472 :
    ThetaLowerSegment 382345472 382411008 (38232914209989 / 100000) (7647882379281 / 20000) := by
  exact
    packedTile32768 382345472 382411008 13 3288 19553 29 _ _ (988091 / 50000) (395237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382411008 :
    ThetaLowerSegment 382411008 382476544 (7647882379281 / 20000) (19122934069269 / 50000) := by
  exact
    packedTile32768 382411008 382476544 13 3267 19555 29 _ _ (1976199 / 100000) (988101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382476544 :
    ThetaLowerSegment 382476544 382542080 (19122934069269 / 50000) (153009811561 / 400) := by
  exact
    packedTile32768 382476544 382542080 13 3332 19557 29 _ _ (247027 / 12500) (1976219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382542080 :
    ThetaLowerSegment 382542080 382607616 (153009811561 / 400) (19129503039439 / 50000) := by
  exact
    packedTile32768 382542080 382607616 13 3316 19558 29 _ _ (1976233 / 100000) (494059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382607616 :
    ThetaLowerSegment 382607616 382673152 (19129503039439 / 50000) (2391609562487 / 6250) := by
  exact
    packedTile32768 382607616 382673152 13 3414 19560 29 _ _ (1976251 / 100000) (988127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382673152 :
    ThetaLowerSegment 382673152 382738688 (2391609562487 / 6250) (9568058295641 / 25000) := by
  exact
    packedTile32768 382673152 382738688 13 3279 19562 29 _ _ (494067 / 25000) (1976271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382738688 :
    ThetaLowerSegment 382738688 382804224 (9568058295641 / 25000) (19139446631507 / 50000) := by
  exact
    packedTile32768 382738688 382804224 13 3370 19563 29 _ _ (395257 / 20000) (61759 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382804224 :
    ThetaLowerSegment 382804224 382869760 (19139446631507 / 50000) (19142673932673 / 50000) := by
  exact
    packedTile32768 382804224 382869760 13 3266 19565 29 _ _ (988151 / 50000) (395261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382869760 :
    ThetaLowerSegment 382869760 382935296 (19142673932673 / 50000) (2393239634019 / 6250) := by
  exact
    packedTile32768 382869760 382935296 13 3282 19567 29 _ _ (1976319 / 100000) (988161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell382935296 :
    ThetaLowerSegment 382935296 383000832 (2393239634019 / 6250) (239365108247 / 625) := by
  exact
    packedTile32768 382935296 383000832 13 3331 19568 29 _ _ (123521 / 6250) (1976339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383000832 :
    ThetaLowerSegment 383000832 383066368 (239365108247 / 625) (1197031081947 / 3125) := by
  exact
    packedTile32768 383000832 383066368 13 3328 19570 29 _ _ (1976353 / 100000) (494089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383066368 :
    ThetaLowerSegment 383066368 383131904 (1197031081947 / 3125) (4788937604043 / 12500) := by
  exact
    packedTile32768 383066368 383131904 13 3292 19572 29 _ _ (197637 / 10000) (1976373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383131904 :
    ThetaLowerSegment 383131904 383197440 (4788937604043 / 12500) (2394880878711 / 6250) := by
  exact
    packedTile32768 383131904 383197440 13 3336 19573 29 _ _ (1976387 / 100000) (197639 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383197440 :
    ThetaLowerSegment 383197440 383262976 (2394880878711 / 6250) (9581161954589 / 25000) := by
  exact
    packedTile32768 383197440 383262976 13 3316 19575 29 _ _ (395281 / 20000) (247051 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383262976 :
    ThetaLowerSegment 383262976 383328512 (9581161954589 / 25000) (19165625522129 / 50000) := by
  exact
    packedTile32768 383262976 383328512 13 3341 19577 29 _ _ (988211 / 50000) (79057 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383328512 :
    ThetaLowerSegment 383328512 383394048 (19165625522129 / 50000) (38337743646373 / 100000) := by
  exact
    packedTile32768 383328512 383394048 13 3285 19578 29 _ _ (1976439 / 100000) (988221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383394048 :
    ThetaLowerSegment 383394048 383459584 (38337743646373 / 100000) (38344333150677 / 100000) := by
  exact
    packedTile32768 383394048 383459584 13 3334 19580 29 _ _ (247057 / 12500) (1976459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383459584 :
    ThetaLowerSegment 383459584 383525120 (38344333150677 / 100000) (38350815982117 / 100000) := by
  exact
    packedTile32768 383459584 383525120 13 3280 19582 29 _ _ (1976473 / 100000) (494119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383525120 :
    ThetaLowerSegment 383525120 383590656 (38350815982117 / 100000) (38357356187527 / 100000) := by
  exact
    packedTile32768 383525120 383590656 13 3309 19583 29 _ _ (197649 / 10000) (1976493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383590656 :
    ThetaLowerSegment 383590656 383656192 (38357356187527 / 100000) (1534556253269 / 4000) := by
  exact
    packedTile32768 383590656 383656192 13 3314 19585 29 _ _ (1976507 / 100000) (197651 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383656192 :
    ThetaLowerSegment 383656192 383721728 (1534556253269 / 4000) (38370533616697 / 100000) := by
  exact
    packedTile32768 383656192 383721728 13 3353 19587 29 _ _ (494131 / 25000) (1976527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383721728 :
    ThetaLowerSegment 383721728 383787264 (38370533616697 / 100000) (1535082880573 / 4000) := by
  exact
    packedTile32768 383721728 383787264 13 3308 19588 29 _ _ (1976541 / 100000) (61767 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383787264 :
    ThetaLowerSegment 383787264 383852800 (1535082880573 / 4000) (38383568960471 / 100000) := by
  exact
    packedTile32768 383787264 383852800 13 3287 19590 29 _ _ (988279 / 50000) (1976561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383852800 :
    ThetaLowerSegment 383852800 383918336 (38383568960471 / 100000) (19194995426323 / 50000) := by
  exact
    packedTile32768 383852800 383918336 13 3249 19592 29 _ _ (79063 / 4000) (988289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383918336 :
    ThetaLowerSegment 383918336 383983872 (19194995426323 / 50000) (38396412803303 / 100000) := by
  exact
    packedTile32768 383918336 383983872 13 3249 19593 29 _ _ (1976593 / 100000) (494149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell383983872 :
    ThetaLowerSegment 383983872 384049408 (38396412803303 / 100000) (38403119441033 / 100000) := by
  exact
    packedTile32768 383983872 384049408 13 3393 19595 29 _ _ (197661 / 10000) (1976613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384049408 :
    ThetaLowerSegment 384049408 384114944 (38403119441033 / 100000) (38409824159817 / 100000) := by
  exact
    packedTile32768 384049408 384114944 13 3392 19597 29 _ _ (1976627 / 100000) (197663 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384114944 :
    ThetaLowerSegment 384114944 384180480 (38409824159817 / 100000) (38416293715629 / 100000) := by
  exact
    packedTile32768 384114944 384180480 13 3273 19598 29 _ _ (494161 / 25000) (1976647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384180480 :
    ThetaLowerSegment 384180480 384246016 (38416293715629 / 100000) (19211425150083 / 50000) := by
  exact
    packedTile32768 384180480 384246016 13 3317 19600 29 _ _ (1976661 / 100000) (247083 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384246016 :
    ThetaLowerSegment 384246016 384311552 (19211425150083 / 50000) (3842940891777 / 10000) := by
  exact
    packedTile32768 384246016 384311552 13 3318 19602 29 _ _ (988339 / 50000) (1976681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384311552 :
    ThetaLowerSegment 384311552 384377088 (3842940891777 / 10000) (1921795216877 / 5000) := by
  exact
    packedTile32768 384311552 384377088 13 3286 19603 29 _ _ (395339 / 20000) (988349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384377088 :
    ThetaLowerSegment 384377088 384442624 (1921795216877 / 5000) (9610622685481 / 25000) := by
  exact
    packedTile32768 384377088 384442624 13 3332 19605 29 _ _ (247089 / 12500) (395343 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384442624 :
    ThetaLowerSegment 384442624 384508160 (9610622685481 / 25000) (38448944762109 / 100000) := by
  exact
    packedTile32768 384442624 384508160 13 3265 19607 29 _ _ (1976729 / 100000) (494183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384508160 :
    ThetaLowerSegment 384508160 384573696 (38448944762109 / 100000) (38455355349387 / 100000) := by
  exact
    packedTile32768 384508160 384573696 13 3243 19608 29 _ _ (988373 / 50000) (1976749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384573696 :
    ThetaLowerSegment 384573696 384639232 (38455355349387 / 100000) (3846192017931 / 10000) := by
  exact
    packedTile32768 384573696 384639232 13 3321 19610 29 _ _ (1976763 / 100000) (988383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384639232 :
    ThetaLowerSegment 384639232 384704768 (3846192017931 / 10000) (3846844157653 / 10000) := by
  exact
    packedTile32768 384639232 384704768 13 3299 19612 29 _ _ (98839 / 5000) (1976783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384704768 :
    ThetaLowerSegment 384704768 384770304 (3846844157653 / 10000) (4809388911201 / 12500) := by
  exact
    packedTile32768 384704768 384770304 13 3374 19613 29 _ _ (1976797 / 100000) (2471 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384770304 :
    ThetaLowerSegment 384770304 384835840 (4809388911201 / 12500) (4810219173081 / 12500) := by
  exact
    packedTile32768 384770304 384835840 13 3360 19615 29 _ _ (988407 / 50000) (1976817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384835840 :
    ThetaLowerSegment 384835840 384901376 (4810219173081 / 12500) (38488405420963 / 100000) := by
  exact
    packedTile32768 384835840 384901376 13 3365 19617 29 _ _ (1976831 / 100000) (988417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384901376 :
    ThetaLowerSegment 384901376 384966912 (38488405420963 / 100000) (38494853899139 / 100000) := by
  exact
    packedTile32768 384901376 384966912 13 3262 19618 29 _ _ (123553 / 6250) (1976851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell384966912 :
    ThetaLowerSegment 384966912 385032448 (38494853899139 / 100000) (19250687788387 / 50000) := by
  exact
    packedTile32768 384966912 385032448 13 3299 19620 29 _ _ (395373 / 20000) (494217 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385032448 :
    ThetaLowerSegment 385032448 385097984 (19250687788387 / 50000) (3850785579597 / 10000) := by
  exact
    packedTile32768 385032448 385097984 13 3278 19622 29 _ _ (988441 / 50000) (395377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385097984 :
    ThetaLowerSegment 385097984 385163520 (3850785579597 / 10000) (9628591925319 / 25000) := by
  exact
    packedTile32768 385097984 385163520 13 3294 19623 29 _ _ (1976899 / 100000) (988451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385163520 :
    ThetaLowerSegment 385163520 385229056 (9628591925319 / 25000) (9630248580927 / 25000) := by
  exact
    packedTile32768 385163520 385229056 13 3352 19625 29 _ _ (494229 / 25000) (1976919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385229056 :
    ThetaLowerSegment 385229056 385294592 (9630248580927 / 25000) (38527472733149 / 100000) := by
  exact
    packedTile32768 385229056 385294592 13 3277 19627 29 _ _ (1976933 / 100000) (247117 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385294592 :
    ThetaLowerSegment 385294592 385360128 (38527472733149 / 100000) (38534139008549 / 100000) := by
  exact
    packedTile32768 385294592 385360128 13 3372 19628 29 _ _ (39539 / 2000) (1976953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385360128 :
    ThetaLowerSegment 385360128 385425664 (38534139008549 / 100000) (38540674861451 / 100000) := by
  exact
    packedTile32768 385360128 385425664 13 3306 19630 29 _ _ (1976967 / 100000) (197697 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385425664 :
    ThetaLowerSegment 385425664 385491200 (38540674861451 / 100000) (38547196931667 / 100000) := by
  exact
    packedTile32768 385425664 385491200 13 3299 19632 29 _ _ (247123 / 12500) (1976987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385491200 :
    ThetaLowerSegment 385491200 385556736 (38547196931667 / 100000) (3855364788593 / 10000) := by
  exact
    packedTile32768 385491200 385556736 13 3263 19633 29 _ _ (1977001 / 100000) (494251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385556736 :
    ThetaLowerSegment 385556736 385622272 (3855364788593 / 10000) (9640053390677 / 25000) := by
  exact
    packedTile32768 385556736 385622272 13 3321 19635 29 _ _ (988509 / 50000) (1977021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385622272 :
    ThetaLowerSegment 385622272 385687808 (9640053390677 / 25000) (38566806974433 / 100000) := by
  exact
    packedTile32768 385622272 385687808 13 3335 19637 29 _ _ (395407 / 20000) (988519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385687808 :
    ThetaLowerSegment 385687808 385753344 (38566806974433 / 100000) (7714668621669 / 20000) := by
  exact
    packedTile32768 385687808 385753344 13 3306 19638 29 _ _ (494263 / 25000) (395411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385753344 :
    ThetaLowerSegment 385753344 385818880 (7714668621669 / 20000) (9644980204227 / 25000) := by
  exact
    packedTile32768 385753344 385818880 13 3327 19640 29 _ _ (1977069 / 100000) (123567 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385818880 :
    ThetaLowerSegment 385818880 385884416 (9644980204227 / 25000) (241165307218 / 625) := by
  exact
    packedTile32768 385818880 385884416 13 3302 19642 29 _ _ (988543 / 50000) (1977089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385884416 :
    ThetaLowerSegment 385884416 385949952 (241165307218 / 625) (9648247352901 / 25000) := by
  exact
    packedTile32768 385884416 385949952 13 3308 19643 29 _ _ (1977103 / 100000) (988553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell385949952 :
    ThetaLowerSegment 385949952 386015488 (9648247352901 / 25000) (9649846842981 / 25000) := by
  exact
    packedTile32768 385949952 386015488 13 3236 19645 29 _ _ (12357 / 625) (1977123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386015488 :
    ThetaLowerSegment 386015488 386081024 (9649846842981 / 25000) (154423631879 / 400) := by
  exact
    packedTile32768 386015488 386081024 13 3298 19647 29 _ _ (1977137 / 100000) (98857 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386081024 :
    ThetaLowerSegment 386081024 386146560 (154423631879 / 400) (19306247923439 / 50000) := by
  exact
    packedTile32768 386081024 386146560 13 3332 19648 29 _ _ (988577 / 50000) (1977157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386146560 :
    ThetaLowerSegment 386146560 386212096 (19306247923439 / 50000) (38619062031769 / 100000) := by
  exact
    packedTile32768 386146560 386212096 13 3321 19650 29 _ _ (1977171 / 100000) (988587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386212096 :
    ThetaLowerSegment 386212096 386277632 (38619062031769 / 100000) (7725139890377 / 20000) := by
  exact
    packedTile32768 386212096 386277632 13 3357 19652 29 _ _ (494297 / 25000) (1977191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386277632 :
    ThetaLowerSegment 386277632 386343168 (7725139890377 / 20000) (772644207759 / 2000) := by
  exact
    packedTile32768 386277632 386343168 13 3293 19653 29 _ _ (395441 / 20000) (247151 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386343168 :
    ThetaLowerSegment 386343168 386408704 (772644207759 / 2000) (19319369587497 / 50000) := by
  exact
    packedTile32768 386343168 386408704 13 3302 19655 29 _ _ (988611 / 50000) (79089 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386408704 :
    ThetaLowerSegment 386408704 386474240 (19319369587497 / 50000) (19322643895281 / 50000) := by
  exact
    packedTile32768 386408704 386474240 13 3312 19657 29 _ _ (1977239 / 100000) (988621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386474240 :
    ThetaLowerSegment 386474240 386539776 (19322643895281 / 50000) (19325931083381 / 50000) := by
  exact
    packedTile32768 386474240 386539776 13 3325 19658 29 _ _ (247157 / 12500) (1977259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386539776 :
    ThetaLowerSegment 386539776 386605312 (19325931083381 / 50000) (38658278417647 / 100000) := by
  exact
    packedTile32768 386539776 386605312 13 3245 19660 29 _ _ (1977273 / 100000) (494319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386605312 :
    ThetaLowerSegment 386605312 386670848 (38658278417647 / 100000) (38664744155947 / 100000) := by
  exact
    packedTile32768 386605312 386670848 13 3270 19662 29 _ _ (197729 / 10000) (1977293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386670848 :
    ThetaLowerSegment 386670848 386736384 (38664744155947 / 100000) (1208477844357 / 3125) := by
  exact
    packedTile32768 386670848 386736384 13 3311 19663 29 _ _ (1977307 / 100000) (197731 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386736384 :
    ThetaLowerSegment 386736384 386801920 (1208477844357 / 3125) (2417374387071 / 6250) := by
  exact
    packedTile32768 386736384 386801920 13 3388 19665 29 _ _ (494331 / 25000) (1977327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386801920 :
    ThetaLowerSegment 386801920 386867456 (2417374387071 / 6250) (4835573325339 / 12500) := by
  exact
    packedTile32768 386801920 386867456 13 3336 19667 29 _ _ (1977341 / 100000) (61792 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386867456 :
    ThetaLowerSegment 386867456 386932992 (4835573325339 / 12500) (4836399860983 / 12500) := by
  exact
    packedTile32768 386867456 386932992 13 3344 19668 29 _ _ (988679 / 50000) (1977361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386932992 :
    ThetaLowerSegment 386932992 386998528 (4836399860983 / 12500) (38697722247989 / 100000) := by
  exact
    packedTile32768 386932992 386998528 13 3299 19670 29 _ _ (15819 / 800) (988689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell386998528 :
    ThetaLowerSegment 386998528 387064064 (38697722247989 / 100000) (7740846759969 / 20000) := by
  exact
    packedTile32768 386998528 387064064 13 3293 19672 29 _ _ (123587 / 6250) (395479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387064064 :
    ThetaLowerSegment 387064064 387129600 (7740846759969 / 20000) (19355435980929 / 50000) := by
  exact
    packedTile32768 387064064 387129600 13 3357 19673 29 _ _ (1977409 / 100000) (494353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387129600 :
    ThetaLowerSegment 387129600 387195136 (19355435980929 / 50000) (774349610391 / 2000) := by
  exact
    packedTile32768 387129600 387195136 13 3342 19675 29 _ _ (988713 / 50000) (1977429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387195136 :
    ThetaLowerSegment 387195136 387260672 (774349610391 / 2000) (19362028745821 / 50000) := by
  exact
    packedTile32768 387195136 387260672 13 3326 19677 29 _ _ (988721 / 50000) (395489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387260672 :
    ThetaLowerSegment 387260672 387326208 (19362028745821 / 50000) (9682642810397 / 25000) := by
  exact
    packedTile32768 387260672 387326208 13 3294 19678 29 _ _ (1977459 / 100000) (988731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387326208 :
    ThetaLowerSegment 387326208 387391744 (9682642810397 / 25000) (4842148237351 / 12500) := by
  exact
    packedTile32768 387326208 387391744 13 3345 19680 29 _ _ (494369 / 25000) (1977479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387391744 :
    ThetaLowerSegment 387391744 387457280 (4842148237351 / 12500) (9685943726371 / 25000) := by
  exact
    packedTile32768 387391744 387457280 13 3332 19682 29 _ _ (1977493 / 100000) (247187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387457280 :
    ThetaLowerSegment 387457280 387522816 (9685943726371 / 25000) (19375171108097 / 50000) := by
  exact
    packedTile32768 387457280 387522816 13 3321 19683 29 _ _ (197751 / 10000) (1977513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387522816 :
    ThetaLowerSegment 387522816 387588352 (19375171108097 / 50000) (38756905628307 / 100000) := by
  exact
    packedTile32768 387522816 387588352 13 3319 19685 29 _ _ (1977527 / 100000) (197753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387588352 :
    ThetaLowerSegment 387588352 387653888 (38756905628307 / 100000) (38763467119299 / 100000) := by
  exact
    packedTile32768 387588352 387653888 13 3318 19687 29 _ _ (247193 / 12500) (1977547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387653888 :
    ThetaLowerSegment 387653888 387719424 (38763467119299 / 100000) (19384983681153 / 50000) := by
  exact
    packedTile32768 387653888 387719424 13 3287 19688 29 _ _ (1977561 / 100000) (494391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387719424 :
    ThetaLowerSegment 387719424 387784960 (19384983681153 / 50000) (969414460139 / 2500) := by
  exact
    packedTile32768 387719424 387784960 13 3343 19690 29 _ _ (988789 / 50000) (1977581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387784960 :
    ThetaLowerSegment 387784960 387850496 (969414460139 / 2500) (969579787081 / 2500) := by
  exact
    packedTile32768 387784960 387850496 13 3344 19692 29 _ _ (395519 / 20000) (988799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387850496 :
    ThetaLowerSegment 387850496 387916032 (969579787081 / 2500) (4848730521251 / 12500) := by
  exact
    packedTile32768 387850496 387916032 13 3364 19693 29 _ _ (494403 / 25000) (395523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387916032 :
    ThetaLowerSegment 387916032 387981568 (4848730521251 / 12500) (4849533438219 / 12500) := by
  exact
    packedTile32768 387916032 387981568 13 3248 19695 29 _ _ (494407 / 25000) (1977631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell387981568 :
    ThetaLowerSegment 387981568 388047104 (4849533438219 / 12500) (38802922281177 / 100000) := by
  exact
    packedTile32768 387981568 388047104 13 3365 19697 29 _ _ (395529 / 20000) (123603 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388047104 :
    ThetaLowerSegment 388047104 388112640 (38802922281177 / 100000) (38809430766819 / 100000) := by
  exact
    packedTile32768 388047104 388112640 13 3291 19698 29 _ _ (988831 / 50000) (395533 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388112640 :
    ThetaLowerSegment 388112640 388178176 (38809430766819 / 100000) (38815921509297 / 100000) := by
  exact
    packedTile32768 388112640 388178176 13 3282 19700 29 _ _ (1977679 / 100000) (988841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388178176 :
    ThetaLowerSegment 388178176 388243712 (38815921509297 / 100000) (38822505259281 / 100000) := by
  exact
    packedTile32768 388178176 388243712 13 3329 19702 29 _ _ (61803 / 3125) (1977699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388243712 :
    ThetaLowerSegment 388243712 388309248 (38822505259281 / 100000) (38829063355589 / 100000) := by
  exact
    packedTile32768 388243712 388309248 13 3316 19703 29 _ _ (1977713 / 100000) (494429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388309248 :
    ThetaLowerSegment 388309248 388374784 (38829063355589 / 100000) (38835603708699 / 100000) := by
  exact
    packedTile32768 388309248 388374784 13 3307 19705 29 _ _ (197773 / 10000) (1977733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388374784 :
    ThetaLowerSegment 388374784 388440320 (38835603708699 / 100000) (38842019519967 / 100000) := by
  exact
    packedTile32768 388374784 388440320 13 3244 19707 29 _ _ (1977747 / 100000) (7911 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388440320 :
    ThetaLowerSegment 388440320 388505856 (38842019519967 / 100000) (38848702384523 / 100000) := by
  exact
    packedTile32768 388440320 388505856 13 3379 19708 29 _ _ (494441 / 25000) (1977767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388505856 :
    ThetaLowerSegment 388505856 388571392 (38848702384523 / 100000) (38855347725323 / 100000) := by
  exact
    packedTile32768 388505856 388571392 13 3360 19710 29 _ _ (98889 / 5000) (1977783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388571392 :
    ThetaLowerSegment 388571392 388636928 (38855347725323 / 100000) (38861870499829 / 100000) := by
  exact
    packedTile32768 388571392 388636928 13 3298 19712 29 _ _ (1977797 / 100000) (9889 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388636928 :
    ThetaLowerSegment 388636928 388702464 (38861870499829 / 100000) (38868278617189 / 100000) := by
  exact
    packedTile32768 388636928 388702464 13 3240 19713 29 _ _ (988907 / 50000) (1977817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388702464 :
    ThetaLowerSegment 388702464 388768000 (38868278617189 / 100000) (19437338450237 / 50000) := by
  exact
    packedTile32768 388702464 388768000 13 3235 19715 29 _ _ (1977831 / 100000) (988917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388768000 :
    ThetaLowerSegment 388768000 388833536 (19437338450237 / 50000) (19440600910513 / 50000) := by
  exact
    packedTile32768 388768000 388833536 13 3299 19717 29 _ _ (247231 / 12500) (1977851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388833536 :
    ThetaLowerSegment 388833536 388899072 (19440600910513 / 50000) (38887833602371 / 100000) := by
  exact
    packedTile32768 388833536 388899072 13 3353 19718 29 _ _ (395573 / 20000) (494467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388899072 :
    ThetaLowerSegment 388899072 388964608 (38887833602371 / 100000) (1555778142937 / 4000) := by
  exact
    packedTile32768 388899072 388964608 13 3347 19720 29 _ _ (988941 / 50000) (395577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell388964608 :
    ThetaLowerSegment 388964608 389030144 (1555778142937 / 4000) (7780194149467 / 20000) := by
  exact
    packedTile32768 388964608 389030144 13 3295 19722 29 _ _ (988949 / 50000) (1977901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389030144 :
    ThetaLowerSegment 389030144 389095680 (7780194149467 / 20000) (1945376772361 / 5000) := by
  exact
    packedTile32768 389030144 389095680 13 3319 19723 29 _ _ (395583 / 20000) (988959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389095680 :
    ThetaLowerSegment 389095680 389161216 (1945376772361 / 5000) (9728537412957 / 25000) := by
  exact
    packedTile32768 389095680 389161216 13 3344 19725 29 _ _ (494483 / 25000) (395587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389161216 :
    ThetaLowerSegment 389161216 389226752 (9728537412957 / 25000) (19460419537673 / 50000) := by
  exact
    packedTile32768 389161216 389226752 13 3382 19727 29 _ _ (1977949 / 100000) (61811 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389226752 :
    ThetaLowerSegment 389226752 389292288 (19460419537673 / 50000) (4865917086707 / 12500) := by
  exact
    packedTile32768 389226752 389292288 13 3285 19728 29 _ _ (988983 / 50000) (1977969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389292288 :
    ThetaLowerSegment 389292288 389357824 (4865917086707 / 12500) (38933846235709 / 100000) := by
  exact
    packedTile32768 389292288 389357824 13 3291 19730 29 _ _ (1977983 / 100000) (988993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389357824 :
    ThetaLowerSegment 389357824 389423360 (38933846235709 / 100000) (19470197695199 / 50000) := by
  exact
    packedTile32768 389357824 389423360 13 3311 19732 29 _ _ (1977999 / 100000) (989001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389423360 :
    ThetaLowerSegment 389423360 389488896 (19470197695199 / 50000) (19473462410607 / 50000) := by
  exact
    packedTile32768 389423360 389488896 13 3301 19733 29 _ _ (61813 / 3125) (1978019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389488896 :
    ThetaLowerSegment 389488896 389554432 (19473462410607 / 50000) (38953580902259 / 100000) := by
  exact
    packedTile32768 389488896 389554432 13 3365 19735 29 _ _ (1978033 / 100000) (494509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389554432 :
    ThetaLowerSegment 389554432 389619968 (38953580902259 / 100000) (38960019455009 / 100000) := by
  exact
    packedTile32768 389554432 389619968 13 3255 19737 29 _ _ (39561 / 2000) (1978053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389619968 :
    ThetaLowerSegment 389619968 389685504 (38960019455009 / 100000) (38966634111057 / 100000) := by
  exact
    packedTile32768 389619968 389685504 13 3344 19738 29 _ _ (1978067 / 100000) (197807 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389685504 :
    ThetaLowerSegment 389685504 389751040 (38966634111057 / 100000) (7794648973557 / 20000) := by
  exact
    packedTile32768 389685504 389751040 13 3342 19740 29 _ _ (494521 / 25000) (1978087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389751040 :
    ThetaLowerSegment 389751040 389816576 (7794648973557 / 20000) (7795954123937 / 20000) := by
  exact
    packedTile32768 389751040 389816576 13 3299 19742 29 _ _ (19781 / 1000) (1978103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389816576 :
    ThetaLowerSegment 389816576 389882112 (7795954123937 / 20000) (4873284086283 / 12500) := by
  exact
    packedTile32768 389816576 389882112 13 3287 19743 29 _ _ (1978117 / 100000) (49453 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389882112 :
    ThetaLowerSegment 389882112 389947648 (4873284086283 / 12500) (4874095121223 / 12500) := by
  exact
    packedTile32768 389882112 389947648 13 3280 19745 29 _ _ (989067 / 50000) (1978137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell389947648 :
    ThetaLowerSegment 389947648 390013184 (4874095121223 / 12500) (4874906163133 / 12500) := by
  exact
    packedTile32768 389947648 390013184 13 3280 19747 29 _ _ (1978151 / 100000) (989077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390013184 :
    ThetaLowerSegment 390013184 390078720 (4874906163133 / 12500) (975143541311 / 2500) := by
  exact
    packedTile32768 390013184 390078720 13 3282 19748 29 _ _ (247271 / 12500) (1978171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390078720 :
    ThetaLowerSegment 390078720 390144256 (975143541311 / 2500) (1219133241409 / 3125) := by
  exact
    packedTile32768 390078720 390144256 13 3297 19750 29 _ _ (247273 / 12500) (1978187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390144256 :
    ThetaLowerSegment 390144256 390209792 (1219133241409 / 3125) (39018714638549 / 100000) := by
  exact
    packedTile32768 390144256 390209792 13 3261 19752 29 _ _ (1978201 / 100000) (494551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390209792 :
    ThetaLowerSegment 390209792 390275328 (39018714638549 / 100000) (39025300126271 / 100000) := by
  exact
    packedTile32768 390209792 390275328 13 3329 19753 29 _ _ (989109 / 50000) (1978221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390275328 :
    ThetaLowerSegment 390275328 390340864 (39025300126271 / 100000) (19515895357653 / 50000) := by
  exact
    packedTile32768 390275328 390340864 13 3281 19755 29 _ _ (395647 / 20000) (989119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390340864 :
    ThetaLowerSegment 390340864 390406400 (19515895357653 / 50000) (19519163429957 / 50000) := by
  exact
    packedTile32768 390340864 390406400 13 3304 19757 29 _ _ (494563 / 25000) (395651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390406400 :
    ThetaLowerSegment 390406400 390471936 (19519163429957 / 50000) (19522413724281 / 50000) := by
  exact
    packedTile32768 390406400 390471936 13 3286 19758 29 _ _ (494567 / 25000) (1978271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390471936 :
    ThetaLowerSegment 390471936 390537472 (19522413724281 / 50000) (39051377550197 / 100000) := by
  exact
    packedTile32768 390471936 390537472 13 3311 19760 29 _ _ (395657 / 20000) (123643 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390537472 :
    ThetaLowerSegment 390537472 390603008 (39051377550197 / 100000) (39057957382649 / 100000) := by
  exact
    packedTile32768 390537472 390603008 13 3326 19762 29 _ _ (989151 / 50000) (395661 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390603008 :
    ThetaLowerSegment 390603008 390668544 (39057957382649 / 100000) (19532297321447 / 50000) := by
  exact
    packedTile32768 390603008 390668544 13 3355 19763 29 _ _ (1978319 / 100000) (989161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390668544 :
    ThetaLowerSegment 390668544 390734080 (19532297321447 / 50000) (19535568500023 / 50000) := by
  exact
    packedTile32768 390668544 390734080 13 3307 19765 29 _ _ (61823 / 3125) (1978339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390734080 :
    ThetaLowerSegment 390734080 390799616 (19535568500023 / 50000) (19538840694231 / 50000) := by
  exact
    packedTile32768 390734080 390799616 13 3308 19766 29 _ _ (123647 / 6250) (395671 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390799616 :
    ThetaLowerSegment 390799616 390865152 (19538840694231 / 50000) (7816844770949 / 20000) := by
  exact
    packedTile32768 390799616 390865152 13 3307 19768 29 _ _ (1978369 / 100000) (494593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390865152 :
    ThetaLowerSegment 390865152 390930688 (7816844770949 / 20000) (39090649652473 / 100000) := by
  exact
    packedTile32768 390865152 390930688 13 3248 19770 29 _ _ (989193 / 50000) (1978389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390930688 :
    ThetaLowerSegment 390930688 390996224 (39090649652473 / 100000) (39097332697807 / 100000) := by
  exact
    packedTile32768 390930688 390996224 13 3378 19771 29 _ _ (1978403 / 100000) (989203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell390996224 :
    ThetaLowerSegment 390996224 391061760 (39097332697807 / 100000) (1564152243391 / 4000) := by
  exact
    packedTile32768 390996224 391061760 13 3272 19773 29 _ _ (1978419 / 100000) (989211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391061760 :
    ThetaLowerSegment 391061760 391127296 (1564152243391 / 4000) (39110348772627 / 100000) := by
  exact
    packedTile32768 391061760 391127296 13 3307 19775 29 _ _ (494609 / 25000) (1978439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391127296 :
    ThetaLowerSegment 391127296 391192832 (39110348772627 / 100000) (1955843982299 / 5000) := by
  exact
    packedTile32768 391127296 391192832 13 3301 19776 29 _ _ (1978453 / 100000) (247307 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391192832 :
    ThetaLowerSegment 391192832 391258368 (1955843982299 / 5000) (1956178739423 / 5000) := by
  exact
    packedTile32768 391192832 391258368 13 3384 19778 29 _ _ (197847 / 10000) (1978473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391258368 :
    ThetaLowerSegment 391258368 391323904 (1956178739423 / 5000) (19565060799317 / 50000) := by
  exact
    packedTile32768 391258368 391323904 13 3309 19780 29 _ _ (989243 / 50000) (1978489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391323904 :
    ThetaLowerSegment 391323904 391389440 (19565060799317 / 50000) (1223019714797 / 3125) := by
  exact
    packedTile32768 391323904 391389440 13 3290 19781 29 _ _ (1978503 / 100000) (989253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391389440 :
    ThetaLowerSegment 391389440 391454976 (1223019714797 / 3125) (4892892278223 / 12500) := by
  exact
    packedTile32768 391389440 391454976 13 3289 19783 29 _ _ (49463 / 2500) (1978523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391454976 :
    ThetaLowerSegment 391454976 391520512 (4892892278223 / 12500) (39149843487677 / 100000) := by
  exact
    packedTile32768 391454976 391520512 13 3389 19785 29 _ _ (1978537 / 100000) (98927 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391520512 :
    ThetaLowerSegment 391520512 391586048 (39149843487677 / 100000) (1957823680939 / 5000) := by
  exact
    packedTile32768 391520512 391586048 13 3351 19786 29 _ _ (1978553 / 100000) (494639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391586048 :
    ThetaLowerSegment 391586048 391651584 (1957823680939 / 5000) (48953570607 / 125) := by
  exact
    packedTile32768 391586048 391651584 13 3226 19788 29 _ _ (197857 / 10000) (1978573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391651584 :
    ThetaLowerSegment 391651584 391717120 (48953570607 / 125) (39169371972591 / 100000) := by
  exact
    packedTile32768 391651584 391717120 13 3293 19790 29 _ _ (1978587 / 100000) (197859 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391717120 :
    ThetaLowerSegment 391717120 391782656 (39169371972591 / 100000) (7835186604691 / 20000) := by
  exact
    packedTile32768 391717120 391782656 13 3316 19791 29 _ _ (494651 / 25000) (1978607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391782656 :
    ThetaLowerSegment 391782656 391848192 (7835186604691 / 20000) (1567301347991 / 4000) := by
  exact
    packedTile32768 391782656 391848192 13 3336 19793 29 _ _ (98931 / 5000) (1978623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391848192 :
    ThetaLowerSegment 391848192 391913728 (1567301347991 / 4000) (19594518739797 / 50000) := by
  exact
    packedTile32768 391848192 391913728 13 3287 19795 29 _ _ (1978637 / 100000) (24733 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391913728 :
    ThetaLowerSegment 391913728 391979264 (19594518739797 / 50000) (9798885328823 / 25000) := by
  exact
    packedTile32768 391913728 391979264 13 3287 19796 29 _ _ (989327 / 50000) (1978657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell391979264 :
    ThetaLowerSegment 391979264 392044800 (9798885328823 / 25000) (2450135616237 / 6250) := by
  exact
    packedTile32768 391979264 392044800 13 3350 19798 29 _ _ (197867 / 10000) (1978673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392044800 :
    ThetaLowerSegment 392044800 392110336 (2450135616237 / 6250) (9802214455463 / 25000) := by
  exact
    packedTile32768 392044800 392110336 13 3380 19800 29 _ _ (1978687 / 100000) (197869 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392110336 :
    ThetaLowerSegment 392110336 392175872 (9802214455463 / 25000) (9803879534879 / 25000) := by
  exact
    packedTile32768 392110336 392175872 13 3366 19801 29 _ _ (123669 / 6250) (1978707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392175872 :
    ThetaLowerSegment 392175872 392241408 (9803879534879 / 25000) (39222089471957 / 100000) := by
  exact
    packedTile32768 392175872 392241408 13 3321 19803 29 _ _ (1978721 / 100000) (494681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392241408 :
    ThetaLowerSegment 392241408 392306944 (39222089471957 / 100000) (9807160267541 / 25000) := by
  exact
    packedTile32768 392241408 392306944 13 3311 19805 29 _ _ (1978737 / 100000) (98937 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392306944 :
    ThetaLowerSegment 392306944 392372480 (9807160267541 / 25000) (4904421598909 / 12500) := by
  exact
    packedTile32768 392306944 392372480 13 3402 19806 29 _ _ (989377 / 50000) (1978757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392372480 :
    ThetaLowerSegment 392372480 392438016 (4904421598909 / 12500) (19620953346557 / 50000) := by
  exact
    packedTile32768 392372480 392438016 13 3302 19808 29 _ _ (1978771 / 100000) (989387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392438016 :
    ThetaLowerSegment 392438016 392503552 (19620953346557 / 50000) (39248438669001 / 100000) := by
  exact
    packedTile32768 392438016 392503552 13 3301 19810 29 _ _ (1978787 / 100000) (197879 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392503552 :
    ThetaLowerSegment 392503552 392569088 (39248438669001 / 100000) (39254927167317 / 100000) := by
  exact
    packedTile32768 392503552 392569088 13 3279 19811 29 _ _ (494701 / 25000) (1978807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392569088 :
    ThetaLowerSegment 392569088 392634624 (39254927167317 / 100000) (2453844419049 / 6250) := by
  exact
    packedTile32768 392569088 392634624 13 3327 19813 29 _ _ (1978821 / 100000) (247353 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392634624 :
    ThetaLowerSegment 392634624 392700160 (2453844419049 / 6250) (19634023403349 / 50000) := by
  exact
    packedTile32768 392634624 392700160 13 3303 19815 29 _ _ (989419 / 50000) (1978841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392700160 :
    ThetaLowerSegment 392700160 392765696 (19634023403349 / 50000) (9818643761511 / 25000) := by
  exact
    packedTile32768 392700160 392765696 13 3299 19816 29 _ _ (989427 / 50000) (1978857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392765696 :
    ThetaLowerSegment 392765696 392831232 (9818643761511 / 25000) (39281142918893 / 100000) := by
  exact
    packedTile32768 392765696 392831232 13 3319 19818 29 _ _ (1978871 / 100000) (989437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392831232 :
    ThetaLowerSegment 392831232 392896768 (39281142918893 / 100000) (39287627734869 / 100000) := by
  exact
    packedTile32768 392831232 392896768 13 3277 19819 29 _ _ (247361 / 12500) (1978891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392896768 :
    ThetaLowerSegment 392896768 392962304 (39287627734869 / 100000) (39294209569573 / 100000) := by
  exact
    packedTile32768 392896768 392962304 13 3326 19821 29 _ _ (247363 / 12500) (1978907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell392962304 :
    ThetaLowerSegment 392962304 393027840 (39294209569573 / 100000) (39300791460819 / 100000) := by
  exact
    packedTile32768 392962304 393027840 13 3326 19823 29 _ _ (1978921 / 100000) (494731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393027840 :
    ThetaLowerSegment 393027840 393093376 (39300791460819 / 100000) (39307143851799 / 100000) := by
  exact
    packedTile32768 393027840 393093376 13 3210 19824 29 _ _ (989469 / 50000) (1978941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393093376 :
    ThetaLowerSegment 393093376 393158912 (39307143851799 / 100000) (39313676378953 / 100000) := by
  exact
    packedTile32768 393093376 393158912 13 3301 19826 29 _ _ (989477 / 50000) (1978957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393158912 :
    ThetaLowerSegment 393158912 393224448 (39313676378953 / 100000) (983004036673 / 2500) := by
  exact
    packedTile32768 393158912 393224448 13 3277 19828 29 _ _ (1978971 / 100000) (989487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393224448 :
    ThetaLowerSegment 393224448 393289984 (983004036673 / 2500) (2457913557861 / 6250) := by
  exact
    packedTile32768 393224448 393289984 13 3262 19829 29 _ _ (494747 / 25000) (1978991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393289984 :
    ThetaLowerSegment 393289984 393322752 (2457913557861 / 6250) (9832479970863 / 25000) := by
  exact
    packedTile32768 393289984 393322752 12 1669 19831 29 _ _ (494751 / 25000) (1979007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393322752 :
    ThetaLowerSegment 393322752 393339136 (9832479970863 / 25000) (9832891605567 / 25000) := by
  exact
    packedTile32768 393322752 393339136 11 832 19832 29 _ _ (1979013 / 100000) (247377 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell393339136 :
    ThetaLowerSegment 393339136 393341184 (9832891605567 / 25000) (19665892057069 / 50000) := by
  exact
    packedTile32768 393339136 393341184 8 110 19832 29 _ _ (1979017 / 100000) (98951 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_361341184_393341184 :
    ThetaLowerSegment 361341184 393341184 (36131060492137 / 100000) (19665892057069 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell361341184 cell361373952)
                      (ThetaLowerSegment.join cell361406720 cell361439488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell361472256 cell361505024)
                      (ThetaLowerSegment.join cell361537792 cell361570560)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell361603328 cell361636096)
                      (ThetaLowerSegment.join cell361701632 cell361767168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell361832704 cell361898240)
                      (ThetaLowerSegment.join cell361931008 cell361963776))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell361996544 cell362029312)
                      (ThetaLowerSegment.join cell362062080 cell362094848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell362127616 cell362193152)
                      (ThetaLowerSegment.join cell362225920 cell362291456)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell362356992 cell362422528)
                      (ThetaLowerSegment.join cell362488064 cell362553600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell362619136 cell362684672)
                      (ThetaLowerSegment.join cell362750208 cell362815744)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell362848512 cell362914048)
                      (ThetaLowerSegment.join cell362979584 cell363045120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell363110656 cell363176192)
                      (ThetaLowerSegment.join cell363241728 cell363307264)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell363372800 cell363438336)
                      (ThetaLowerSegment.join cell363503872 cell363569408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell363634944 cell363700480)
                      (ThetaLowerSegment.join cell363766016 cell363831552))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell363897088 cell363962624)
                      (ThetaLowerSegment.join cell364028160 cell364093696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell364159232 cell364224768)
                      (ThetaLowerSegment.join cell364290304 cell364355840)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell364421376 cell364486912)
                      (ThetaLowerSegment.join cell364552448 cell364617984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell364683520 cell364716288)
                      (ThetaLowerSegment.join cell364749056 cell364781824))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell364814592 cell364847360)
                      (ThetaLowerSegment.join cell364880128 cell364912896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell364945664 cell364978432)
                      (ThetaLowerSegment.join cell365011200 cell365043968)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell365109504 cell365175040)
                      (ThetaLowerSegment.join cell365240576 cell365306112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell365338880 cell365404416)
                      (ThetaLowerSegment.join cell365469952 cell365535488))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell365601024 cell365666560)
                      (ThetaLowerSegment.join cell365732096 cell365797632))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell365863168 cell365928704)
                      (ThetaLowerSegment.join cell365994240 cell366059776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell366125312 cell366190848)
                      (ThetaLowerSegment.join cell366256384 cell366321920))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell366387456 cell366452992)
                      (ThetaLowerSegment.join cell366518528 cell366584064)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell366649600 cell366715136)
                      (ThetaLowerSegment.join cell366780672 cell366846208))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell366911744 cell366977280)
                      (ThetaLowerSegment.join cell367042816 cell367108352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell367173888 cell367239424)
                      (ThetaLowerSegment.join cell367304960 cell367370496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell367436032 cell367501568)
                      (ThetaLowerSegment.join cell367567104 cell367632640))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell367698176 cell367763712)
                      (ThetaLowerSegment.join cell367829248 cell367894784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell367960320 cell368025856)
                      (ThetaLowerSegment.join cell368091392 cell368156928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell368222464 cell368288000)
                      (ThetaLowerSegment.join cell368353536 cell368419072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell368484608 cell368550144)
                      (ThetaLowerSegment.join cell368615680 cell368681216)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell368746752 cell368812288)
                      (ThetaLowerSegment.join cell368877824 cell368943360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell369008896 cell369074432)
                      (ThetaLowerSegment.join cell369139968 cell369205504)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell369271040 cell369336576)
                      (ThetaLowerSegment.join cell369402112 cell369467648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell369533184 cell369598720)
                      (ThetaLowerSegment.join cell369664256 cell369729792))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell369795328 cell369860864)
                      (ThetaLowerSegment.join cell369926400 cell369991936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell370057472 cell370123008)
                      (ThetaLowerSegment.join cell370188544 cell370254080)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell370319616 cell370385152)
                      (ThetaLowerSegment.join cell370450688 cell370516224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell370581760 cell370647296)
                      (ThetaLowerSegment.join cell370712832 cell370745600)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell370778368 cell370811136)
                      (ThetaLowerSegment.join cell370843904 cell370876672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell370909440 cell370942208)
                      (ThetaLowerSegment.join cell370974976 cell371007744)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell371040512 cell371073280)
                      (ThetaLowerSegment.join cell371106048 cell371138816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell371171584 cell371204352)
                      (ThetaLowerSegment.join cell371237120 cell371269888))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell371302656 cell371335424)
                      (ThetaLowerSegment.join cell371368192 cell371400960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell371433728 cell371466496)
                      (ThetaLowerSegment.join cell371499264 cell371532032)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell371564800 cell371597568)
                      (ThetaLowerSegment.join cell371630336 cell371663104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell371695872 cell371728640)
                      (ThetaLowerSegment.join cell371761408 cell371794176))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell371826944 cell371859712)
                      (ThetaLowerSegment.join cell371892480 cell371925248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell371958016 cell372023552)
                      (ThetaLowerSegment.join cell372056320 cell372089088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell372121856 cell372154624)
                      (ThetaLowerSegment.join cell372187392 cell372220160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell372252928 cell372285696)
                      (ThetaLowerSegment.join cell372351232 cell372416768))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell372449536 cell372515072)
                      (ThetaLowerSegment.join cell372547840 cell372580608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell372613376 cell372646144)
                      (ThetaLowerSegment.join cell372678912 cell372711680)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell372744448 cell372777216)
                      (ThetaLowerSegment.join cell372809984 cell372842752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell372875520 cell372908288)
                      (ThetaLowerSegment.join cell372941056 cell372973824)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell373006592 cell373039360)
                      (ThetaLowerSegment.join cell373072128 cell373104896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell373137664 cell373170432)
                      (ThetaLowerSegment.join cell373203200 cell373235968)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell373268736 cell373301504)
                      (ThetaLowerSegment.join cell373334272 cell373367040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell373399808 cell373432576)
                      (ThetaLowerSegment.join cell373465344 cell373498112))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell373530880 cell373563648)
                      (ThetaLowerSegment.join cell373596416 cell373629184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell373661952 cell373694720)
                      (ThetaLowerSegment.join cell373727488 cell373760256)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell373825792 cell373858560)
                      (ThetaLowerSegment.join cell373891328 cell373924096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell373956864 cell373989632)
                      (ThetaLowerSegment.join cell374022400 cell374055168))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell374087936 cell374120704)
                      (ThetaLowerSegment.join cell374153472 cell374186240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell374219008 cell374251776)
                      (ThetaLowerSegment.join cell374284544 cell374317312)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell374350080 cell374382848)
                      (ThetaLowerSegment.join cell374415616 cell374448384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell374481152 cell374546688)
                      (ThetaLowerSegment.join cell374612224 cell374677760))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell374743296 cell374808832)
                      (ThetaLowerSegment.join cell374874368 cell374939904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell375005440 cell375070976)
                      (ThetaLowerSegment.join cell375136512 cell375202048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell375267584 cell375333120)
                      (ThetaLowerSegment.join cell375398656 cell375464192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell375529728 cell375595264)
                      (ThetaLowerSegment.join cell375660800 cell375726336)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell375791872 cell375857408)
                      (ThetaLowerSegment.join cell375922944 cell375988480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell376054016 cell376119552)
                      (ThetaLowerSegment.join cell376185088 cell376250624)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell376316160 cell376381696)
                      (ThetaLowerSegment.join cell376447232 cell376512768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell376578304 cell376643840)
                      (ThetaLowerSegment.join cell376709376 cell376774912))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell376840448 cell376905984)
                      (ThetaLowerSegment.join cell376971520 cell377037056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell377102592 cell377168128)
                      (ThetaLowerSegment.join cell377233664 cell377299200)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell377364736 cell377430272)
                      (ThetaLowerSegment.join cell377495808 cell377561344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell377626880 cell377692416)
                      (ThetaLowerSegment.join cell377757952 cell377823488))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell377889024 cell377954560)
                      (ThetaLowerSegment.join cell378020096 cell378085632))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell378151168 cell378216704)
                      (ThetaLowerSegment.join cell378282240 cell378347776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell378413312 cell378478848)
                      (ThetaLowerSegment.join cell378544384 cell378609920))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell378675456 cell378740992)
                      (ThetaLowerSegment.join cell378806528 cell378872064))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell378937600 cell379003136)
                      (ThetaLowerSegment.join cell379068672 cell379134208))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell379199744 cell379265280)
                      (ThetaLowerSegment.join cell379330816 cell379396352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell379461888 cell379527424)
                      (ThetaLowerSegment.join cell379592960 cell379658496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell379724032 cell379789568)
                      (ThetaLowerSegment.join cell379855104 cell379920640)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell379986176 cell380051712)
                      (ThetaLowerSegment.join cell380117248 cell380182784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell380248320 cell380313856)
                      (ThetaLowerSegment.join cell380379392 cell380444928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell380510464 cell380576000)
                      (ThetaLowerSegment.join cell380641536 cell380707072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell380772608 cell380838144)
                      (ThetaLowerSegment.join cell380903680 cell380969216))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell381034752 cell381100288)
                      (ThetaLowerSegment.join cell381165824 cell381231360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell381296896 cell381362432)
                      (ThetaLowerSegment.join cell381427968 cell381493504)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell381559040 cell381624576)
                      (ThetaLowerSegment.join cell381690112 cell381755648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell381821184 cell381886720)
                      (ThetaLowerSegment.join cell381952256 cell382017792)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell382083328 cell382148864)
                      (ThetaLowerSegment.join cell382214400 cell382279936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell382345472 cell382411008)
                      (ThetaLowerSegment.join cell382476544 cell382542080)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell382607616 cell382673152)
                      (ThetaLowerSegment.join cell382738688 cell382804224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell382869760 cell382935296)
                      (ThetaLowerSegment.join cell383000832 cell383066368))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell383131904 cell383197440)
                      (ThetaLowerSegment.join cell383262976 cell383328512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell383394048 cell383459584)
                      (ThetaLowerSegment.join cell383525120 cell383590656)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell383656192 cell383721728)
                      (ThetaLowerSegment.join cell383787264 cell383852800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell383918336 cell383983872)
                      (ThetaLowerSegment.join cell384049408 cell384114944)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell384180480 cell384246016)
                      (ThetaLowerSegment.join cell384311552 cell384377088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell384442624 cell384508160)
                      (ThetaLowerSegment.join cell384573696 cell384639232)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell384704768 cell384770304)
                      (ThetaLowerSegment.join cell384835840 cell384901376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell384966912 cell385032448)
                      (ThetaLowerSegment.join cell385097984 cell385163520))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell385229056 cell385294592)
                      (ThetaLowerSegment.join cell385360128 cell385425664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell385491200 cell385556736)
                      (ThetaLowerSegment.join cell385622272 cell385687808)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell385753344 cell385818880)
                      (ThetaLowerSegment.join cell385884416 cell385949952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell386015488 cell386081024)
                      (ThetaLowerSegment.join cell386146560 cell386212096))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell386277632 cell386343168)
                      (ThetaLowerSegment.join cell386408704 cell386474240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell386539776 cell386605312)
                      (ThetaLowerSegment.join cell386670848 cell386736384)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell386801920 cell386867456)
                      (ThetaLowerSegment.join cell386932992 cell386998528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell387064064 cell387129600)
                      (ThetaLowerSegment.join cell387195136 cell387260672))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell387326208 cell387391744)
                      (ThetaLowerSegment.join cell387457280 cell387522816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell387588352 cell387653888)
                      (ThetaLowerSegment.join cell387719424 cell387784960)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell387850496 cell387916032)
                      (ThetaLowerSegment.join cell387981568 cell388047104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell388112640 cell388178176)
                      (ThetaLowerSegment.join cell388243712 cell388309248)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell388374784 cell388440320)
                      (ThetaLowerSegment.join cell388505856 cell388571392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell388636928 cell388702464)
                      (ThetaLowerSegment.join cell388768000 cell388833536)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell388899072 cell388964608)
                      (ThetaLowerSegment.join cell389030144 cell389095680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell389161216 cell389226752)
                      (ThetaLowerSegment.join cell389292288 cell389357824))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell389423360 cell389488896)
                      (ThetaLowerSegment.join cell389554432 cell389619968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell389685504 cell389751040)
                      (ThetaLowerSegment.join cell389816576 cell389882112)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell389947648 cell390013184)
                      (ThetaLowerSegment.join cell390078720 cell390144256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell390209792 cell390275328)
                      (ThetaLowerSegment.join cell390340864 cell390406400)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell390471936 cell390537472)
                (ThetaLowerSegment.join cell390603008 cell390668544))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell390734080 cell390799616)
                (ThetaLowerSegment.join cell390865152 cell390930688)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell390996224 cell391061760)
                (ThetaLowerSegment.join cell391127296 cell391192832))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell391258368 cell391323904)
                (ThetaLowerSegment.join cell391389440 cell391454976))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell391520512 cell391586048)
                (ThetaLowerSegment.join cell391651584 cell391717120))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell391782656 cell391848192)
                (ThetaLowerSegment.join cell391913728 cell391979264)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell392044800 cell392110336)
                (ThetaLowerSegment.join cell392175872 cell392241408))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell392306944 cell392372480)
                (ThetaLowerSegment.join cell392438016 cell392503552)))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell392569088 cell392634624)
              (ThetaLowerSegment.join cell392700160 cell392765696))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell392831232 cell392896768)
              (ThetaLowerSegment.join cell392962304 cell393027840)))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell393093376 cell393158912)
              (ThetaLowerSegment.join cell393224448 cell393289984))
            (ThetaLowerSegment.join cell393322752 cell393339136)))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
