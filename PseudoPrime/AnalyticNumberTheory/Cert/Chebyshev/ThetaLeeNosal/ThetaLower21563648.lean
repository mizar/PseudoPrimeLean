/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis4096
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis8192

/-! # Direct theta estimate up to 21563648 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell13922560 :
    ThetaLowerSegment 13922560 13930752 (1391841141353 / 100000) (696322748971 / 50000) := by
  exact
    packedTile4096 13922560 13930752 10 489 3731 24 _ _ (1644901 / 100000) (205613 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13930752 :
    ThetaLowerSegment 13930752 13938944 (696322748971 / 50000) (696720829049 / 50000) := by
  exact
    packedTile4096 13930752 13938944 10 484 3732 24 _ _ (1644959 / 100000) (822481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13938944 :
    ThetaLowerSegment 13938944 13947136 (696720829049 / 50000) (139425429699 / 10000) := by
  exact
    packedTile4096 13938944 13947136 10 494 3733 24 _ _ (822509 / 50000) (1645021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13947136 :
    ThetaLowerSegment 13947136 13955328 (139425429699 / 10000) (697525257129 / 50000) := by
  exact
    packedTile4096 13947136 13955328 10 484 3734 24 _ _ (1645077 / 100000) (41127 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13955328 :
    ThetaLowerSegment 13955328 13963520 (697525257129 / 50000) (139585169549 / 10000) := by
  exact
    packedTile4096 13955328 13963520 10 487 3735 24 _ _ (102821 / 6250) (1645139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13963520 :
    ThetaLowerSegment 13963520 13971712 (139585169549 / 10000) (43646020228 / 3125) := by
  exact
    packedTile4096 13963520 13971712 10 499 3736 24 _ _ (822597 / 50000) (1645197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13971712 :
    ThetaLowerSegment 13971712 13979904 (43646020228 / 3125) (1397473885507 / 100000) := by
  exact
    packedTile4096 13971712 13979904 10 487 3737 24 _ _ (1645253 / 100000) (205657 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13979904 :
    ThetaLowerSegment 13979904 13988096 (1397473885507 / 100000) (1398293250883 / 100000) := by
  exact
    packedTile4096 13979904 13988096 10 498 3738 24 _ _ (51416 / 3125) (329063 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13988096 :
    ThetaLowerSegment 13988096 13996288 (1398293250883 / 100000) (1399068220153 / 100000) := by
  exact
    packedTile4096 13988096 13996288 10 471 3740 24 _ _ (164537 / 10000) (1645373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13996288 :
    ThetaLowerSegment 13996288 14004480 (1399068220153 / 100000) (349970676877 / 25000) := by
  exact
    packedTile4096 13996288 14004480 10 495 3741 24 _ _ (1645429 / 100000) (205679 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14004480 :
    ThetaLowerSegment 14004480 14012672 (349970676877 / 25000) (280141419299 / 20000) := by
  exact
    packedTile4096 14004480 14012672 10 501 3742 24 _ _ (1645487 / 100000) (164549 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14012672 :
    ThetaLowerSegment 14012672 14020864 (280141419299 / 20000) (280302682807 / 20000) := by
  exact
    packedTile4096 14012672 14020864 10 490 3743 24 _ _ (822773 / 50000) (1645549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14020864 :
    ThetaLowerSegment 14020864 14029056 (280302682807 / 20000) (1402355963283 / 100000) := by
  exact
    packedTile4096 14020864 14029056 10 512 3744 24 _ _ (411401 / 25000) (1645607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14029056 :
    ThetaLowerSegment 14029056 14037248 (1402355963283 / 100000) (701593511549 / 50000) := by
  exact
    packedTile4096 14029056 14037248 10 505 3745 24 _ _ (1645663 / 100000) (822833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14037248 :
    ThetaLowerSegment 14037248 14045440 (701593511549 / 50000) (140399671783 / 10000) := by
  exact
    packedTile4096 14037248 14045440 10 492 3746 24 _ _ (1645721 / 100000) (411431 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14045440 :
    ThetaLowerSegment 14045440 14053632 (140399671783 / 10000) (1404791629087 / 100000) := by
  exact
    packedTile4096 14045440 14053632 10 483 3747 24 _ _ (1645779 / 100000) (822891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14053632 :
    ThetaLowerSegment 14053632 14061824 (1404791629087 / 100000) (56224647757 / 4000) := by
  exact
    packedTile4096 14053632 14061824 10 501 3748 24 _ _ (822919 / 50000) (1645841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14061824 :
    ThetaLowerSegment 14061824 14070016 (56224647757 / 4000) (1406401286317 / 100000) := by
  exact
    packedTile4096 14061824 14070016 10 477 3749 24 _ _ (205737 / 12500) (1645899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14070016 :
    ThetaLowerSegment 14070016 14078208 (1406401286317 / 100000) (1407248952627 / 100000) := by
  exact
    packedTile4096 14070016 14078208 10 515 3751 24 _ _ (822977 / 50000) (1645957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14078208 :
    ThetaLowerSegment 14078208 14086400 (1407248952627 / 100000) (1408091710771 / 100000) := by
  exact
    packedTile4096 14078208 14086400 10 512 3752 24 _ _ (411503 / 25000) (329203 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14086400 :
    ThetaLowerSegment 14086400 14094592 (1408091710771 / 100000) (352226628979 / 25000) := by
  exact
    packedTile4096 14086400 14094592 10 495 3753 24 _ _ (1646071 / 100000) (823037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14094592 :
    ThetaLowerSegment 14094592 14102784 (352226628979 / 25000) (1409721349771 / 100000) := by
  exact
    packedTile4096 14094592 14102784 10 495 3754 24 _ _ (1646129 / 100000) (411533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14102784 :
    ThetaLowerSegment 14102784 14110976 (1409721349771 / 100000) (1410570782263 / 100000) := by
  exact
    packedTile4096 14102784 14110976 10 516 3755 24 _ _ (1646187 / 100000) (164619 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14110976 :
    ThetaLowerSegment 14110976 14119168 (1410570782263 / 100000) (1411400489743 / 100000) := by
  exact
    packedTile4096 14110976 14119168 10 504 3756 24 _ _ (329249 / 20000) (205781 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14119168 :
    ThetaLowerSegment 14119168 14127360 (1411400489743 / 100000) (706099473349 / 50000) := by
  exact
    packedTile4096 14119168 14127360 10 485 3757 24 _ _ (1646303 / 100000) (823153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14127360 :
    ThetaLowerSegment 14127360 14135552 (706099473349 / 50000) (1413040237169 / 100000) := by
  exact
    packedTile4096 14127360 14135552 10 511 3758 24 _ _ (1646361 / 100000) (411591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14135552 :
    ThetaLowerSegment 14135552 14143744 (1413040237169 / 100000) (353467919691 / 25000) := by
  exact
    packedTile4096 14135552 14143744 10 505 3759 24 _ _ (1646419 / 100000) (823211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14143744 :
    ThetaLowerSegment 14143744 14151936 (353467919691 / 25000) (141465869477 / 10000) := by
  exact
    packedTile4096 14143744 14151936 10 478 3760 24 _ _ (1646477 / 100000) (20581 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14151936 :
    ThetaLowerSegment 14151936 14160128 (141465869477 / 10000) (141548854841 / 10000) := by
  exact
    packedTile4096 14151936 14160128 10 504 3761 24 _ _ (329307 / 20000) (823269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14160128 :
    ThetaLowerSegment 14160128 14168320 (141548854841 / 10000) (708146042897 / 50000) := by
  exact
    packedTile4096 14160128 14168320 10 488 3762 24 _ _ (1646593 / 100000) (411649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14168320 :
    ThetaLowerSegment 14168320 14176512 (708146042897 / 50000) (708549472147 / 50000) := by
  exact
    packedTile4096 14168320 14176512 10 490 3764 24 _ _ (32933 / 2000) (1646653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14176512 :
    ThetaLowerSegment 14176512 14184704 (708549472147 / 50000) (141790912463 / 10000) := by
  exact
    packedTile4096 14176512 14184704 10 492 3765 24 _ _ (411677 / 25000) (1646711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14184704 :
    ThetaLowerSegment 14184704 14192896 (141790912463 / 10000) (28373662093 / 2000) := by
  exact
    packedTile4096 14184704 14192896 10 470 3766 24 _ _ (823383 / 50000) (1646769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14192896 :
    ThetaLowerSegment 14192896 14201088 (28373662093 / 2000) (709749964677 / 50000) := by
  exact
    packedTile4096 14192896 14201088 10 496 3767 24 _ _ (205853 / 12500) (1646827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14201088 :
    ThetaLowerSegment 14201088 14209280 (709749964677 / 50000) (284065003347 / 20000) := by
  exact
    packedTile4096 14201088 14209280 10 501 3768 24 _ _ (1646881 / 100000) (411721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14209280 :
    ThetaLowerSegment 14209280 14217472 (284065003347 / 20000) (710575066587 / 50000) := by
  exact
    packedTile4096 14209280 14217472 10 501 3769 24 _ _ (1646939 / 100000) (823471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14217472 :
    ThetaLowerSegment 14217472 14225664 (710575066587 / 50000) (284395714533 / 20000) := by
  exact
    packedTile4096 14217472 14225664 10 503 3770 24 _ _ (1646997 / 100000) (1647 / 100) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14225664 :
    ThetaLowerSegment 14225664 14233856 (284395714533 / 20000) (1422775746801 / 100000) := by
  exact
    packedTile4096 14225664 14233856 10 484 3771 24 _ _ (823527 / 50000) (1647057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14233856 :
    ThetaLowerSegment 14233856 14242048 (1422775746801 / 100000) (284723813629 / 20000) := by
  exact
    packedTile4096 14233856 14242048 10 512 3772 24 _ _ (205889 / 12500) (329423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14242048 :
    ThetaLowerSegment 14242048 14250240 (284723813629 / 20000) (1424436063969 / 100000) := by
  exact
    packedTile4096 14242048 14250240 10 496 3773 24 _ _ (1647169 / 100000) (411793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14250240 :
    ThetaLowerSegment 14250240 14258432 (1424436063969 / 100000) (356316978401 / 25000) := by
  exact
    packedTile4096 14250240 14258432 10 505 3774 24 _ _ (1647227 / 100000) (164723 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14258432 :
    ThetaLowerSegment 14258432 14266624 (356316978401 / 25000) (71304907237 / 5000) := by
  exact
    packedTile4096 14258432 14266624 10 504 3776 24 _ _ (411821 / 25000) (1647287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14266624 :
    ThetaLowerSegment 14266624 14274816 (71304907237 / 5000) (713453494831 / 50000) := by
  exact
    packedTile4096 14266624 14274816 10 491 3777 24 _ _ (823671 / 50000) (329469 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14274816 :
    ThetaLowerSegment 14274816 14283008 (713453494831 / 50000) (713881818571 / 50000) := by
  exact
    packedTile4096 14274816 14283008 10 520 3778 24 _ _ (1647399 / 100000) (823701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14283008 :
    ThetaLowerSegment 14283008 14291200 (713881818571 / 50000) (142859395547 / 10000) := by
  exact
    packedTile4096 14283008 14291200 10 504 3779 24 _ _ (1647457 / 100000) (82373 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14291200 :
    ThetaLowerSegment 14291200 14299392 (142859395547 / 10000) (142940123733 / 10000) := by
  exact
    packedTile4096 14291200 14299392 10 490 3780 24 _ _ (823757 / 50000) (1647517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14299392 :
    ThetaLowerSegment 14299392 14307584 (142940123733 / 10000) (1430193718981 / 100000) := by
  exact
    packedTile4096 14299392 14307584 10 481 3781 24 _ _ (1647571 / 100000) (823787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14307584 :
    ThetaLowerSegment 14307584 14315776 (1430193718981 / 100000) (7155178287 / 500) := by
  exact
    packedTile4096 14307584 14315776 10 511 3782 24 _ _ (1647629 / 100000) (102977 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14315776 :
    ThetaLowerSegment 14315776 14323968 (7155178287 / 500) (71592151177 / 5000) := by
  exact
    packedTile4096 14315776 14323968 10 490 3783 24 _ _ (823843 / 50000) (1647689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14323968 :
    ThetaLowerSegment 14323968 14332160 (71592151177 / 5000) (358165076017 / 25000) := by
  exact
    packedTile4096 14323968 14332160 10 496 3784 24 _ _ (1647743 / 100000) (823873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14332160 :
    ThetaLowerSegment 14332160 14340352 (358165076017 / 25000) (358373934667 / 25000) := by
  exact
    packedTile4096 14332160 14340352 10 507 3785 24 _ _ (8239 / 500) (1647803 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14340352 :
    ThetaLowerSegment 14340352 14348544 (358373934667 / 25000) (717151594299 / 50000) := by
  exact
    packedTile4096 14340352 14348544 10 490 3786 24 _ _ (1647857 / 100000) (82393 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14348544 :
    ThetaLowerSegment 14348544 14356736 (717151594299 / 50000) (717599826907 / 50000) := by
  exact
    packedTile4096 14348544 14356736 10 544 3787 24 _ _ (823957 / 50000) (1647917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14356736 :
    ThetaLowerSegment 14356736 14364928 (717599826907 / 50000) (718005227773 / 50000) := by
  exact
    packedTile4096 14356736 14364928 10 492 3789 24 _ _ (1647971 / 100000) (823987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14364928 :
    ThetaLowerSegment 14364928 14373120 (718005227773 / 50000) (287363927557 / 20000) := by
  exact
    packedTile4096 14364928 14373120 10 491 3790 24 _ _ (1648029 / 100000) (51501 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14373120 :
    ThetaLowerSegment 14373120 14381312 (287363927557 / 20000) (1437646976957 / 100000) := by
  exact
    packedTile4096 14373120 14381312 10 502 3791 24 _ _ (824043 / 50000) (1648089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14381312 :
    ThetaLowerSegment 14381312 14389504 (1437646976957 / 100000) (1438507307603 / 100000) := by
  exact
    packedTile4096 14381312 14389504 10 522 3792 24 _ _ (1648143 / 100000) (824073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14389504 :
    ThetaLowerSegment 14389504 14397696 (1438507307603 / 100000) (89958934031 / 6250) := by
  exact
    packedTile4096 14389504 14397696 10 507 3793 24 _ _ (1648199 / 100000) (824101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14397696 :
    ThetaLowerSegment 14397696 14405888 (89958934031 / 6250) (90008896791 / 6250) := by
  exact
    packedTile4096 14397696 14405888 10 485 3794 24 _ _ (51508 / 3125) (1648259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14405888 :
    ThetaLowerSegment 14405888 14414080 (90008896791 / 6250) (7204733627 / 500) := by
  exact
    packedTile4096 14405888 14414080 10 488 3795 24 _ _ (1648313 / 100000) (412079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14414080 :
    ThetaLowerSegment 14414080 14422272 (7204733627 / 500) (144177255877 / 10000) := by
  exact
    packedTile4096 14414080 14422272 10 501 3796 24 _ _ (164837 / 10000) (1648373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14422272 :
    ThetaLowerSegment 14422272 14430464 (144177255877 / 10000) (360645072 / 25) := by
  exact
    packedTile4096 14422272 14430464 10 490 3797 24 _ _ (1648427 / 100000) (164843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14430464 :
    ThetaLowerSegment 14430464 14438656 (360645072 / 25) (45105773381 / 3125) := by
  exact
    packedTile4096 14430464 14438656 10 488 3798 24 _ _ (412121 / 25000) (1648487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14438656 :
    ThetaLowerSegment 14438656 14446848 (45105773381 / 3125) (180529012219 / 12500) := by
  exact
    packedTile4096 14438656 14446848 10 514 3799 24 _ _ (82427 / 5000) (1648543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14446848 :
    ThetaLowerSegment 14446848 14455040 (180529012219 / 12500) (1445034964491 / 100000) := by
  exact
    packedTile4096 14446848 14455040 10 487 3800 24 _ _ (1648597 / 100000) (8243 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14455040 :
    ThetaLowerSegment 14455040 14463232 (1445034964491 / 100000) (1445867534761 / 100000) := by
  exact
    packedTile4096 14455040 14463232 10 505 3801 24 _ _ (824327 / 50000) (1648657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14463232 :
    ThetaLowerSegment 14463232 14471424 (1445867534761 / 100000) (1446658916041 / 100000) := by
  exact
    packedTile4096 14463232 14471424 10 480 3803 24 _ _ (1648711 / 100000) (824357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14471424 :
    ThetaLowerSegment 14471424 14479616 (1446658916041 / 100000) (180938091689 / 12500) := by
  exact
    packedTile4096 14471424 14479616 10 513 3804 24 _ _ (1648767 / 100000) (164877 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14479616 :
    ThetaLowerSegment 14479616 14487808 (180938091689 / 12500) (90519644131 / 6250) := by
  exact
    packedTile4096 14479616 14487808 10 491 3805 24 _ _ (206103 / 12500) (1648827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14487808 :
    ThetaLowerSegment 14487808 14496000 (90519644131 / 6250) (45285019013 / 3125) := by
  exact
    packedTile4096 14487808 14496000 10 489 3806 24 _ _ (20611 / 1250) (1648883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14496000 :
    ThetaLowerSegment 14496000 14504192 (45285019013 / 3125) (72496594271 / 5000) := by
  exact
    packedTile4096 14496000 14504192 10 492 3807 24 _ _ (1648937 / 100000) (82447 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14504192 :
    ThetaLowerSegment 14504192 14512384 (72496594271 / 5000) (1450741540983 / 100000) := by
  exact
    packedTile4096 14504192 14512384 10 491 3808 24 _ _ (1648993 / 100000) (412249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14512384 :
    ThetaLowerSegment 14512384 14520576 (1450741540983 / 100000) (1451541330233 / 100000) := by
  exact
    packedTile4096 14512384 14520576 10 485 3809 24 _ _ (32981 / 2000) (1649053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14520576 :
    ThetaLowerSegment 14520576 14528768 (1451541330233 / 100000) (290473836289 / 20000) := by
  exact
    packedTile4096 14520576 14528768 10 502 3810 24 _ _ (824553 / 50000) (1649109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14528768 :
    ThetaLowerSegment 14528768 14536960 (290473836289 / 20000) (726589460239 / 50000) := by
  exact
    packedTile4096 14528768 14536960 10 491 3811 24 _ _ (1649163 / 100000) (824583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14536960 :
    ThetaLowerSegment 14536960 14545152 (726589460239 / 50000) (727005063427 / 50000) := by
  exact
    packedTile4096 14536960 14545152 10 504 3812 24 _ _ (1649219 / 100000) (824611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14545152 :
    ThetaLowerSegment 14545152 14553344 (727005063427 / 50000) (727410785077 / 50000) := by
  exact
    packedTile4096 14545152 14553344 10 492 3813 24 _ _ (65971 / 4000) (824639 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14553344 :
    ThetaLowerSegment 14553344 14561536 (727410785077 / 50000) (727824767409 / 50000) := by
  exact
    packedTile4096 14553344 14561536 10 502 3814 24 _ _ (412333 / 25000) (329867 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14561536 :
    ThetaLowerSegment 14561536 14569728 (727824767409 / 50000) (728231341551 / 50000) := by
  exact
    packedTile4096 14561536 14569728 10 493 3815 24 _ _ (412347 / 25000) (1649391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14569728 :
    ThetaLowerSegment 14569728 14577920 (728231341551 / 50000) (728646176717 / 50000) := by
  exact
    packedTile4096 14569728 14577920 10 503 3817 24 _ _ (412361 / 25000) (1649447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14577920 :
    ThetaLowerSegment 14577920 14586112 (728646176717 / 50000) (729070922967 / 50000) := by
  exact
    packedTile4096 14577920 14586112 10 515 3818 24 _ _ (3299 / 200) (1649503 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14586112 :
    ThetaLowerSegment 14586112 14594304 (729070922967 / 50000) (1458961675763 / 100000) := by
  exact
    packedTile4096 14586112 14594304 10 497 3819 24 _ _ (1649557 / 100000) (41239 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14594304 :
    ThetaLowerSegment 14594304 14602496 (1458961675763 / 100000) (729895715551 / 50000) := by
  exact
    packedTile4096 14594304 14602496 10 503 3820 24 _ _ (1649613 / 100000) (103101 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14602496 :
    ThetaLowerSegment 14602496 14610688 (729895715551 / 50000) (1460584921891 / 100000) := by
  exact
    packedTile4096 14602496 14610688 10 481 3821 24 _ _ (1649669 / 100000) (206209 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14610688 :
    ThetaLowerSegment 14610688 14618880 (1460584921891 / 100000) (1461396586591 / 100000) := by
  exact
    packedTile4096 14610688 14618880 10 492 3822 24 _ _ (65989 / 4000) (51554 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14618880 :
    ThetaLowerSegment 14618880 14627072 (1461396586591 / 100000) (58486483399 / 4000) := by
  exact
    packedTile4096 14618880 14627072 10 464 3823 24 _ _ (1649781 / 100000) (206223 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14627072 :
    ThetaLowerSegment 14627072 14635264 (58486483399 / 4000) (1462996902497 / 100000) := by
  exact
    packedTile4096 14627072 14635264 10 506 3824 24 _ _ (1649837 / 100000) (20623 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14635264 :
    ThetaLowerSegment 14635264 14643456 (1462996902497 / 100000) (1463808649853 / 100000) := by
  exact
    packedTile4096 14635264 14643456 10 492 3825 24 _ _ (1649893 / 100000) (206237 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14643456 :
    ThetaLowerSegment 14643456 14651648 (1463808649853 / 100000) (73230278761 / 5000) := by
  exact
    packedTile4096 14643456 14651648 10 483 3826 24 _ _ (1649949 / 100000) (51561 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14651648 :
    ThetaLowerSegment 14651648 14659840 (73230278761 / 5000) (293081825531 / 20000) := by
  exact
    packedTile4096 14651648 14659840 10 487 3827 24 _ _ (330001 / 20000) (206251 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14659840 :
    ThetaLowerSegment 14659840 14668032 (293081825531 / 20000) (1466260559131 / 100000) := by
  exact
    packedTile4096 14659840 14668032 10 516 3828 24 _ _ (1650061 / 100000) (103129 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14668032 :
    ThetaLowerSegment 14668032 14676224 (1466260559131 / 100000) (1467065816227 / 100000) := by
  exact
    packedTile4096 14668032 14676224 10 488 3829 24 _ _ (1650117 / 100000) (41253 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14676224 :
    ThetaLowerSegment 14676224 14684416 (1467065816227 / 100000) (1467943707731 / 100000) := by
  exact
    packedTile4096 14676224 14684416 10 532 3830 24 _ _ (412543 / 25000) (66007 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14684416 :
    ThetaLowerSegment 14684416 14692608 (1467943707731 / 100000) (1468747368767 / 100000) := by
  exact
    packedTile4096 14684416 14692608 10 487 3832 24 _ _ (412557 / 25000) (1650231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14692608 :
    ThetaLowerSegment 14692608 14700800 (1468747368767 / 100000) (1469539505087 / 100000) := by
  exact
    packedTile4096 14692608 14700800 10 480 3833 24 _ _ (412571 / 25000) (1650287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14700800 :
    ThetaLowerSegment 14700800 14708992 (1469539505087 / 100000) (1470363024747 / 100000) := by
  exact
    packedTile4096 14700800 14708992 10 499 3834 24 _ _ (82517 / 5000) (1650343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14708992 :
    ThetaLowerSegment 14708992 14717184 (1470363024747 / 100000) (1471191523037 / 100000) := by
  exact
    packedTile4096 14708992 14717184 10 502 3835 24 _ _ (330079 / 20000) (825199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14717184 :
    ThetaLowerSegment 14717184 14725376 (1471191523037 / 100000) (736004248141 / 50000) := by
  exact
    packedTile4096 14717184 14725376 10 495 3836 24 _ _ (1650451 / 100000) (825227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14725376 :
    ThetaLowerSegment 14725376 14733568 (736004248141 / 50000) (184105456603 / 12500) := by
  exact
    packedTile4096 14725376 14733568 10 506 3837 24 _ _ (1650507 / 100000) (165051 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14733568 :
    ThetaLowerSegment 14733568 14741760 (184105456603 / 12500) (147365737989 / 10000) := by
  exact
    packedTile4096 14733568 14741760 10 493 3838 24 _ _ (825281 / 50000) (330113 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14741760 :
    ThetaLowerSegment 14741760 14749952 (147365737989 / 10000) (737236392591 / 50000) := by
  exact
    packedTile4096 14741760 14749952 10 494 3839 24 _ _ (825309 / 50000) (1650621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14749952 :
    ThetaLowerSegment 14749952 14758144 (737236392591 / 50000) (46103324236 / 3125) := by
  exact
    packedTile4096 14749952 14758144 10 505 3840 24 _ _ (825337 / 50000) (1650677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14758144 :
    ThetaLowerSegment 14758144 14766336 (46103324236 / 3125) (184513991413 / 12500) := by
  exact
    packedTile4096 14758144 14766336 10 488 3841 24 _ _ (1650729 / 100000) (412683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14766336 :
    ThetaLowerSegment 14766336 14774528 (184513991413 / 12500) (369247537231 / 25000) := by
  exact
    packedTile4096 14766336 14774528 10 532 3842 24 _ _ (330157 / 20000) (412697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14774528 :
    ThetaLowerSegment 14774528 14782720 (369247537231 / 25000) (369453066811 / 25000) := by
  exact
    packedTile4096 14774528 14782720 10 498 3843 24 _ _ (41271 / 2500) (1650843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14782720 :
    ThetaLowerSegment 14782720 14790912 (369453066811 / 25000) (1478642667429 / 100000) := by
  exact
    packedTile4096 14782720 14790912 10 503 3844 24 _ _ (330179 / 20000) (825449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14790912 :
    ThetaLowerSegment 14790912 14799104 (1478642667429 / 100000) (1479438425811 / 100000) := by
  exact
    packedTile4096 14790912 14799104 10 482 3845 24 _ _ (1650951 / 100000) (825477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14799104 :
    ThetaLowerSegment 14799104 14807296 (1479438425811 / 100000) (296055757573 / 20000) := by
  exact
    packedTile4096 14799104 14807296 10 509 3846 24 _ _ (825503 / 50000) (1651009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14807296 :
    ThetaLowerSegment 14807296 14815488 (296055757573 / 20000) (1481072948687 / 100000) := by
  exact
    packedTile4096 14807296 14815488 10 481 3848 24 _ _ (825531 / 50000) (330213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14815488 :
    ThetaLowerSegment 14815488 14823680 (1481072948687 / 100000) (740951730269 / 50000) := by
  exact
    packedTile4096 14815488 14823680 10 503 3849 24 _ _ (1651117 / 100000) (20639 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14823680 :
    ThetaLowerSegment 14823680 14831872 (740951730269 / 50000) (741354616237 / 50000) := by
  exact
    packedTile4096 14823680 14831872 10 488 3850 24 _ _ (412793 / 25000) (66047 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14831872 :
    ThetaLowerSegment 14831872 14840064 (741354616237 / 50000) (370884537107 / 25000) := by
  exact
    packedTile4096 14831872 14840064 10 502 3851 24 _ _ (1651227 / 100000) (165123 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14840064 :
    ThetaLowerSegment 14840064 14848256 (370884537107 / 25000) (742190151379 / 50000) := by
  exact
    packedTile4096 14840064 14848256 10 510 3852 24 _ _ (1651283 / 100000) (825643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14848256 :
    ThetaLowerSegment 14848256 14856448 (742190151379 / 50000) (742586472499 / 50000) := by
  exact
    packedTile4096 14848256 14856448 10 480 3853 24 _ _ (825669 / 50000) (1651341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14856448 :
    ThetaLowerSegment 14856448 14864640 (742586472499 / 50000) (148600524707 / 10000) := by
  exact
    packedTile4096 14856448 14864640 10 504 3854 24 _ _ (1651393 / 100000) (412849 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14864640 :
    ThetaLowerSegment 14864640 14872832 (148600524707 / 10000) (743408054019 / 50000) := by
  exact
    packedTile4096 14864640 14872832 10 491 3855 24 _ _ (206431 / 12500) (1651451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14872832 :
    ThetaLowerSegment 14872832 14881024 (743408054019 / 50000) (46488085578 / 3125) := by
  exact
    packedTile4096 14872832 14881024 10 486 3856 24 _ _ (1651503 / 100000) (825753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14881024 :
    ThetaLowerSegment 14881024 14889216 (46488085578 / 3125) (148839992543 / 10000) := by
  exact
    packedTile4096 14881024 14889216 10 473 3857 24 _ _ (825779 / 50000) (1651561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14889216 :
    ThetaLowerSegment 14889216 14897408 (148839992543 / 10000) (744616169191 / 50000) := by
  exact
    packedTile4096 14889216 14897408 10 504 3858 24 _ _ (1651613 / 100000) (51613 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14897408 :
    ThetaLowerSegment 14897408 14905600 (744616169191 / 50000) (745019176183 / 50000) := by
  exact
    packedTile4096 14897408 14905600 10 488 3859 24 _ _ (412917 / 25000) (1651671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14905600 :
    ThetaLowerSegment 14905600 14913792 (745019176183 / 50000) (1490839438021 / 100000) := by
  exact
    packedTile4096 14905600 14913792 10 485 3860 24 _ _ (1651723 / 100000) (825863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14913792 :
    ThetaLowerSegment 14913792 14921984 (1490839438021 / 100000) (1491663675243 / 100000) := by
  exact
    packedTile4096 14913792 14921984 10 499 3861 24 _ _ (825889 / 50000) (1651781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14921984 :
    ThetaLowerSegment 14921984 14930176 (1491663675243 / 100000) (746234058957 / 50000) := by
  exact
    packedTile4096 14921984 14930176 10 487 3862 24 _ _ (1651833 / 100000) (412959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14930176 :
    ThetaLowerSegment 14930176 14938368 (746234058957 / 50000) (149328084681 / 10000) := by
  exact
    packedTile4096 14930176 14938368 10 492 3863 24 _ _ (103243 / 6250) (1651891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14938368 :
    ThetaLowerSegment 14938368 14946560 (149328084681 / 10000) (186766243189 / 12500) := by
  exact
    packedTile4096 14938368 14946560 10 514 3865 24 _ _ (1651943 / 100000) (825973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14946560 :
    ThetaLowerSegment 14946560 14954752 (186766243189 / 12500) (373744768121 / 25000) := by
  exact
    packedTile4096 14946560 14954752 10 514 3866 24 _ _ (825999 / 50000) (1652001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14954752 :
    ThetaLowerSegment 14954752 14962944 (373744768121 / 25000) (186966757531 / 12500) := by
  exact
    packedTile4096 14954752 14962944 10 457 3867 24 _ _ (413013 / 25000) (330411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14962944 :
    ThetaLowerSegment 14962944 14971136 (186966757531 / 12500) (1496548548999 / 100000) := by
  exact
    packedTile4096 14962944 14971136 10 493 3868 24 _ _ (1652107 / 100000) (165211 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14971136 :
    ThetaLowerSegment 14971136 14979328 (1496548548999 / 100000) (1497356456217 / 100000) := by
  exact
    packedTile4096 14971136 14979328 10 489 3869 24 _ _ (826081 / 50000) (330433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14979328 :
    ThetaLowerSegment 14979328 14987520 (1497356456217 / 100000) (374538619257 / 25000) := by
  exact
    packedTile4096 14979328 14987520 10 483 3870 24 _ _ (1652217 / 100000) (82611 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14987520 :
    ThetaLowerSegment 14987520 14995712 (374538619257 / 25000) (374753414487 / 25000) := by
  exact
    packedTile4096 14987520 14995712 10 520 3871 24 _ _ (1652271 / 100000) (826137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell14995712 :
    ThetaLowerSegment 14995712 15003904 (374753414487 / 25000) (37495251977 / 2500) := by
  exact
    packedTile4096 14995712 15003904 10 482 3872 24 _ _ (826163 / 50000) (1652329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15003904 :
    ThetaLowerSegment 15003904 15012096 (37495251977 / 2500) (1500637921961 / 100000) := by
  exact
    packedTile4096 15003904 15012096 10 501 3873 24 _ _ (1652381 / 100000) (51637 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15012096 :
    ThetaLowerSegment 15012096 15020288 (1500637921961 / 100000) (375361490669 / 25000) := by
  exact
    packedTile4096 15012096 15020288 10 489 3874 24 _ _ (330487 / 20000) (826219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15020288 :
    ThetaLowerSegment 15020288 15028480 (375361490669 / 25000) (375569704409 / 25000) := by
  exact
    packedTile4096 15020288 15028480 10 504 3875 24 _ _ (165249 / 10000) (1652493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15028480 :
    ThetaLowerSegment 15028480 15036672 (375569704409 / 25000) (375773380457 / 25000) := by
  exact
    packedTile4096 15028480 15036672 10 493 3876 24 _ _ (51642 / 3125) (1652547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15036672 :
    ThetaLowerSegment 15036672 15044864 (375773380457 / 25000) (12031398233 / 800) := by
  exact
    packedTile4096 15036672 15044864 10 503 3877 24 _ _ (1652599 / 100000) (826301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15044864 :
    ThetaLowerSegment 15044864 15053056 (12031398233 / 800) (37618571059 / 2500) := by
  exact
    packedTile4096 15044864 15053056 10 495 3878 24 _ _ (1652653 / 100000) (103291 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15053056 :
    ThetaLowerSegment 15053056 15061248 (37618571059 / 2500) (376391059559 / 25000) := by
  exact
    packedTile4096 15053056 15061248 10 497 3879 24 _ _ (413177 / 25000) (1652711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15061248 :
    ThetaLowerSegment 15061248 15069440 (376391059559 / 25000) (150636913333 / 10000) := by
  exact
    packedTile4096 15061248 15069440 10 487 3880 24 _ _ (826381 / 50000) (330553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15069440 :
    ThetaLowerSegment 15069440 15077632 (150636913333 / 10000) (753599423481 / 50000) := by
  exact
    packedTile4096 15069440 15077632 10 502 3881 24 _ _ (103301 / 6250) (1652819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15077632 :
    ThetaLowerSegment 15077632 15085824 (753599423481 / 50000) (1507990572171 / 100000) := by
  exact
    packedTile4096 15077632 15085824 10 479 3882 24 _ _ (1652871 / 100000) (826437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15085824 :
    ThetaLowerSegment 15085824 15094016 (1507990572171 / 100000) (1508820340521 / 100000) := by
  exact
    packedTile4096 15085824 15094016 10 502 3884 24 _ _ (66117 / 4000) (51654 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15094016 :
    ThetaLowerSegment 15094016 15102208 (1508820340521 / 100000) (1509650135979 / 100000) := by
  exact
    packedTile4096 15094016 15102208 10 502 3885 24 _ _ (1652979 / 100000) (826491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15102208 :
    ThetaLowerSegment 15102208 15110400 (1509650135979 / 100000) (1510438633197 / 100000) := by
  exact
    packedTile4096 15102208 15110400 10 477 3886 24 _ _ (826517 / 50000) (1653037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15110400 :
    ThetaLowerSegment 15110400 15118592 (1510438633197 / 100000) (302251712969 / 20000) := by
  exact
    packedTile4096 15110400 15118592 10 496 3887 24 _ _ (51659 / 3125) (1653091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15118592 :
    ThetaLowerSegment 15118592 15126784 (302251712969 / 20000) (302417027169 / 20000) := by
  exact
    packedTile4096 15118592 15126784 10 500 3888 24 _ _ (826571 / 50000) (330629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15126784 :
    ThetaLowerSegment 15126784 15134976 (302417027169 / 20000) (1512905121061 / 100000) := by
  exact
    packedTile4096 15126784 15134976 10 496 3889 24 _ _ (413299 / 25000) (1653199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15134976 :
    ThetaLowerSegment 15134976 15143168 (1512905121061 / 100000) (1513698681061 / 100000) := by
  exact
    packedTile4096 15134976 15143168 10 480 3890 24 _ _ (6613 / 400) (1653253 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15143168 :
    ThetaLowerSegment 15143168 15151360 (1513698681061 / 100000) (1514528640171 / 100000) := by
  exact
    packedTile4096 15143168 15151360 10 502 3891 24 _ _ (330661 / 20000) (413327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15151360 :
    ThetaLowerSegment 15151360 15159552 (1514528640171 / 100000) (378836763219 / 25000) := by
  exact
    packedTile4096 15151360 15159552 10 495 3892 24 _ _ (1653359 / 100000) (826681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15159552 :
    ThetaLowerSegment 15159552 15167744 (378836763219 / 25000) (379051706909 / 25000) := by
  exact
    packedTile4096 15159552 15167744 10 520 3893 24 _ _ (1653413 / 100000) (206677 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15167744 :
    ThetaLowerSegment 15167744 15175936 (379051706909 / 25000) (1517021986867 / 100000) := by
  exact
    packedTile4096 15167744 15175936 10 493 3894 24 _ _ (1653467 / 100000) (165347 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15175936 :
    ThetaLowerSegment 15175936 15184128 (1517021986867 / 100000) (758903704671 / 50000) := by
  exact
    packedTile4096 15175936 15184128 10 475 3895 24 _ _ (1653521 / 100000) (413381 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15184128 :
    ThetaLowerSegment 15184128 15192320 (758903704671 / 50000) (1518629236117 / 100000) := by
  exact
    packedTile4096 15184128 15192320 10 497 3896 24 _ _ (66143 / 4000) (826789 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15192320 :
    ThetaLowerSegment 15192320 15200512 (1518629236117 / 100000) (1519419670779 / 100000) := by
  exact
    packedTile4096 15192320 15200512 10 478 3897 24 _ _ (1653629 / 100000) (51676 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15200512 :
    ThetaLowerSegment 15200512 15208704 (1519419670779 / 100000) (1520248165461 / 100000) := by
  exact
    packedTile4096 15200512 15208704 10 501 3898 24 _ _ (826841 / 50000) (330737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15208704 :
    ThetaLowerSegment 15208704 15216896 (1520248165461 / 100000) (1521051881157 / 100000) := by
  exact
    packedTile4096 15208704 15216896 10 486 3899 24 _ _ (206717 / 12500) (1653739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15216896 :
    ThetaLowerSegment 15216896 15225088 (1521051881157 / 100000) (1521865545837 / 100000) := by
  exact
    packedTile4096 15216896 15225088 10 492 3900 24 _ _ (165379 / 10000) (1653793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15225088 :
    ThetaLowerSegment 15225088 15233280 (1521865545837 / 100000) (304542462793 / 20000) := by
  exact
    packedTile4096 15225088 15233280 10 512 3901 24 _ _ (413461 / 25000) (1653847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15233280 :
    ThetaLowerSegment 15233280 15241472 (304542462793 / 20000) (1523526031781 / 100000) := by
  exact
    packedTile4096 15233280 15241472 10 492 3902 24 _ _ (826949 / 50000) (1653901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15241472 :
    ThetaLowerSegment 15241472 15249664 (1523526031781 / 100000) (304871263137 / 20000) := by
  exact
    packedTile4096 15241472 15249664 10 502 3904 24 _ _ (51686 / 3125) (330791 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15249664 :
    ThetaLowerSegment 15249664 15257856 (304871263137 / 20000) (305039971647 / 20000) := by
  exact
    packedTile4096 15249664 15257856 10 510 3905 24 _ _ (330801 / 20000) (206751 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15257856 :
    ThetaLowerSegment 15257856 15266048 (305039971647 / 20000) (763010962779 / 50000) := by
  exact
    packedTile4096 15257856 15266048 10 497 3906 24 _ _ (1654059 / 100000) (827031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15266048 :
    ThetaLowerSegment 15266048 15274240 (763010962779 / 50000) (381713072571 / 25000) := by
  exact
    packedTile4096 15266048 15274240 10 502 3907 24 _ _ (1654113 / 100000) (413529 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15274240 :
    ThetaLowerSegment 15274240 15282432 (381713072571 / 25000) (38192232457 / 2500) := by
  exact
    packedTile4096 15274240 15282432 10 506 3908 24 _ _ (827083 / 50000) (1654169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15282432 :
    ThetaLowerSegment 15282432 15290624 (38192232457 / 2500) (38212248519 / 2500) := by
  exact
    packedTile4096 15282432 15290624 10 484 3909 24 _ _ (82711 / 5000) (1654223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15290624 :
    ThetaLowerSegment 15290624 15298816 (38212248519 / 2500) (764652748921 / 50000) := by
  exact
    packedTile4096 15290624 15298816 10 493 3910 24 _ _ (827137 / 50000) (1654277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15298816 :
    ThetaLowerSegment 15298816 15307008 (764652748921 / 50000) (1530127698361 / 100000) := by
  exact
    packedTile4096 15298816 15307008 10 497 3911 24 _ _ (1654327 / 100000) (165433 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15307008 :
    ThetaLowerSegment 15307008 15315200 (1530127698361 / 100000) (765474962859 / 50000) := by
  exact
    packedTile4096 15307008 15315200 10 497 3912 24 _ _ (1654381 / 100000) (103399 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15315200 :
    ThetaLowerSegment 15315200 15323392 (765474962859 / 50000) (19147069521 / 1250) := by
  exact
    packedTile4096 15315200 15323392 10 493 3913 24 _ _ (827217 / 50000) (1654437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15323392 :
    ThetaLowerSegment 15323392 15331584 (19147069521 / 1250) (95786636733 / 6250) := by
  exact
    packedTile4096 15323392 15331584 10 496 3914 24 _ _ (206811 / 12500) (1654491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15331584 :
    ThetaLowerSegment 15331584 15339776 (95786636733 / 6250) (383346746393 / 25000) := by
  exact
    packedTile4096 15331584 15339776 10 484 3915 24 _ _ (1654541 / 100000) (103409 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15339776 :
    ThetaLowerSegment 15339776 15347968 (383346746393 / 25000) (153422586473 / 10000) := by
  exact
    packedTile4096 15339776 15347968 10 507 3916 24 _ _ (827297 / 50000) (1654597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15347968 :
    ThetaLowerSegment 15347968 15356160 (153422586473 / 10000) (153505318873 / 10000) := by
  exact
    packedTile4096 15347968 15356160 10 500 3917 24 _ _ (206831 / 12500) (1654651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15356160 :
    ThetaLowerSegment 15356160 15364352 (153505318873 / 10000) (383972616859 / 25000) := by
  exact
    packedTile4096 15356160 15364352 10 506 3918 24 _ _ (1654701 / 100000) (103419 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15364352 :
    ThetaLowerSegment 15364352 15372544 (383972616859 / 25000) (384164568439 / 25000) := by
  exact
    packedTile4096 15364352 15372544 10 464 3919 24 _ _ (330951 / 20000) (827379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15372544 :
    ThetaLowerSegment 15372544 15380736 (384164568439 / 25000) (384365213909 / 25000) := by
  exact
    packedTile4096 15372544 15380736 10 485 3920 24 _ _ (206851 / 12500) (1654811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15380736 :
    ThetaLowerSegment 15380736 15388928 (384365213909 / 25000) (769132559041 / 50000) := by
  exact
    packedTile4096 15380736 15388928 10 486 3921 24 _ _ (1654861 / 100000) (103429 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15388928 :
    ThetaLowerSegment 15388928 15397120 (769132559041 / 50000) (384765282929 / 25000) := by
  exact
    packedTile4096 15388928 15397120 10 481 3922 24 _ _ (827457 / 50000) (1654917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15397120 :
    ThetaLowerSegment 15397120 15405312 (384765282929 / 25000) (76993024063 / 5000) := by
  exact
    packedTile4096 15397120 15405312 10 483 3923 24 _ _ (206871 / 12500) (1654971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15405312 :
    ThetaLowerSegment 15405312 15413504 (76993024063 / 5000) (770332410733 / 50000) := by
  exact
    packedTile4096 15405312 15413504 10 486 3924 24 _ _ (1655021 / 100000) (103439 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15413504 :
    ThetaLowerSegment 15413504 15421696 (770332410733 / 50000) (770756109677 / 50000) := by
  exact
    packedTile4096 15413504 15421696 10 512 3926 24 _ _ (827537 / 50000) (1655077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15421696 :
    ThetaLowerSegment 15421696 15429888 (770756109677 / 50000) (771150029903 / 50000) := by
  exact
    packedTile4096 15421696 15429888 10 476 3927 24 _ _ (1655127 / 100000) (165513 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15429888 :
    ThetaLowerSegment 15429888 15438080 (771150029903 / 50000) (771556376593 / 50000) := by
  exact
    packedTile4096 15429888 15438080 10 491 3928 24 _ _ (82759 / 5000) (1655183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15438080 :
    ThetaLowerSegment 15438080 15446272 (771556376593 / 50000) (96495652393 / 6250) := by
  exact
    packedTile4096 15438080 15446272 10 494 3929 24 _ _ (1655233 / 100000) (413809 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15446272 :
    ThetaLowerSegment 15446272 15454464 (96495652393 / 6250) (48273069308 / 3125) := by
  exact
    packedTile4096 15446272 15454464 10 488 3930 24 _ _ (827643 / 50000) (1655289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15454464 :
    ThetaLowerSegment 15454464 15462656 (48273069308 / 3125) (1545564232017 / 100000) := by
  exact
    packedTile4096 15454464 15462656 10 499 3931 24 _ _ (1655339 / 100000) (827671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15462656 :
    ThetaLowerSegment 15462656 15470848 (1545564232017 / 100000) (309273088349 / 20000) := by
  exact
    packedTile4096 15462656 15470848 10 484 3932 24 _ _ (51731 / 3125) (331079 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15470848 :
    ThetaLowerSegment 15470848 15479040 (309273088349 / 20000) (38680118809 / 2500) := by
  exact
    packedTile4096 15470848 15479040 10 507 3933 24 _ _ (331089 / 20000) (206931 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15479040 :
    ThetaLowerSegment 15479040 15487232 (38680118809 / 2500) (77400797319 / 5000) := by
  exact
    packedTile4096 15479040 15487232 10 490 3934 24 _ _ (827749 / 50000) (1655501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15487232 :
    ThetaLowerSegment 15487232 15495424 (77400797319 / 5000) (1548828821921 / 100000) := by
  exact
    packedTile4096 15487232 15495424 10 491 3935 24 _ _ (1655551 / 100000) (827777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15495424 :
    ThetaLowerSegment 15495424 15503616 (1548828821921 / 100000) (1549681457981 / 100000) := by
  exact
    packedTile4096 15495424 15503616 10 515 3936 24 _ _ (413901 / 25000) (1655607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15503616 :
    ThetaLowerSegment 15503616 15511808 (1549681457981 / 100000) (1550522531737 / 100000) := by
  exact
    packedTile4096 15503616 15511808 10 508 3937 24 _ _ (1655657 / 100000) (82783 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15511808 :
    ThetaLowerSegment 15511808 15520000 (1550522531737 / 100000) (1551353698157 / 100000) := by
  exact
    packedTile4096 15511808 15520000 10 502 3938 24 _ _ (165571 / 10000) (1655713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15520000 :
    ThetaLowerSegment 15520000 15528192 (1551353698157 / 100000) (776096584999 / 50000) := by
  exact
    packedTile4096 15520000 15528192 10 507 3939 24 _ _ (1655763 / 100000) (827883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15528192 :
    ThetaLowerSegment 15528192 15536384 (776096584999 / 50000) (1553022733313 / 100000) := by
  exact
    packedTile4096 15528192 15536384 10 501 3940 24 _ _ (331163 / 20000) (827909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15536384 :
    ThetaLowerSegment 15536384 15544576 (1553022733313 / 100000) (1553822517557 / 100000) := by
  exact
    packedTile4096 15536384 15544576 10 483 3941 24 _ _ (413967 / 25000) (1655871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15544576 :
    ThetaLowerSegment 15544576 15552768 (1553822517557 / 100000) (48583189672 / 3125) := by
  exact
    packedTile4096 15544576 15552768 10 507 3942 24 _ _ (1655921 / 100000) (413981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15552768 :
    ThetaLowerSegment 15552768 15560960 (48583189672 / 3125) (777753307867 / 50000) := by
  exact
    packedTile4096 15552768 15560960 10 510 3943 24 _ _ (1655973 / 100000) (206997 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15560960 :
    ThetaLowerSegment 15560960 15569152 (777753307867 / 50000) (389083243177 / 25000) := by
  exact
    packedTile4096 15560960 15569152 10 499 3944 24 _ _ (828013 / 50000) (1656029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15569152 :
    ThetaLowerSegment 15569152 15577344 (389083243177 / 25000) (778565601393 / 50000) := by
  exact
    packedTile4096 15569152 15577344 10 482 3945 24 _ _ (1656079 / 100000) (828041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15577344 :
    ThetaLowerSegment 15577344 15585536 (778565601393 / 50000) (1557944363107 / 100000) := by
  exact
    packedTile4096 15577344 15585536 10 491 3946 24 _ _ (1656131 / 100000) (828067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15585536 :
    ThetaLowerSegment 15585536 15593728 (1557944363107 / 100000) (1558820484443 / 100000) := by
  exact
    packedTile4096 15585536 15593728 10 529 3947 24 _ _ (207023 / 12500) (1656187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15593728 :
    ThetaLowerSegment 15593728 15601920 (1558820484443 / 100000) (1559605540307 / 100000) := by
  exact
    packedTile4096 15593728 15601920 10 474 3948 24 _ _ (414059 / 25000) (1656239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15601920 :
    ThetaLowerSegment 15601920 15610112 (1559605540307 / 100000) (195054417637 / 12500) := by
  exact
    packedTile4096 15601920 15610112 10 501 3949 24 _ _ (1656289 / 100000) (414073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15610112 :
    ThetaLowerSegment 15610112 15618304 (195054417637 / 12500) (780633412139 / 50000) := by
  exact
    packedTile4096 15610112 15618304 10 502 3950 24 _ _ (1656341 / 100000) (207043 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15618304 :
    ThetaLowerSegment 15618304 15626496 (780633412139 / 50000) (19525628733 / 1250) := by
  exact
    packedTile4096 15618304 15626496 10 473 3952 24 _ _ (828197 / 50000) (1656397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15626496 :
    ThetaLowerSegment 15626496 15634688 (19525628733 / 1250) (97681149937 / 6250) := by
  exact
    packedTile4096 15626496 15634688 10 512 3953 24 _ _ (828223 / 50000) (1656449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15634688 :
    ThetaLowerSegment 15634688 15642880 (97681149937 / 6250) (312741022801 / 20000) := by
  exact
    packedTile4096 15634688 15642880 10 487 3954 24 _ _ (1656499 / 100000) (828251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15642880 :
    ThetaLowerSegment 15642880 15651072 (312741022801 / 20000) (1564503571587 / 100000) := by
  exact
    packedTile4096 15642880 15651072 10 482 3955 24 _ _ (1656551 / 100000) (828277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15651072 :
    ThetaLowerSegment 15651072 15659264 (1564503571587 / 100000) (1565345125911 / 100000) := by
  exact
    packedTile4096 15651072 15659264 10 508 3956 24 _ _ (1656603 / 100000) (828303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15659264 :
    ThetaLowerSegment 15659264 15667456 (1565345125911 / 100000) (12529639443 / 800) := by
  exact
    packedTile4096 15659264 15667456 10 519 3957 24 _ _ (103541 / 6250) (1656659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15667456 :
    ThetaLowerSegment 15667456 15675648 (12529639443 / 800) (1567020030711 / 100000) := by
  exact
    packedTile4096 15667456 15675648 10 492 3958 24 _ _ (414177 / 25000) (1656711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15675648 :
    ThetaLowerSegment 15675648 15683840 (1567020030711 / 100000) (1567802021431 / 100000) := by
  exact
    packedTile4096 15675648 15683840 10 472 3959 24 _ _ (41419 / 2500) (1656763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15683840 :
    ThetaLowerSegment 15683840 15692032 (1567802021431 / 100000) (392159677999 / 25000) := by
  exact
    packedTile4096 15683840 15692032 10 505 3960 24 _ _ (1656813 / 100000) (103551 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15692032 :
    ThetaLowerSegment 15692032 15700224 (392159677999 / 25000) (1569445605251 / 100000) := by
  exact
    packedTile4096 15692032 15700224 10 487 3961 24 _ _ (331373 / 20000) (414217 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15700224 :
    ThetaLowerSegment 15700224 15708416 (1569445605251 / 100000) (785129575749 / 50000) := by
  exact
    packedTile4096 15700224 15708416 10 491 3962 24 _ _ (1656917 / 100000) (41423 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15708416 :
    ThetaLowerSegment 15708416 15716608 (785129575749 / 50000) (1571119118409 / 100000) := by
  exact
    packedTile4096 15708416 15716608 10 519 3963 24 _ _ (1656969 / 100000) (414243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15716608 :
    ThetaLowerSegment 15716608 15724800 (1571119118409 / 100000) (1571917802531 / 100000) := by
  exact
    packedTile4096 15716608 15724800 10 482 3964 24 _ _ (1657021 / 100000) (51782 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15724800 :
    ThetaLowerSegment 15724800 15732992 (1571917802531 / 100000) (786352456103 / 50000) := by
  exact
    packedTile4096 15724800 15732992 10 475 3965 24 _ _ (1657073 / 100000) (414269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15732992 :
    ThetaLowerSegment 15732992 15741184 (786352456103 / 50000) (393388754461 / 25000) := by
  exact
    packedTile4096 15732992 15741184 10 513 3966 24 _ _ (828563 / 50000) (1657129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15741184 :
    ThetaLowerSegment 15741184 15749376 (393388754461 / 25000) (196795879383 / 12500) := by
  exact
    packedTile4096 15741184 15749376 10 490 3967 24 _ _ (828589 / 50000) (1657181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15749376 :
    ThetaLowerSegment 15749376 15757568 (196795879383 / 12500) (196896970413 / 12500) := by
  exact
    packedTile4096 15749376 15757568 10 488 3968 24 _ _ (165723 / 10000) (1657233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15757568 :
    ThetaLowerSegment 15757568 15765760 (196896970413 / 12500) (78800054487 / 5000) := by
  exact
    packedTile4096 15757568 15765760 10 498 3969 24 _ _ (828641 / 50000) (331457 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15765760 :
    ThetaLowerSegment 15765760 15773952 (78800054487 / 5000) (788399133697 / 50000) := by
  exact
    packedTile4096 15765760 15773952 10 481 3970 24 _ _ (828667 / 50000) (1657337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15773952 :
    ThetaLowerSegment 15773952 15782144 (788399133697 / 50000) (788803535881 / 50000) := by
  exact
    packedTile4096 15773952 15782144 10 488 3971 24 _ _ (828693 / 50000) (1657389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15782144 :
    ThetaLowerSegment 15782144 15790336 (788803535881 / 50000) (394604803973 / 25000) := by
  exact
    packedTile4096 15782144 15790336 10 490 3972 24 _ _ (1657437 / 100000) (10359 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15790336 :
    ThetaLowerSegment 15790336 15798528 (394604803973 / 25000) (1579223098057 / 100000) := by
  exact
    packedTile4096 15790336 15798528 10 485 3973 24 _ _ (1657489 / 100000) (414373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15798528 :
    ThetaLowerSegment 15798528 15806720 (1579223098057 / 100000) (395007580131 / 25000) := by
  exact
    packedTile4096 15798528 15806720 10 487 3974 24 _ _ (1657541 / 100000) (207193 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15806720 :
    ThetaLowerSegment 15806720 15814912 (395007580131 / 25000) (49401847407 / 3125) := by
  exact
    packedTile4096 15806720 15814912 10 500 3975 24 _ _ (1657593 / 100000) (414399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15814912 :
    ThetaLowerSegment 15814912 15823104 (49401847407 / 3125) (395415354301 / 25000) := by
  exact
    packedTile4096 15814912 15823104 10 484 3976 24 _ _ (331529 / 20000) (103603 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15823104 :
    ThetaLowerSegment 15823104 15831296 (395415354301 / 25000) (19781294091 / 1250) := by
  exact
    packedTile4096 15823104 15831296 10 508 3977 24 _ _ (1657697 / 100000) (16577 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15831296 :
    ThetaLowerSegment 15831296 15839488 (19781294091 / 1250) (395831857009 / 25000) := by
  exact
    packedTile4096 15831296 15839488 10 497 3978 24 _ _ (414437 / 25000) (1657751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15839488 :
    ThetaLowerSegment 15839488 15847680 (395831857009 / 25000) (396039496459 / 25000) := by
  exact
    packedTile4096 15839488 15847680 10 501 3979 24 _ _ (8289 / 500) (1657803 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15847680 :
    ThetaLowerSegment 15847680 15855872 (396039496459 / 25000) (15850399631 / 1000) := by
  exact
    packedTile4096 15847680 15855872 10 532 3980 24 _ _ (414463 / 25000) (331571 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15855872 :
    ThetaLowerSegment 15855872 15864064 (15850399631 / 1000) (396466814299 / 25000) := by
  exact
    packedTile4096 15855872 15864064 10 499 3981 24 _ _ (103619 / 6250) (1657907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15864064 :
    ThetaLowerSegment 15864064 15872256 (396466814299 / 25000) (1586684629011 / 100000) := by
  exact
    packedTile4096 15864064 15872256 10 493 3982 24 _ _ (331591 / 20000) (828979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15872256 :
    ThetaLowerSegment 15872256 15880448 (1586684629011 / 100000) (793764277287 / 50000) := by
  exact
    packedTile4096 15872256 15880448 10 509 3984 24 _ _ (1658007 / 100000) (165801 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15880448 :
    ThetaLowerSegment 15880448 15888640 (793764277287 / 50000) (99271623573 / 6250) := by
  exact
    packedTile4096 15880448 15888640 10 493 3985 24 _ _ (829029 / 50000) (1658061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15888640 :
    ThetaLowerSegment 15888640 15896832 (99271623573 / 6250) (397284638437 / 25000) := by
  exact
    packedTile4096 15888640 15896832 10 478 3986 24 _ _ (165811 / 10000) (1658113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15896832 :
    ThetaLowerSegment 15896832 15905024 (397284638437 / 25000) (794979671969 / 50000) := by
  exact
    packedTile4096 15896832 15905024 10 495 3987 24 _ _ (829081 / 50000) (331633 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15905024 :
    ThetaLowerSegment 15905024 15913216 (794979671969 / 50000) (159076191903 / 10000) := by
  exact
    packedTile4096 15905024 15913216 10 484 3988 24 _ _ (1658213 / 100000) (207277 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15913216 :
    ThetaLowerSegment 15913216 15921408 (159076191903 / 10000) (159158441847 / 10000) := by
  exact
    packedTile4096 15913216 15921408 10 496 3989 24 _ _ (331653 / 20000) (414567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15921408 :
    ThetaLowerSegment 15921408 15929600 (159158441847 / 10000) (796207617393 / 50000) := by
  exact
    packedTile4096 15921408 15929600 10 501 3990 24 _ _ (414579 / 25000) (1658319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15929600 :
    ThetaLowerSegment 15929600 15937792 (796207617393 / 50000) (318647888637 / 20000) := by
  exact
    packedTile4096 15929600 15937792 10 497 3991 24 _ _ (1658367 / 100000) (165837 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15937792 :
    ThetaLowerSegment 15937792 15945984 (318647888637 / 20000) (398512602519 / 25000) := by
  exact
    packedTile4096 15937792 15945984 10 489 3992 24 _ _ (1658419 / 100000) (829211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15945984 :
    ThetaLowerSegment 15945984 15954176 (398512602519 / 25000) (797430700953 / 50000) := by
  exact
    packedTile4096 15945984 15954176 10 489 3993 24 _ _ (165847 / 10000) (1658473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15954176 :
    ThetaLowerSegment 15954176 15962368 (797430700953 / 50000) (398919763313 / 25000) := by
  exact
    packedTile4096 15954176 15962368 10 493 3994 24 _ _ (829261 / 50000) (66341 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15962368 :
    ThetaLowerSegment 15962368 15970560 (398919763313 / 25000) (159651829119 / 10000) := by
  exact
    packedTile4096 15962368 15970560 10 506 3995 24 _ _ (1658573 / 100000) (103661 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15970560 :
    ThetaLowerSegment 15970560 15978752 (159651829119 / 10000) (159732272383 / 10000) := by
  exact
    packedTile4096 15970560 15978752 10 485 3996 24 _ _ (51832 / 3125) (1658627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15978752 :
    ThetaLowerSegment 15978752 15986944 (159732272383 / 10000) (799070225549 / 50000) := by
  exact
    packedTile4096 15978752 15986944 10 493 3997 24 _ _ (414669 / 25000) (1658679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15986944 :
    ThetaLowerSegment 15986944 15995136 (799070225549 / 50000) (399739965559 / 25000) := by
  exact
    packedTile4096 15986944 15995136 10 494 3998 24 _ _ (1658727 / 100000) (165873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell15995136 :
    ThetaLowerSegment 15995136 16003328 (399739965559 / 25000) (799885502339 / 50000) := by
  exact
    packedTile4096 15995136 16003328 10 489 3999 24 _ _ (829389 / 50000) (1658781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16003328 :
    ThetaLowerSegment 16003328 16011520 (799885502339 / 50000) (200072978861 / 12500) := by
  exact
    packedTile4096 16003328 16011520 10 490 4000 24 _ _ (1658829 / 100000) (103677 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16011520 :
    ThetaLowerSegment 16011520 16019712 (200072978861 / 12500) (200174792621 / 12500) := by
  exact
    packedTile4096 16011520 16019712 10 491 4001 24 _ _ (10368 / 625) (1658883 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16019712 :
    ThetaLowerSegment 16019712 16027904 (200174792621 / 12500) (100139030569 / 6250) := by
  exact
    packedTile4096 16019712 16027904 10 498 4002 24 _ _ (414733 / 25000) (331787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16027904 :
    ThetaLowerSegment 16027904 16036096 (100139030569 / 6250) (160305729857 / 10000) := by
  exact
    packedTile4096 16027904 16036096 10 502 4003 24 _ _ (1658983 / 100000) (829493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16036096 :
    ThetaLowerSegment 16036096 16044288 (160305729857 / 10000) (40096133493 / 2500) := by
  exact
    packedTile4096 16036096 16044288 10 475 4004 24 _ _ (829517 / 50000) (1659037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16044288 :
    ThetaLowerSegment 16044288 16052480 (40096133493 / 2500) (320931990091 / 20000) := by
  exact
    packedTile4096 16044288 16052480 10 491 4005 24 _ _ (331817 / 20000) (103693 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16052480 :
    ThetaLowerSegment 16052480 16060672 (320931990091 / 20000) (1605438085239 / 100000) := by
  exact
    packedTile4096 16052480 16060672 10 469 4006 24 _ _ (51848 / 3125) (1659139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16060672 :
    ThetaLowerSegment 16060672 16068864 (1605438085239 / 100000) (401571482449 / 25000) := by
  exact
    packedTile4096 16060672 16068864 10 511 4007 24 _ _ (1659187 / 100000) (165919 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16068864 :
    ThetaLowerSegment 16068864 16077056 (401571482449 / 25000) (803571877921 / 50000) := by
  exact
    packedTile4096 16068864 16077056 10 517 4008 24 _ _ (829619 / 50000) (1659241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16077056 :
    ThetaLowerSegment 16077056 16085248 (803571877921 / 50000) (401982564707 / 25000) := by
  exact
    packedTile4096 16077056 16085248 10 474 4009 24 _ _ (1659289 / 100000) (414823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16085248 :
    ThetaLowerSegment 16085248 16093440 (401982564707 / 25000) (402187493197 / 25000) := by
  exact
    packedTile4096 16085248 16093440 10 494 4010 24 _ _ (82967 / 5000) (1659343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16093440 :
    ThetaLowerSegment 16093440 16101632 (402187493197 / 25000) (1609578008897 / 100000) := by
  exact
    packedTile4096 16093440 16101632 10 499 4011 24 _ _ (1659391 / 100000) (829697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16101632 :
    ThetaLowerSegment 16101632 16109824 (1609578008897 / 100000) (1610357946637 / 100000) := by
  exact
    packedTile4096 16101632 16109824 10 470 4012 24 _ _ (829721 / 50000) (331889 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16109824 :
    ThetaLowerSegment 16109824 16118016 (1610357946637 / 100000) (1611184373653 / 100000) := by
  exact
    packedTile4096 16109824 16118016 10 498 4013 24 _ _ (414873 / 25000) (331899 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16118016 :
    ThetaLowerSegment 16118016 16126208 (1611184373653 / 100000) (806009561891 / 50000) := by
  exact
    packedTile4096 16118016 16126208 10 503 4014 24 _ _ (1659543 / 100000) (829773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16126208 :
    ThetaLowerSegment 16126208 16134400 (806009561891 / 50000) (806419481609 / 50000) := by
  exact
    packedTile4096 16126208 16134400 10 494 4015 24 _ _ (829797 / 50000) (1659597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16134400 :
    ThetaLowerSegment 16134400 16142592 (806419481609 / 50000) (806831073569 / 50000) := by
  exact
    packedTile4096 16134400 16142592 10 496 4016 24 _ _ (331929 / 20000) (51864 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16142592 :
    ThetaLowerSegment 16142592 16150784 (806831073569 / 50000) (807242678177 / 50000) := by
  exact
    packedTile4096 16142592 16150784 10 496 4017 24 _ _ (103731 / 6250) (1659699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16150784 :
    ThetaLowerSegment 16150784 16158976 (807242678177 / 50000) (807632718487 / 50000) := by
  exact
    packedTile4096 16150784 16158976 10 470 4018 24 _ _ (829873 / 50000) (1659749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16158976 :
    ThetaLowerSegment 16158976 16167168 (807632718487 / 50000) (404021344173 / 25000) := by
  exact
    packedTile4096 16158976 16167168 10 494 4019 24 _ _ (1659797 / 100000) (8299 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16167168 :
    ThetaLowerSegment 16167168 16175360 (404021344173 / 25000) (404221770819 / 25000) := by
  exact
    packedTile4096 16167168 16175360 10 483 4020 24 _ _ (207481 / 12500) (1659851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16175360 :
    ThetaLowerSegment 16175360 16183552 (404221770819 / 25000) (404427598171 / 25000) := by
  exact
    packedTile4096 16175360 16183552 10 496 4021 24 _ _ (829949 / 50000) (1659901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16183552 :
    ThetaLowerSegment 16183552 16191744 (404427598171 / 25000) (1618515467949 / 100000) := by
  exact
    packedTile4096 16183552 16191744 10 485 4022 24 _ _ (1659949 / 100000) (103747 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16191744 :
    ThetaLowerSegment 16191744 16199936 (1618515467949 / 100000) (1619347127949 / 100000) := by
  exact
    packedTile4096 16191744 16199936 10 501 4023 24 _ _ (83 / 5) (1660003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16199936 :
    ThetaLowerSegment 16199936 16208128 (1619347127949 / 100000) (1620193753449 / 100000) := by
  exact
    packedTile4096 16199936 16208128 10 510 4024 24 _ _ (33201 / 2000) (1660053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16208128 :
    ThetaLowerSegment 16208128 16216320 (1620193753449 / 100000) (1621020483747 / 100000) := by
  exact
    packedTile4096 16208128 16216320 10 498 4025 24 _ _ (1660101 / 100000) (207513 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16216320 :
    ThetaLowerSegment 16216320 16224512 (1621020483747 / 100000) (1621837278039 / 100000) := by
  exact
    packedTile4096 16216320 16224512 10 492 4026 24 _ _ (1660151 / 100000) (830077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16224512 :
    ThetaLowerSegment 16224512 16232704 (1621837278039 / 100000) (1622657417827 / 100000) := by
  exact
    packedTile4096 16224512 16232704 10 494 4027 24 _ _ (830101 / 50000) (332041 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16232704 :
    ThetaLowerSegment 16232704 16240896 (1622657417827 / 100000) (1623500825843 / 100000) := by
  exact
    packedTile4096 16232704 16240896 10 508 4028 24 _ _ (415063 / 25000) (332051 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16240896 :
    ThetaLowerSegment 16240896 16249088 (1623500825843 / 100000) (1624311053707 / 100000) := by
  exact
    packedTile4096 16240896 16249088 10 488 4029 24 _ _ (1660303 / 100000) (830153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16249088 :
    ThetaLowerSegment 16249088 16257280 (1624311053707 / 100000) (1625127947383 / 100000) := by
  exact
    packedTile4096 16249088 16257280 10 492 4031 24 _ _ (1660353 / 100000) (415089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16257280 :
    ThetaLowerSegment 16257280 16265472 (1625127947383 / 100000) (65038193143 / 4000) := by
  exact
    packedTile4096 16257280 16265472 10 498 4032 24 _ _ (415101 / 25000) (1660407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16265472 :
    ThetaLowerSegment 16265472 16273664 (65038193143 / 4000) (1626791697391 / 100000) := by
  exact
    packedTile4096 16265472 16273664 10 504 4033 24 _ _ (830227 / 50000) (1660457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16273664 :
    ThetaLowerSegment 16273664 16281856 (1626791697391 / 100000) (325516419459 / 20000) := by
  exact
    packedTile4096 16273664 16281856 10 476 4034 24 _ _ (207563 / 12500) (1660507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16281856 :
    ThetaLowerSegment 16281856 16290048 (325516419459 / 20000) (325683803403 / 20000) := by
  exact
    packedTile4096 16281856 16290048 10 504 4035 24 _ _ (332111 / 20000) (830279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16290048 :
    ThetaLowerSegment 16290048 16298240 (325683803403 / 20000) (325849199661 / 20000) := by
  exact
    packedTile4096 16290048 16298240 10 498 4036 24 _ _ (332121 / 20000) (51894 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16298240 :
    ThetaLowerSegment 16298240 16306432 (325849199661 / 20000) (81503235061 / 5000) := by
  exact
    packedTile4096 16298240 16306432 10 493 4037 24 _ _ (332131 / 20000) (830329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16306432 :
    ThetaLowerSegment 16306432 16314624 (81503235061 / 5000) (203861466601 / 12500) := by
  exact
    packedTile4096 16306432 16314624 10 498 4038 24 _ _ (830353 / 50000) (1660709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16314624 :
    ThetaLowerSegment 16314624 16322816 (203861466601 / 12500) (407915996087 / 25000) := by
  exact
    packedTile4096 16314624 16322816 10 465 4039 24 _ _ (415189 / 25000) (1660759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16322816 :
    ThetaLowerSegment 16322816 16331008 (407915996087 / 25000) (163247279687 / 10000) := by
  exact
    packedTile4096 16322816 16331008 10 487 4040 24 _ _ (830403 / 50000) (1660809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16331008 :
    ThetaLowerSegment 16331008 16339200 (163247279687 / 10000) (816624208311 / 50000) := by
  exact
    packedTile4096 16331008 16339200 10 467 4041 24 _ _ (207607 / 12500) (1660859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16339200 :
    ThetaLowerSegment 16339200 16347392 (816624208311 / 50000) (817036112999 / 50000) := by
  exact
    packedTile4096 16339200 16347392 10 496 4042 24 _ _ (830453 / 50000) (1660909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16347392 :
    ThetaLowerSegment 16347392 16355584 (817036112999 / 50000) (32697788327 / 2000) := by
  exact
    packedTile4096 16347392 16355584 10 492 4043 24 _ _ (415239 / 25000) (1660959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16355584 :
    ThetaLowerSegment 16355584 16363776 (32697788327 / 2000) (817849993639 / 50000) := by
  exact
    packedTile4096 16355584 16363776 10 488 4044 24 _ _ (830503 / 50000) (1661009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16363776 :
    ThetaLowerSegment 16363776 16371968 (817849993639 / 50000) (204564238151 / 12500) := by
  exact
    packedTile4096 16363776 16371968 10 490 4045 24 _ _ (1661057 / 100000) (83053 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16371968 :
    ThetaLowerSegment 16371968 16380160 (204564238151 / 12500) (818670568247 / 50000) := by
  exact
    packedTile4096 16371968 16380160 10 498 4046 24 _ _ (1661107 / 100000) (166111 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16380160 :
    ThetaLowerSegment 16380160 16388352 (818670568247 / 50000) (1638156764581 / 100000) := by
  exact
    packedTile4096 16380160 16388352 10 491 4047 24 _ _ (1661157 / 100000) (41529 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16388352 :
    ThetaLowerSegment 16388352 16396544 (1638156764581 / 100000) (819492853437 / 50000) := by
  exact
    packedTile4096 16388352 16396544 10 499 4048 24 _ _ (1661207 / 100000) (166121 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16396544 :
    ThetaLowerSegment 16396544 16404736 (819492853437 / 50000) (409946608187 / 25000) := by
  exact
    packedTile4096 16396544 16404736 10 482 4049 24 _ _ (1661257 / 100000) (83063 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16404736 :
    ThetaLowerSegment 16404736 16412928 (409946608187 / 25000) (328123749511 / 20000) := by
  exact
    packedTile4096 16404736 16412928 10 501 4050 24 _ _ (1661307 / 100000) (166131 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16412928 :
    ThetaLowerSegment 16412928 16421120 (328123749511 / 20000) (328284901043 / 20000) := by
  exact
    packedTile4096 16412928 16421120 10 485 4051 24 _ _ (415339 / 25000) (1661359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16421120 :
    ThetaLowerSegment 16421120 16429312 (328284901043 / 20000) (1642291759147 / 100000) := by
  exact
    packedTile4096 16421120 16429312 10 522 4052 24 _ _ (830703 / 50000) (1661409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16429312 :
    ThetaLowerSegment 16429312 16437504 (1642291759147 / 100000) (1643130794427 / 100000) := by
  exact
    packedTile4096 16429312 16437504 10 505 4053 24 _ _ (103841 / 6250) (1661459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16437504 :
    ThetaLowerSegment 16437504 16445696 (1643130794427 / 100000) (1643943270861 / 100000) := by
  exact
    packedTile4096 16437504 16445696 10 489 4054 24 _ _ (830753 / 50000) (1661509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16445696 :
    ThetaLowerSegment 16445696 16453888 (1643943270861 / 100000) (328947831237 / 20000) := by
  exact
    packedTile4096 16445696 16453888 10 479 4055 24 _ _ (415389 / 25000) (1661559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16453888 :
    ThetaLowerSegment 16453888 16462080 (328947831237 / 20000) (329105683807 / 20000) := by
  exact
    packedTile4096 16453888 16462080 10 475 4056 24 _ _ (830803 / 50000) (1661609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16462080 :
    ThetaLowerSegment 16462080 16470272 (329105683807 / 20000) (1646355923723 / 100000) := by
  exact
    packedTile4096 16462080 16470272 10 498 4057 24 _ _ (207707 / 12500) (1661659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16470272 :
    ThetaLowerSegment 16470272 16478464 (1646355923723 / 100000) (1647206716683 / 100000) := by
  exact
    packedTile4096 16470272 16478464 10 512 4058 24 _ _ (332341 / 20000) (415427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16478464 :
    ThetaLowerSegment 16478464 16486656 (1647206716683 / 100000) (103000168583 / 6250) := by
  exact
    packedTile4096 16478464 16486656 10 479 4059 24 _ _ (332351 / 20000) (830879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16486656 :
    ThetaLowerSegment 16486656 16494848 (103000168583 / 6250) (206108354491 / 12500) := by
  exact
    packedTile4096 16486656 16494848 10 520 4060 24 _ _ (332361 / 20000) (103863 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16494848 :
    ThetaLowerSegment 16494848 16503040 (206108354491 / 12500) (412421947951 / 25000) := by
  exact
    packedTile4096 16494848 16503040 10 494 4061 24 _ _ (830927 / 50000) (1661857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16503040 :
    ThetaLowerSegment 16503040 16511232 (412421947951 / 25000) (16505170819 / 1000) := by
  exact
    packedTile4096 16503040 16511232 10 499 4062 24 _ _ (103869 / 6250) (1661907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16511232 :
    ThetaLowerSegment 16511232 16519424 (16505170819 / 1000) (825648269163 / 50000) := by
  exact
    packedTile4096 16511232 16519424 10 469 4063 24 _ _ (830977 / 50000) (1661957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16519424 :
    ThetaLowerSegment 16519424 16527616 (825648269163 / 50000) (826057121901 / 50000) := by
  exact
    packedTile4096 16519424 16527616 10 492 4064 24 _ _ (1662003 / 100000) (831003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16527616 :
    ThetaLowerSegment 16527616 16535808 (826057121901 / 50000) (826465986939 / 50000) := by
  exact
    packedTile4096 16527616 16535808 10 492 4065 24 _ _ (1662053 / 100000) (207757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16535808 :
    ThetaLowerSegment 16535808 16544000 (826465986939 / 50000) (826879850337 / 50000) := by
  exact
    packedTile4096 16535808 16544000 10 498 4066 24 _ _ (831051 / 50000) (332421 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16544000 :
    ThetaLowerSegment 16544000 16552192 (826879850337 / 50000) (165452096629 / 10000) := by
  exact
    packedTile4096 16544000 16552192 10 458 4067 24 _ _ (207769 / 12500) (332431 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16552192 :
    ThetaLowerSegment 16552192 16560384 (165452096629 / 10000) (1655333782579 / 100000) := by
  exact
    packedTile4096 16552192 16560384 10 489 4068 24 _ _ (1662201 / 100000) (415551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16560384 :
    ThetaLowerSegment 16560384 16568576 (1655333782579 / 100000) (828079960663 / 50000) := by
  exact
    packedTile4096 16560384 16568576 10 497 4069 24 _ _ (1662251 / 100000) (831127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16568576 :
    ThetaLowerSegment 16568576 16576768 (828079960663 / 50000) (828466445413 / 50000) := by
  exact
    packedTile4096 16568576 16576768 10 465 4070 24 _ _ (16623 / 1000) (1662303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16576768 :
    ThetaLowerSegment 16576768 16584960 (828466445413 / 50000) (414443925569 / 25000) := by
  exact
    packedTile4096 16576768 16584960 10 507 4071 24 _ _ (33247 / 2000) (1662353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16584960 :
    ThetaLowerSegment 16584960 16593152 (414443925569 / 25000) (1658638487357 / 100000) := by
  exact
    packedTile4096 16584960 16593152 10 519 4072 24 _ _ (1662399 / 100000) (831201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16593152 :
    ThetaLowerSegment 16593152 16601344 (1658638487357 / 100000) (414868674801 / 25000) := by
  exact
    packedTile4096 16593152 16601344 10 503 4073 24 _ _ (1662449 / 100000) (415613 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16601344 :
    ThetaLowerSegment 16601344 16609536 (414868674801 / 25000) (415078149549 / 25000) := by
  exact
    packedTile4096 16601344 16609536 10 504 4074 24 _ _ (831249 / 50000) (1662501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16609536 :
    ThetaLowerSegment 16609536 16617728 (415078149549 / 25000) (1661145534243 / 100000) := by
  exact
    packedTile4096 16609536 16617728 10 501 4075 24 _ _ (1662547 / 100000) (33251 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16617728 :
    ThetaLowerSegment 16617728 16625920 (1661145534243 / 100000) (1661946905997 / 100000) := by
  exact
    packedTile4096 16617728 16625920 10 482 4076 24 _ _ (1662597 / 100000) (8313 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16625920 :
    ThetaLowerSegment 16625920 16634112 (1661946905997 / 100000) (1662748301369 / 100000) := by
  exact
    packedTile4096 16625920 16634112 10 482 4077 24 _ _ (831323 / 50000) (1662649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16634112 :
    ThetaLowerSegment 16634112 16642304 (1662748301369 / 100000) (1663579648869 / 100000) := by
  exact
    packedTile4096 16634112 16642304 10 500 4078 24 _ _ (332539 / 20000) (831349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16642304 :
    ThetaLowerSegment 16642304 16650496 (1663579648869 / 100000) (1664407695381 / 100000) := by
  exact
    packedTile4096 16642304 16650496 10 498 4079 24 _ _ (207843 / 12500) (1662747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16650496 :
    ThetaLowerSegment 16650496 16658688 (1664407695381 / 100000) (66609630207 / 4000) := by
  exact
    packedTile4096 16650496 16658688 10 501 4080 24 _ _ (831397 / 50000) (1662797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16658688 :
    ThetaLowerSegment 16658688 16666880 (66609630207 / 4000) (333207783963 / 20000) := by
  exact
    packedTile4096 16658688 16666880 10 480 4081 24 _ _ (1662843 / 100000) (831423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16666880 :
    ThetaLowerSegment 16666880 16675072 (333207783963 / 20000) (1666850411111 / 100000) := by
  exact
    packedTile4096 16666880 16675072 10 488 4082 24 _ _ (415723 / 25000) (332579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16675072 :
    ThetaLowerSegment 16675072 16683264 (1666850411111 / 100000) (1667695185139 / 100000) := by
  exact
    packedTile4096 16675072 16683264 10 508 4083 24 _ _ (1662941 / 100000) (51967 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16683264 :
    ThetaLowerSegment 16683264 16691456 (1667695185139 / 100000) (1668528343129 / 100000) := by
  exact
    packedTile4096 16683264 16691456 10 501 4084 24 _ _ (166299 / 10000) (1662993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16691456 :
    ThetaLowerSegment 16691456 16699648 (1668528343129 / 100000) (834655817249 / 50000) := by
  exact
    packedTile4096 16691456 16699648 10 471 4085 24 _ _ (1663039 / 100000) (831521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16699648 :
    ThetaLowerSegment 16699648 16707840 (834655817249 / 50000) (835059116089 / 50000) := by
  exact
    packedTile4096 16699648 16707840 10 485 4086 24 _ _ (103943 / 6250) (1663091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16707840 :
    ThetaLowerSegment 16707840 16716032 (835059116089 / 50000) (1670944811267 / 100000) := by
  exact
    packedTile4096 16707840 16716032 10 497 4087 24 _ _ (1663137 / 100000) (83157 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16716032 :
    ThetaLowerSegment 16716032 16724224 (1670944811267 / 100000) (1671766425151 / 100000) := by
  exact
    packedTile4096 16716032 16724224 10 494 4088 24 _ _ (831593 / 50000) (1663189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16724224 :
    ThetaLowerSegment 16724224 16732416 (1671766425151 / 100000) (52268221048 / 3125) := by
  exact
    packedTile4096 16724224 16732416 10 491 4089 24 _ _ (332647 / 20000) (831619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16732416 :
    ThetaLowerSegment 16732416 16740608 (52268221048 / 3125) (418357421273 / 25000) := by
  exact
    packedTile4096 16732416 16740608 10 509 4090 24 _ _ (415821 / 25000) (1663287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16740608 :
    ThetaLowerSegment 16740608 16748800 (418357421273 / 25000) (837122359131 / 50000) := by
  exact
    packedTile4096 16740608 16748800 10 490 4091 24 _ _ (1663333 / 100000) (207917 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16748800 :
    ThetaLowerSegment 16748800 16756992 (837122359131 / 50000) (418771181543 / 25000) := by
  exact
    packedTile4096 16748800 16756992 10 505 4092 24 _ _ (831691 / 50000) (332677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16756992 :
    ThetaLowerSegment 16756992 16765184 (418771181543 / 25000) (167591311481 / 10000) := by
  exact
    packedTile4096 16756992 16765184 10 498 4093 24 _ _ (1663431 / 100000) (831717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16765184 :
    ThetaLowerSegment 16765184 16773376 (167591311481 / 10000) (167671823913 / 10000) := by
  exact
    packedTile4096 16765184 16773376 10 484 4094 24 _ _ (41587 / 2500) (1663483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16773376 :
    ThetaLowerSegment 16773376 16781568 (167671823913 / 10000) (1677548340101 / 100000) := by
  exact
    packedTile8192 16773376 16781568 10 499 4095 24 _ _ (1663529 / 100000) (415883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16781568 :
    ThetaLowerSegment 16781568 16789760 (1677548340101 / 100000) (67134073931 / 4000) := by
  exact
    packedTile8192 16781568 16789760 10 483 4096 24 _ _ (831789 / 50000) (1663581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16789760 :
    ThetaLowerSegment 16789760 16797952 (67134073931 / 4000) (1679235233681 / 100000) := by
  exact
    packedTile8192 16789760 16797952 10 531 4097 24 _ _ (831813 / 50000) (1663629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16797952 :
    ThetaLowerSegment 16797952 16806144 (1679235233681 / 100000) (420002210639 / 25000) := by
  exact
    packedTile8192 16797952 16806144 10 465 4098 24 _ _ (66547 / 4000) (831839 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16806144 :
    ThetaLowerSegment 16806144 16814336 (420002210639 / 25000) (420215999173 / 25000) := by
  exact
    packedTile8192 16806144 16814336 10 514 4099 24 _ _ (415931 / 25000) (1663727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16814336 :
    ThetaLowerSegment 16814336 16822528 (420215999173 / 25000) (420425634571 / 25000) := by
  exact
    packedTile8192 16814336 16822528 10 504 4100 24 _ _ (1663773 / 100000) (51993 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16822528 :
    ThetaLowerSegment 16822528 16830720 (420425634571 / 25000) (1682482870333 / 100000) := by
  exact
    packedTile8192 16822528 16830720 10 469 4101 24 _ _ (1663821 / 100000) (103989 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16830720 :
    ThetaLowerSegment 16830720 16838912 (1682482870333 / 100000) (1683324788553 / 100000) := by
  exact
    packedTile8192 16830720 16838912 10 506 4102 24 _ _ (166387 / 10000) (1663873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16838912 :
    ThetaLowerSegment 16838912 16847104 (1683324788553 / 100000) (67365471241 / 4000) := by
  exact
    packedTile8192 16838912 16847104 10 488 4103 24 _ _ (1663919 / 100000) (831961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16847104 :
    ThetaLowerSegment 16847104 16855296 (67365471241 / 4000) (336983769103 / 20000) := by
  exact
    packedTile8192 16847104 16855296 10 470 4104 24 _ _ (1663967 / 100000) (166397 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16855296 :
    ThetaLowerSegment 16855296 16863488 (336983769103 / 20000) (1685760837611 / 100000) := by
  exact
    packedTile8192 16855296 16863488 10 506 4105 24 _ _ (104001 / 6250) (1664019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16863488 :
    ThetaLowerSegment 16863488 16871680 (1685760837611 / 100000) (105410494321 / 6250) := by
  exact
    packedTile8192 16863488 16871680 10 485 4106 24 _ _ (332813 / 20000) (416017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16871680 :
    ThetaLowerSegment 16871680 16879872 (105410494321 / 6250) (421843334957 / 25000) := by
  exact
    packedTile8192 16871680 16879872 10 484 4107 24 _ _ (1664113 / 100000) (416029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16879872 :
    ThetaLowerSegment 16879872 16888064 (421843334957 / 25000) (422043034397 / 25000) := by
  exact
    packedTile8192 16879872 16888064 10 480 4108 24 _ _ (832081 / 50000) (332833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16888064 :
    ThetaLowerSegment 16888064 16896256 (422043034397 / 25000) (52781486594 / 3125) := by
  exact
    packedTile8192 16888064 16896256 10 502 4109 24 _ _ (166421 / 10000) (1664213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16896256 :
    ThetaLowerSegment 16896256 16904448 (52781486594 / 3125) (422459925127 / 25000) := by
  exact
    packedTile8192 16896256 16904448 10 500 4110 24 _ _ (1664259 / 100000) (832131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16904448 :
    ThetaLowerSegment 16904448 16912640 (422459925127 / 25000) (422662970581 / 25000) := by
  exact
    packedTile8192 16904448 16912640 10 488 4111 24 _ _ (1664307 / 100000) (166431 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16912640 :
    ThetaLowerSegment 16912640 16920832 (422662970581 / 25000) (422872679437 / 25000) := by
  exact
    packedTile8192 16912640 16920832 10 504 4112 24 _ _ (416089 / 25000) (1664359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16920832 :
    ThetaLowerSegment 16920832 16929024 (422872679437 / 25000) (423069911311 / 25000) := by
  exact
    packedTile8192 16920832 16929024 10 474 4113 24 _ _ (416101 / 25000) (1664407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16929024 :
    ThetaLowerSegment 16929024 16937216 (423069911311 / 25000) (846544284701 / 50000) := by
  exact
    packedTile8192 16929024 16937216 10 486 4114 24 _ _ (1664453 / 100000) (208057 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16937216 :
    ThetaLowerSegment 16937216 16945408 (846544284701 / 50000) (1693945787417 / 100000) := by
  exact
    packedTile8192 16937216 16945408 10 515 4115 24 _ _ (1664501 / 100000) (208063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16945408 :
    ThetaLowerSegment 16945408 16953600 (1693945787417 / 100000) (338959607301 / 20000) := by
  exact
    packedTile8192 16945408 16953600 10 512 4116 24 _ _ (1664549 / 100000) (208069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16953600 :
    ThetaLowerSegment 16953600 16961792 (338959607301 / 20000) (1695678608847 / 100000) := by
  exact
    packedTile8192 16953600 16961792 10 529 4117 24 _ _ (832299 / 50000) (1664601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16961792 :
    ThetaLowerSegment 16961792 16969984 (1695678608847 / 100000) (1696451004591 / 100000) := by
  exact
    packedTile8192 16961792 16969984 10 464 4118 24 _ _ (832323 / 50000) (1664649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16969984 :
    ThetaLowerSegment 16969984 16978176 (1696451004591 / 100000) (1697311651389 / 100000) := by
  exact
    packedTile8192 16969984 16978176 10 517 4119 24 _ _ (832347 / 50000) (1664697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16978176 :
    ThetaLowerSegment 16978176 16986368 (1697311651389 / 100000) (339626473839 / 20000) := by
  exact
    packedTile8192 16978176 16986368 10 493 4120 24 _ _ (832371 / 50000) (332949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16986368 :
    ThetaLowerSegment 16986368 16994560 (339626473839 / 20000) (212368722697 / 12500) := by
  exact
    packedTile8192 16986368 16994560 10 491 4121 24 _ _ (1664791 / 100000) (832397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell16994560 :
    ThetaLowerSegment 16994560 17002752 (212368722697 / 12500) (67990688701 / 4000) := by
  exact
    packedTile8192 16994560 17002752 10 491 4122 24 _ _ (1664839 / 100000) (832421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17002752 :
    ThetaLowerSegment 17002752 17010944 (67990688701 / 4000) (340123261979 / 20000) := by
  exact
    packedTile8192 17002752 17010944 10 510 4123 24 _ _ (1664887 / 100000) (166489 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17010944 :
    ThetaLowerSegment 17010944 17019136 (340123261979 / 20000) (68057151927 / 4000) := by
  exact
    packedTile8192 17010944 17019136 10 488 4124 24 _ _ (332987 / 20000) (832469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17019136 :
    ThetaLowerSegment 17019136 17027328 (68057151927 / 4000) (106391642789 / 6250) := by
  exact
    packedTile8192 17019136 17027328 10 503 4125 24 _ _ (1664983 / 100000) (832493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17027328 :
    ThetaLowerSegment 17027328 17035520 (106391642789 / 6250) (106442842523 / 6250) := by
  exact
    packedTile8192 17027328 17035520 10 492 4126 24 _ _ (208129 / 12500) (333007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17035520 :
    ThetaLowerSegment 17035520 17043712 (106442842523 / 6250) (212984965441 / 12500) := by
  exact
    packedTile8192 17035520 17043712 10 477 4127 24 _ _ (41627 / 2500) (1665083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17043712 :
    ThetaLowerSegment 17043712 17051904 (212984965441 / 12500) (53270541822 / 3125) := by
  exact
    packedTile8192 17043712 17051904 10 467 4128 24 _ _ (208141 / 12500) (1665131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17051904 :
    ThetaLowerSegment 17051904 17060096 (53270541822 / 3125) (213188946699 / 12500) := by
  exact
    packedTile8192 17051904 17060096 10 513 4129 24 _ _ (208147 / 12500) (1665179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17060096 :
    ThetaLowerSegment 17060096 17068288 (213188946699 / 12500) (106646407523 / 6250) := by
  exact
    packedTile8192 17060096 17068288 10 499 4130 24 _ _ (208153 / 12500) (1665227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17068288 :
    ThetaLowerSegment 17068288 17076480 (106646407523 / 6250) (213396686387 / 12500) := by
  exact
    packedTile8192 17068288 17076480 10 499 4131 24 _ _ (208159 / 12500) (66611 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17076480 :
    ThetaLowerSegment 17076480 17084672 (213396686387 / 12500) (213498270907 / 12500) := by
  exact
    packedTile8192 17076480 17084672 10 488 4132 24 _ _ (41633 / 2500) (1665323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17084672 :
    ThetaLowerSegment 17084672 17092864 (213498270907 / 12500) (106801698631 / 6250) := by
  exact
    packedTile8192 17084672 17092864 10 505 4133 24 _ _ (208171 / 12500) (1665371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17092864 :
    ThetaLowerSegment 17092864 17101056 (106801698631 / 6250) (213707693939 / 12500) := by
  exact
    packedTile8192 17092864 17101056 10 501 4134 24 _ _ (208177 / 12500) (1665419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17101056 :
    ThetaLowerSegment 17101056 17109248 (213707693939 / 12500) (106902249517 / 6250) := by
  exact
    packedTile8192 17101056 17109248 10 465 4135 24 _ _ (208183 / 12500) (1665467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17109248 :
    ThetaLowerSegment 17109248 17117440 (106902249517 / 6250) (427817186943 / 25000) := by
  exact
    packedTile8192 17109248 17117440 10 500 4136 24 _ _ (1665511 / 100000) (832757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17117440 :
    ThetaLowerSegment 17117440 17125632 (427817186943 / 25000) (856039104723 / 50000) := by
  exact
    packedTile8192 17117440 17125632 10 486 4137 24 _ _ (1665559 / 100000) (832781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17125632 :
    ThetaLowerSegment 17125632 17133824 (856039104723 / 50000) (214112627413 / 12500) := by
  exact
    packedTile8192 17125632 17133824 10 494 4138 24 _ _ (1665607 / 100000) (166561 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17133824 :
    ThetaLowerSegment 17133824 17142016 (214112627413 / 12500) (1713692205429 / 100000) := by
  exact
    packedTile8192 17133824 17142016 10 475 4139 24 _ _ (333131 / 20000) (832829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17142016 :
    ThetaLowerSegment 17142016 17150208 (1713692205429 / 100000) (857255032801 / 50000) := by
  exact
    packedTile8192 17142016 17150208 10 491 4140 24 _ _ (1665703 / 100000) (832853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17150208 :
    ThetaLowerSegment 17150208 17158400 (857255032801 / 50000) (1715317954837 / 100000) := by
  exact
    packedTile8192 17150208 17158400 10 485 4141 24 _ _ (1665751 / 100000) (832877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17158400 :
    ThetaLowerSegment 17158400 17166592 (1715317954837 / 100000) (1716097548301 / 100000) := by
  exact
    packedTile8192 17158400 17166592 10 468 4142 24 _ _ (832899 / 50000) (1665801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17166592 :
    ThetaLowerSegment 17166592 17174784 (1716097548301 / 100000) (1716908815303 / 100000) := by
  exact
    packedTile8192 17166592 17174784 10 487 4143 24 _ _ (832923 / 50000) (1665849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17174784 :
    ThetaLowerSegment 17174784 17182976 (1716908815303 / 100000) (1717708444423 / 100000) := by
  exact
    packedTile8192 17174784 17182976 10 480 4144 24 _ _ (832947 / 50000) (1665897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17182976 :
    ThetaLowerSegment 17182976 17191168 (1717708444423 / 100000) (429624108629 / 25000) := by
  exact
    packedTile8192 17182976 17191168 10 473 4145 24 _ _ (1665941 / 100000) (208243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17191168 :
    ThetaLowerSegment 17191168 17199360 (429624108629 / 25000) (859656384563 / 50000) := by
  exact
    packedTile8192 17191168 17199360 10 490 4146 24 _ _ (1665989 / 100000) (208249 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17199360 :
    ThetaLowerSegment 17199360 17207552 (859656384563 / 50000) (860069561739 / 50000) := by
  exact
    packedTile8192 17199360 17207552 10 496 4147 24 _ _ (1666037 / 100000) (41651 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17207552 :
    ThetaLowerSegment 17207552 17215744 (860069561739 / 50000) (860462757563 / 50000) := by
  exact
    packedTile8192 17207552 17215744 10 472 4148 24 _ _ (416521 / 25000) (1666087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17215744 :
    ThetaLowerSegment 17215744 17223936 (860462757563 / 50000) (860884288959 / 50000) := by
  exact
    packedTile8192 17215744 17223936 10 506 4149 24 _ _ (416533 / 25000) (333227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17223936 :
    ThetaLowerSegment 17223936 17232128 (860884288959 / 50000) (861293336149 / 50000) := by
  exact
    packedTile8192 17223936 17232128 10 491 4150 24 _ _ (83309 / 5000) (1666183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17232128 :
    ThetaLowerSegment 17232128 17240320 (861293336149 / 50000) (1723441446749 / 100000) := by
  exact
    packedTile8192 17232128 17240320 10 513 4151 24 _ _ (1666227 / 100000) (166623 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17240320 :
    ThetaLowerSegment 17240320 17248512 (1723441446749 / 100000) (215528699353 / 12500) := by
  exact
    packedTile8192 17240320 17248512 10 473 4152 24 _ _ (66651 / 4000) (833139 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17248512 :
    ThetaLowerSegment 17248512 17256704 (215528699353 / 12500) (862523879463 / 50000) := by
  exact
    packedTile8192 17248512 17256704 10 491 4153 24 _ _ (833161 / 50000) (66653 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17256704 :
    ThetaLowerSegment 17256704 17264896 (862523879463 / 50000) (862935472853 / 50000) := by
  exact
    packedTile8192 17256704 17264896 10 494 4154 24 _ _ (166637 / 10000) (1666373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17264896 :
    ThetaLowerSegment 17264896 17273088 (862935472853 / 50000) (863342078601 / 50000) := by
  exact
    packedTile8192 17264896 17273088 10 488 4155 24 _ _ (1666417 / 100000) (83321 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17273088 :
    ThetaLowerSegment 17273088 17281280 (863342078601 / 50000) (1727509057377 / 100000) := by
  exact
    packedTile8192 17273088 17281280 10 495 4156 24 _ _ (333293 / 20000) (416617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17281280 :
    ThetaLowerSegment 17281280 17289472 (1727509057377 / 100000) (1728337313841 / 100000) := by
  exact
    packedTile8192 17281280 17289472 10 497 4157 24 _ _ (104157 / 6250) (333303 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17289472 :
    ThetaLowerSegment 17289472 17297664 (1728337313841 / 100000) (1729177259577 / 100000) := by
  exact
    packedTile8192 17289472 17297664 10 504 4158 24 _ _ (1666559 / 100000) (833281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17297664 :
    ThetaLowerSegment 17297664 17305856 (1729177259577 / 100000) (1730020562719 / 100000) := by
  exact
    packedTile8192 17297664 17305856 10 506 4159 24 _ _ (1666607 / 100000) (166661 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17305856 :
    ThetaLowerSegment 17305856 17314048 (1730020562719 / 100000) (1730823889947 / 100000) := by
  exact
    packedTile8192 17305856 17314048 10 482 4160 24 _ _ (833327 / 50000) (1666657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17314048 :
    ThetaLowerSegment 17314048 17322240 (1730823889947 / 100000) (69268156323 / 4000) := by
  exact
    packedTile8192 17314048 17322240 10 528 4161 24 _ _ (1666701 / 100000) (104169 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17322240 :
    ThetaLowerSegment 17322240 17330432 (69268156323 / 4000) (1732550616567 / 100000) := by
  exact
    packedTile8192 17322240 17330432 10 508 4161 24 _ _ (1666749 / 100000) (52086 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17330432 :
    ThetaLowerSegment 17330432 17338624 (1732550616567 / 100000) (1733344011463 / 100000) := by
  exact
    packedTile8192 17330432 17338624 10 476 4162 24 _ _ (416699 / 25000) (1666799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17338624 :
    ThetaLowerSegment 17338624 17346816 (1733344011463 / 100000) (346836820067 / 20000) := by
  exact
    packedTile8192 17338624 17346816 10 504 4163 24 _ _ (1666843 / 100000) (833423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17346816 :
    ThetaLowerSegment 17346816 17355008 (346836820067 / 20000) (13879953671 / 800) := by
  exact
    packedTile8192 17346816 17355008 10 486 4164 24 _ _ (166689 / 10000) (1666893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17355008 :
    ThetaLowerSegment 17355008 17363200 (13879953671 / 800) (1735799339929 / 100000) := by
  exact
    packedTile8192 17355008 17363200 10 483 4165 24 _ _ (833469 / 50000) (1666941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17363200 :
    ThetaLowerSegment 17363200 17371392 (1735799339929 / 100000) (868300579857 / 50000) := by
  exact
    packedTile8192 17363200 17371392 10 481 4166 24 _ _ (333397 / 20000) (416747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17371392 :
    ThetaLowerSegment 17371392 17379584 (868300579857 / 50000) (868713170277 / 50000) := by
  exact
    packedTile8192 17371392 17379584 10 495 4167 24 _ _ (208379 / 12500) (333407 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17379584 :
    ThetaLowerSegment 17379584 17387776 (868713170277 / 50000) (86912493879 / 5000) := by
  exact
    packedTile8192 17379584 17387776 10 494 4168 24 _ _ (1667079 / 100000) (833541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17387776 :
    ThetaLowerSegment 17387776 17395968 (86912493879 / 5000) (869527549719 / 50000) := by
  exact
    packedTile8192 17387776 17395968 10 483 4169 24 _ _ (833563 / 50000) (1667129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17395968 :
    ThetaLowerSegment 17395968 17404160 (869527549719 / 50000) (1739913693533 / 100000) := by
  exact
    packedTile8192 17395968 17404160 10 515 4170 24 _ _ (1667173 / 100000) (208397 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17404160 :
    ThetaLowerSegment 17404160 17412352 (1739913693533 / 100000) (1740780647933 / 100000) := by
  exact
    packedTile8192 17404160 17412352 10 520 4171 24 _ _ (83361 / 5000) (1667223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17412352 :
    ThetaLowerSegment 17412352 17420544 (1740780647933 / 100000) (1741594274717 / 100000) := by
  exact
    packedTile8192 17412352 17420544 10 488 4172 24 _ _ (416817 / 25000) (1667271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17420544 :
    ThetaLowerSegment 17420544 17428736 (1741594274717 / 100000) (1742391251287 / 100000) := by
  exact
    packedTile8192 17420544 17428736 10 478 4173 24 _ _ (333463 / 20000) (833659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17428736 :
    ThetaLowerSegment 17428736 17436928 (1742391251287 / 100000) (1743218262839 / 100000) := by
  exact
    packedTile8192 17428736 17436928 10 496 4174 24 _ _ (833681 / 50000) (333473 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17436928 :
    ThetaLowerSegment 17436928 17445120 (1743218262839 / 100000) (1744038628067 / 100000) := by
  exact
    packedTile8192 17436928 17445120 10 492 4175 24 _ _ (1667409 / 100000) (416853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17445120 :
    ThetaLowerSegment 17445120 17453312 (1744038628067 / 100000) (1744847344227 / 100000) := by
  exact
    packedTile8192 17445120 17453312 10 485 4176 24 _ _ (52108 / 3125) (1667459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17453312 :
    ThetaLowerSegment 17453312 17461504 (1744847344227 / 100000) (1745661085203 / 100000) := by
  exact
    packedTile8192 17453312 17461504 10 488 4177 24 _ _ (833751 / 50000) (333501 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17461504 :
    ThetaLowerSegment 17461504 17469696 (1745661085203 / 100000) (1746478184213 / 100000) := by
  exact
    packedTile8192 17461504 17469696 10 490 4178 24 _ _ (1667549 / 100000) (52111 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17469696 :
    ThetaLowerSegment 17469696 17477888 (1746478184213 / 100000) (1747335328557 / 100000) := by
  exact
    packedTile8192 17469696 17477888 10 514 4179 24 _ _ (416899 / 25000) (1667599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17477888 :
    ThetaLowerSegment 17477888 17486080 (1747335328557 / 100000) (1748175820629 / 100000) := by
  exact
    packedTile8192 17477888 17486080 10 504 4180 24 _ _ (1667643 / 100000) (833823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17486080 :
    ThetaLowerSegment 17486080 17502464 (1748175820629 / 100000) (1749878532119 / 100000) := by
  exact
    packedTile8192 17486080 17502464 11 1021 4181 24 _ _ (166769 / 10000) (1667693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17502464 :
    ThetaLowerSegment 17502464 17518848 (1749878532119 / 100000) (1751467930271 / 100000) := by
  exact
    packedTile8192 17502464 17518848 11 953 4183 24 _ _ (208473 / 12500) (1667787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17518848 :
    ThetaLowerSegment 17518848 17535232 (1751467930271 / 100000) (1753112456993 / 100000) := by
  exact
    packedTile8192 17518848 17535232 11 986 4185 24 _ _ (1667877 / 100000) (41697 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17535232 :
    ThetaLowerSegment 17535232 17551616 (1753112456993 / 100000) (1754803779587 / 100000) := by
  exact
    packedTile8192 17535232 17551616 11 1014 4187 24 _ _ (1667971 / 100000) (833987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17551616 :
    ThetaLowerSegment 17551616 17568000 (1754803779587 / 100000) (1756410125219 / 100000) := by
  exact
    packedTile8192 17551616 17568000 11 963 4189 24 _ _ (52127 / 3125) (1668067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17568000 :
    ThetaLowerSegment 17568000 17584384 (1756410125219 / 100000) (1758081618533 / 100000) := by
  exact
    packedTile8192 17568000 17584384 11 1002 4191 24 _ _ (1668157 / 100000) (10426 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17584384 :
    ThetaLowerSegment 17584384 17600768 (1758081618533 / 100000) (879844072123 / 50000) := by
  exact
    packedTile8192 17584384 17600768 11 963 4193 24 _ _ (1668251 / 100000) (834127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17600768 :
    ThetaLowerSegment 17600768 17617152 (879844072123 / 50000) (880655721479 / 50000) := by
  exact
    packedTile8192 17600768 17617152 11 973 4195 24 _ _ (208543 / 12500) (1668347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17617152 :
    ThetaLowerSegment 17617152 17633536 (880655721479 / 50000) (1762994895891 / 100000) := by
  exact
    packedTile8192 17617152 17633536 11 1009 4197 24 _ _ (1668437 / 100000) (41711 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17633536 :
    ThetaLowerSegment 17633536 17649920 (1762994895891 / 100000) (1764605027341 / 100000) := by
  exact
    packedTile8192 17633536 17649920 11 965 4199 24 _ _ (166853 / 10000) (1668533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17649920 :
    ThetaLowerSegment 17649920 17666304 (1764605027341 / 100000) (1766196893683 / 100000) := by
  exact
    packedTile8192 17649920 17666304 11 954 4201 24 _ _ (1668623 / 100000) (834313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17666304 :
    ThetaLowerSegment 17666304 17682688 (1766196893683 / 100000) (220977986351 / 12500) := by
  exact
    packedTile8192 17666304 17682688 11 975 4203 24 _ _ (333743 / 20000) (834359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17682688 :
    ThetaLowerSegment 17682688 17699072 (220977986351 / 12500) (55296698988 / 3125) := by
  exact
    packedTile8192 17682688 17699072 11 1001 4205 24 _ _ (208601 / 12500) (1668811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17699072 :
    ThetaLowerSegment 17699072 17715456 (55296698988 / 3125) (885549925189 / 50000) := by
  exact
    packedTile8192 17699072 17715456 11 962 4207 24 _ _ (1668901 / 100000) (208613 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17715456 :
    ThetaLowerSegment 17715456 17731840 (885549925189 / 50000) (354550096891 / 20000) := by
  exact
    packedTile8192 17715456 17731840 11 989 4208 24 _ _ (1668993 / 100000) (417249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17731840 :
    ThetaLowerSegment 17731840 17748224 (354550096891 / 20000) (1774342792499 / 100000) := by
  exact
    packedTile8192 17731840 17748224 11 954 4210 24 _ _ (834543 / 50000) (1669089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17748224 :
    ThetaLowerSegment 17748224 17756416 (1774342792499 / 100000) (1775142328761 / 100000) := by
  exact
    packedTile8192 17748224 17756416 10 479 4212 24 _ _ (834589 / 50000) (1669181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17756416 :
    ThetaLowerSegment 17756416 17764608 (1775142328761 / 100000) (1775951902401 / 100000) := by
  exact
    packedTile8192 17756416 17764608 10 485 4213 24 _ _ (208653 / 12500) (1669227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17764608 :
    ThetaLowerSegment 17764608 17772800 (1775951902401 / 100000) (1776756490541 / 100000) := by
  exact
    packedTile8192 17764608 17772800 10 482 4214 24 _ _ (166927 / 10000) (1669273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17772800 :
    ThetaLowerSegment 17772800 17780992 (1776756490541 / 100000) (1777609511017 / 100000) := by
  exact
    packedTile8192 17772800 17780992 10 511 4215 24 _ _ (417329 / 25000) (1669319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17780992 :
    ThetaLowerSegment 17780992 17789184 (1777609511017 / 100000) (1778457547421 / 100000) := by
  exact
    packedTile8192 17780992 17789184 10 508 4216 24 _ _ (1669363 / 100000) (834683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17789184 :
    ThetaLowerSegment 17789184 17805568 (1778457547421 / 100000) (890050957643 / 50000) := by
  exact
    packedTile8192 17789184 17805568 11 985 4217 24 _ _ (1669409 / 100000) (417353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17805568 :
    ThetaLowerSegment 17805568 17821952 (890050957643 / 50000) (1781729678761 / 100000) := by
  exact
    packedTile8192 17805568 17821952 11 975 4219 24 _ _ (1669501 / 100000) (52172 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17821952 :
    ThetaLowerSegment 17821952 17838336 (1781729678761 / 100000) (1783352523157 / 100000) := by
  exact
    packedTile8192 17821952 17838336 11 972 4221 24 _ _ (1669593 / 100000) (417399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17838336 :
    ThetaLowerSegment 17838336 17846528 (1783352523157 / 100000) (1784137275107 / 100000) := by
  exact
    packedTile8192 17838336 17846528 10 470 4223 24 _ _ (333937 / 20000) (208711 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17846528 :
    ThetaLowerSegment 17846528 17854720 (1784137275107 / 100000) (1784955442807 / 100000) := by
  exact
    packedTile8192 17846528 17854720 10 490 4224 24 _ _ (166973 / 10000) (1669733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17854720 :
    ThetaLowerSegment 17854720 17862912 (1784955442807 / 100000) (1785792000583 / 100000) := by
  exact
    packedTile8192 17854720 17862912 10 501 4225 24 _ _ (104361 / 6250) (1669779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17862912 :
    ThetaLowerSegment 17862912 17871104 (1785792000583 / 100000) (1786640270159 / 100000) := by
  exact
    packedTile8192 17862912 17871104 10 508 4226 24 _ _ (834911 / 50000) (66793 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17871104 :
    ThetaLowerSegment 17871104 17887488 (1786640270159 / 100000) (1788258372251 / 100000) := by
  exact
    packedTile8192 17871104 17887488 11 969 4227 24 _ _ (417467 / 25000) (1669871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17887488 :
    ThetaLowerSegment 17887488 17895680 (1788258372251 / 100000) (1789083332491 / 100000) := by
  exact
    packedTile8192 17887488 17895680 10 494 4229 24 _ _ (41749 / 2500) (1669963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17895680 :
    ThetaLowerSegment 17895680 17903872 (1789083332491 / 100000) (1789904974951 / 100000) := by
  exact
    packedTile8192 17895680 17903872 10 492 4230 24 _ _ (334001 / 20000) (208751 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17903872 :
    ThetaLowerSegment 17903872 17912064 (1789904974951 / 100000) (1790693239023 / 100000) := by
  exact
    packedTile8192 17903872 17912064 10 472 4231 24 _ _ (1670051 / 100000) (835027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17912064 :
    ThetaLowerSegment 17912064 17920256 (1790693239023 / 100000) (895753288131 / 50000) := by
  exact
    packedTile8192 17912064 17920256 10 487 4232 24 _ _ (1670097 / 100000) (16701 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17920256 :
    ThetaLowerSegment 17920256 17928448 (895753288131 / 50000) (1792333297047 / 100000) := by
  exact
    packedTile8192 17920256 17928448 10 495 4233 24 _ _ (1670143 / 100000) (835073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17928448 :
    ThetaLowerSegment 17928448 17936640 (1792333297047 / 100000) (358632342059 / 20000) := by
  exact
    packedTile8192 17928448 17936640 10 496 4234 24 _ _ (417547 / 25000) (1670191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17936640 :
    ThetaLowerSegment 17936640 17944832 (358632342059 / 20000) (358799365459 / 20000) := by
  exact
    packedTile8192 17936640 17944832 10 500 4235 24 _ _ (835117 / 50000) (1670237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17944832 :
    ThetaLowerSegment 17944832 17953024 (358799365459 / 20000) (14358802723 / 800) := by
  exact
    packedTile8192 17944832 17953024 10 511 4236 24 _ _ (41757 / 2500) (1670283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17953024 :
    ThetaLowerSegment 17953024 17969408 (14358802723 / 800) (17965490609 / 1000) := by
  exact
    packedTile8192 17953024 17969408 11 1017 4237 24 _ _ (66813 / 4000) (208791 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17969408 :
    ThetaLowerSegment 17969408 17985792 (17965490609 / 1000) (1798217807483 / 100000) := by
  exact
    packedTile8192 17969408 17985792 11 999 4239 24 _ _ (1670417 / 100000) (83521 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell17985792 :
    ThetaLowerSegment 17985792 18002176 (1798217807483 / 100000) (359972317471 / 20000) := by
  exact
    packedTile8192 17985792 18002176 11 984 4240 24 _ _ (417627 / 25000) (1670511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18002176 :
    ThetaLowerSegment 18002176 18018560 (359972317471 / 20000) (1801468703593 / 100000) := by
  exact
    packedTile8192 18002176 18018560 11 962 4242 24 _ _ (1670599 / 100000) (835301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18018560 :
    ThetaLowerSegment 18018560 18034944 (1801468703593 / 100000) (1803069224613 / 100000) := by
  exact
    packedTile8192 18018560 18034944 11 958 4244 24 _ _ (167069 / 10000) (1670693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18034944 :
    ThetaLowerSegment 18034944 18051328 (1803069224613 / 100000) (1804679857497 / 100000) := by
  exact
    packedTile8192 18034944 18051328 11 964 4246 24 _ _ (1670781 / 100000) (52212 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18051328 :
    ThetaLowerSegment 18051328 18067712 (1804679857497 / 100000) (903157820103 / 50000) := by
  exact
    packedTile8192 18051328 18067712 11 979 4248 24 _ _ (1670871 / 100000) (835437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18067712 :
    ThetaLowerSegment 18067712 18084096 (903157820103 / 50000) (903966565711 / 50000) := by
  exact
    packedTile8192 18067712 18084096 11 968 4250 24 _ _ (835481 / 50000) (334193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18084096 :
    ThetaLowerSegment 18084096 18100480 (903966565711 / 50000) (56548564151 / 3125) := by
  exact
    packedTile8192 18084096 18100480 11 970 4252 24 _ _ (1671053 / 100000) (104441 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18100480 :
    ThetaLowerSegment 18100480 18108672 (56548564151 / 3125) (22629786747 / 1250) := by
  exact
    packedTile8192 18100480 18108672 10 496 4254 24 _ _ (1671143 / 100000) (835573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18108672 :
    ThetaLowerSegment 18108672 18125056 (22629786747 / 1250) (226500081339 / 12500) := by
  exact
    packedTile8192 18108672 18125056 11 968 4255 24 _ _ (1671189 / 100000) (208899 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18125056 :
    ThetaLowerSegment 18125056 18133248 (226500081339 / 12500) (906406446153 / 50000) := by
  exact
    packedTile8192 18125056 18133248 10 486 4257 24 _ _ (1671279 / 100000) (835641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18133248 :
    ThetaLowerSegment 18133248 18141440 (906406446153 / 50000) (906831798111 / 50000) := by
  exact
    packedTile8192 18133248 18141440 10 509 4258 24 _ _ (417831 / 25000) (1671327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18141440 :
    ThetaLowerSegment 18141440 18157824 (906831798111 / 50000) (907630712493 / 50000) := by
  exact
    packedTile8192 18141440 18157824 11 956 4259 24 _ _ (1671369 / 100000) (417843 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18157824 :
    ThetaLowerSegment 18157824 18166016 (907630712493 / 50000) (908026012783 / 50000) := by
  exact
    packedTile8192 18157824 18166016 10 473 4261 24 _ _ (83573 / 5000) (1671463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18166016 :
    ThetaLowerSegment 18166016 18174208 (908026012783 / 50000) (1816892792581 / 100000) := by
  exact
    packedTile8192 18166016 18174208 10 503 4262 24 _ _ (334301 / 20000) (417877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18174208 :
    ThetaLowerSegment 18174208 18182400 (1816892792581 / 100000) (1817706837431 / 100000) := by
  exact
    packedTile8192 18174208 18182400 10 487 4263 24 _ _ (33431 / 2000) (1671553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18182400 :
    ThetaLowerSegment 18182400 18190592 (1817706837431 / 100000) (909238721363 / 50000) := by
  exact
    packedTile8192 18182400 18190592 10 461 4264 24 _ _ (334319 / 20000) (835799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18190592 :
    ThetaLowerSegment 18190592 18198784 (909238721363 / 50000) (909651616443 / 50000) := by
  exact
    packedTile8192 18190592 18198784 10 494 4265 24 _ _ (41791 / 2500) (1671643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18198784 :
    ThetaLowerSegment 18198784 18206976 (909651616443 / 50000) (1820117343481 / 100000) := by
  exact
    packedTile8192 18198784 18206976 10 487 4266 24 _ _ (334337 / 20000) (208961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18206976 :
    ThetaLowerSegment 18206976 18215168 (1820117343481 / 100000) (1820928132531 / 100000) := by
  exact
    packedTile8192 18206976 18215168 10 485 4266 24 _ _ (167173 / 10000) (1671733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18215168 :
    ThetaLowerSegment 18215168 18223360 (1820928132531 / 100000) (910889533003 / 50000) := by
  exact
    packedTile8192 18215168 18223360 10 509 4267 24 _ _ (66871 / 4000) (835889 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18223360 :
    ThetaLowerSegment 18223360 18231552 (910889533003 / 50000) (911299964813 / 50000) := by
  exact
    packedTile8192 18223360 18231552 10 491 4268 24 _ _ (83591 / 5000) (1671823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18231552 :
    ThetaLowerSegment 18231552 18239744 (911299964813 / 50000) (1823477658751 / 100000) := by
  exact
    packedTile8192 18231552 18239744 10 525 4269 24 _ _ (334373 / 20000) (417967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18239744 :
    ThetaLowerSegment 18239744 18247936 (1823477658751 / 100000) (1824291878921 / 100000) := by
  exact
    packedTile8192 18239744 18247936 10 487 4270 24 _ _ (167191 / 10000) (1671913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18247936 :
    ThetaLowerSegment 18247936 18256128 (1824291878921 / 100000) (228141191047 / 12500) := by
  exact
    packedTile8192 18247936 18256128 10 501 4271 24 _ _ (334391 / 20000) (835979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18256128 :
    ThetaLowerSegment 18256128 18272512 (228141191047 / 12500) (228348101047 / 12500) := by
  exact
    packedTile8192 18256128 18272512 11 990 4272 24 _ _ (418 / 25) (1672003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18272512 :
    ThetaLowerSegment 18272512 18288896 (228348101047 / 12500) (457105863899 / 25000) := by
  exact
    packedTile8192 18272512 18288896 11 980 4274 24 _ _ (1672089 / 100000) (418023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18288896 :
    ThetaLowerSegment 18288896 18305280 (457105863899 / 25000) (1830067207553 / 100000) := by
  exact
    packedTile8192 18288896 18305280 11 983 4276 24 _ _ (1672179 / 100000) (836091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18305280 :
    ThetaLowerSegment 18305280 18321664 (1830067207553 / 100000) (366350570941 / 20000) := by
  exact
    packedTile8192 18305280 18321664 11 1008 4278 24 _ _ (1672269 / 100000) (104517 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18321664 :
    ThetaLowerSegment 18321664 18338048 (366350570941 / 20000) (1833415178557 / 100000) := by
  exact
    packedTile8192 18321664 18338048 11 994 4280 24 _ _ (836179 / 50000) (1672361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18338048 :
    ThetaLowerSegment 18338048 18354432 (1833415178557 / 100000) (367002138599 / 20000) := by
  exact
    packedTile8192 18338048 18354432 11 954 4282 24 _ _ (1672447 / 100000) (33449 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18354432 :
    ThetaLowerSegment 18354432 18370816 (367002138599 / 20000) (1836592912997 / 100000) := by
  exact
    packedTile8192 18354432 18370816 11 946 4284 24 _ _ (1672537 / 100000) (83627 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18370816 :
    ThetaLowerSegment 18370816 18387200 (1836592912997 / 100000) (1838235431729 / 100000) := by
  exact
    packedTile8192 18370816 18387200 11 982 4286 24 _ _ (836313 / 50000) (1672629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18387200 :
    ThetaLowerSegment 18387200 18403584 (1838235431729 / 100000) (1839874692429 / 100000) := by
  exact
    packedTile8192 18387200 18403584 11 980 4288 24 _ _ (334543 / 20000) (836359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18403584 :
    ThetaLowerSegment 18403584 18419968 (1839874692429 / 100000) (368310837529 / 20000) := by
  exact
    packedTile8192 18403584 18419968 11 1004 4289 24 _ _ (418201 / 25000) (1672807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18419968 :
    ThetaLowerSegment 18419968 18436352 (368310837529 / 20000) (1843130052851 / 100000) := by
  exact
    packedTile8192 18419968 18436352 11 942 4291 24 _ _ (1672893 / 100000) (52278 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18436352 :
    ThetaLowerSegment 18436352 18452736 (1843130052851 / 100000) (1844801361869 / 100000) := by
  exact
    packedTile8192 18436352 18452736 11 999 4293 24 _ _ (836491 / 50000) (334597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18452736 :
    ThetaLowerSegment 18452736 18469120 (1844801361869 / 100000) (115401828747 / 6250) := by
  exact
    packedTile8192 18452736 18469120 11 973 4295 24 _ _ (1673071 / 100000) (836537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18469120 :
    ThetaLowerSegment 18469120 18485504 (115401828747 / 6250) (57750795456 / 3125) := by
  exact
    packedTile8192 18469120 18485504 11 954 4297 24 _ _ (41829 / 2500) (1673163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18485504 :
    ThetaLowerSegment 18485504 18493696 (57750795456 / 3125) (57775894176 / 3125) := by
  exact
    packedTile8192 18485504 18493696 10 480 4299 24 _ _ (52289 / 3125) (1673251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18493696 :
    ThetaLowerSegment 18493696 18501888 (57775894176 / 3125) (1849626774393 / 100000) := by
  exact
    packedTile8192 18493696 18501888 10 477 4300 24 _ _ (1673293 / 100000) (104581 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18501888 :
    ThetaLowerSegment 18501888 18510080 (1849626774393 / 100000) (1850446709523 / 100000) := by
  exact
    packedTile8192 18501888 18510080 10 490 4301 24 _ _ (1673337 / 100000) (83667 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18510080 :
    ThetaLowerSegment 18510080 18518272 (1850446709523 / 100000) (1851256625927 / 100000) := by
  exact
    packedTile8192 18510080 18518272 10 484 4302 24 _ _ (1673381 / 100000) (209173 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18518272 :
    ThetaLowerSegment 18518272 18526464 (1851256625927 / 100000) (1852066563627 / 100000) := by
  exact
    packedTile8192 18518272 18526464 10 484 4303 24 _ _ (66937 / 4000) (418357 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18526464 :
    ThetaLowerSegment 18526464 18534656 (1852066563627 / 100000) (1852886563927 / 100000) := by
  exact
    packedTile8192 18526464 18534656 10 490 4304 24 _ _ (167347 / 10000) (1673473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18534656 :
    ThetaLowerSegment 18534656 18542848 (1852886563927 / 100000) (1853713279843 / 100000) := by
  exact
    packedTile8192 18534656 18542848 10 494 4305 24 _ _ (836757 / 50000) (1673517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18542848 :
    ThetaLowerSegment 18542848 18551040 (1853713279843 / 100000) (1854538343937 / 100000) := by
  exact
    packedTile8192 18542848 18551040 10 493 4306 24 _ _ (836779 / 50000) (1673561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18551040 :
    ThetaLowerSegment 18551040 18559232 (1854538343937 / 100000) (1855360082519 / 100000) := by
  exact
    packedTile8192 18551040 18559232 10 491 4307 24 _ _ (836801 / 50000) (334721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18559232 :
    ThetaLowerSegment 18559232 18567424 (1855360082519 / 100000) (1856155064369 / 100000) := by
  exact
    packedTile8192 18559232 18567424 10 475 4308 24 _ _ (836823 / 50000) (1673649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18567424 :
    ThetaLowerSegment 18567424 18575616 (1856155064369 / 100000) (1856998604129 / 100000) := by
  exact
    packedTile8192 18567424 18575616 10 504 4308 24 _ _ (167369 / 10000) (1673693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18575616 :
    ThetaLowerSegment 18575616 18583808 (1856998604129 / 100000) (1857798649459 / 100000) := by
  exact
    packedTile8192 18575616 18583808 10 478 4309 24 _ _ (334747 / 20000) (836869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18583808 :
    ThetaLowerSegment 18583808 18592000 (1857798649459 / 100000) (371731794373 / 20000) := by
  exact
    packedTile8192 18583808 18592000 10 514 4310 24 _ _ (1673779 / 100000) (836891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18592000 :
    ThetaLowerSegment 18592000 18600192 (371731794373 / 20000) (464871041651 / 25000) := by
  exact
    packedTile8192 18592000 18600192 10 493 4311 24 _ _ (1673823 / 100000) (836913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18600192 :
    ThetaLowerSegment 18600192 18608384 (464871041651 / 25000) (1860319426237 / 100000) := by
  exact
    packedTile8192 18600192 18608384 10 499 4312 24 _ _ (1673867 / 100000) (167387 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18608384 :
    ThetaLowerSegment 18608384 18616576 (1860319426237 / 100000) (1861142990449 / 100000) := by
  exact
    packedTile8192 18608384 18616576 10 492 4313 24 _ _ (1673911 / 100000) (836957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18616576 :
    ThetaLowerSegment 18616576 18632960 (1861142990449 / 100000) (931390896197 / 50000) := by
  exact
    packedTile8192 18616576 18632960 11 979 4314 24 _ _ (334791 / 20000) (836979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18632960 :
    ThetaLowerSegment 18632960 18649344 (931390896197 / 50000) (372890162653 / 20000) := by
  exact
    packedTile8192 18632960 18649344 11 997 4316 24 _ _ (1674043 / 100000) (837023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18649344 :
    ThetaLowerSegment 18649344 18665728 (372890162653 / 20000) (233263316103 / 12500) := by
  exact
    packedTile8192 18649344 18665728 11 989 4318 24 _ _ (1674131 / 100000) (837067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18665728 :
    ThetaLowerSegment 18665728 18682112 (233263316103 / 12500) (93385856327 / 5000) := by
  exact
    packedTile8192 18665728 18682112 11 962 4320 24 _ _ (837109 / 50000) (1674221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18682112 :
    ThetaLowerSegment 18682112 18698496 (93385856327 / 5000) (116832988057 / 6250) := by
  exact
    packedTile8192 18682112 18698496 11 962 4322 24 _ _ (837153 / 50000) (1674309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18698496 :
    ThetaLowerSegment 18698496 18714880 (116832988057 / 6250) (935480171531 / 50000) := by
  exact
    packedTile8192 18698496 18714880 11 975 4324 24 _ _ (837197 / 50000) (1674397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18714880 :
    ThetaLowerSegment 18714880 18723072 (935480171531 / 50000) (467936837283 / 25000) := by
  exact
    packedTile8192 18714880 18723072 10 470 4326 24 _ _ (1674481 / 100000) (418621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18723072 :
    ThetaLowerSegment 18723072 18731264 (467936837283 / 25000) (936300678441 / 50000) := by
  exact
    packedTile8192 18723072 18731264 10 510 4327 24 _ _ (66981 / 4000) (52329 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18731264 :
    ThetaLowerSegment 18731264 18747648 (936300678441 / 50000) (1874274251313 / 100000) := by
  exact
    packedTile8192 18731264 18747648 11 999 4327 24 _ _ (1674569 / 100000) (418643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18747648 :
    ThetaLowerSegment 18747648 18764032 (1874274251313 / 100000) (375187102013 / 20000) := by
  exact
    packedTile8192 18747648 18764032 11 992 4329 24 _ _ (52333 / 3125) (1674659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18764032 :
    ThetaLowerSegment 18764032 18780416 (375187102013 / 20000) (1877571734953 / 100000) := by
  exact
    packedTile8192 18764032 18780416 11 977 4331 24 _ _ (209343 / 12500) (1674747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18780416 :
    ThetaLowerSegment 18780416 18796800 (1877571734953 / 100000) (93958727411 / 5000) := by
  exact
    packedTile8192 18780416 18796800 11 957 4333 24 _ _ (1674831 / 100000) (837417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18796800 :
    ThetaLowerSegment 18796800 18813184 (93958727411 / 5000) (470200642129 / 25000) := by
  exact
    packedTile8192 18796800 18813184 11 972 4335 24 _ _ (837459 / 50000) (1674921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18813184 :
    ThetaLowerSegment 18813184 18829568 (470200642129 / 25000) (1882442398411 / 100000) := by
  exact
    packedTile8192 18813184 18829568 11 979 4337 24 _ _ (335001 / 20000) (52344 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18829568 :
    ThetaLowerSegment 18829568 18845952 (1882442398411 / 100000) (1884060537283 / 100000) := by
  exact
    packedTile8192 18829568 18845952 11 966 4339 24 _ _ (418773 / 25000) (335019 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18845952 :
    ThetaLowerSegment 18845952 18854144 (1884060537283 / 100000) (1884921579289 / 100000) := by
  exact
    packedTile8192 18845952 18854144 10 514 4341 24 _ _ (1675179 / 100000) (837591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18854144 :
    ThetaLowerSegment 18854144 18870528 (1884921579289 / 100000) (188657502439 / 10000) := by
  exact
    packedTile8192 18854144 18870528 11 987 4342 24 _ _ (1675223 / 100000) (837613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18870528 :
    ThetaLowerSegment 18870528 18886912 (188657502439 / 10000) (188816321827 / 10000) := by
  exact
    packedTile8192 18870528 18886912 11 948 4344 24 _ _ (167531 / 10000) (1675313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18886912 :
    ThetaLowerSegment 18886912 18903296 (188816321827 / 10000) (944889150007 / 50000) := by
  exact
    packedTile8192 18886912 18903296 11 964 4345 24 _ _ (418849 / 25000) (1675399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18903296 :
    ThetaLowerSegment 18903296 18911488 (944889150007 / 50000) (1890587558303 / 100000) := by
  exact
    packedTile8192 18903296 18911488 10 483 4347 24 _ _ (1675483 / 100000) (837743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18911488 :
    ThetaLowerSegment 18911488 18919680 (1890587558303 / 100000) (1891398513371 / 100000) := by
  exact
    packedTile8192 18911488 18919680 10 484 4348 24 _ _ (1675527 / 100000) (167553 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18919680 :
    ThetaLowerSegment 18919680 18927872 (1891398513371 / 100000) (1892222893811 / 100000) := by
  exact
    packedTile8192 18919680 18927872 10 492 4349 24 _ _ (167557 / 10000) (1675573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18927872 :
    ThetaLowerSegment 18927872 18936064 (1892222893811 / 100000) (236636986023 / 12500) := by
  exact
    packedTile8192 18927872 18936064 10 521 4350 24 _ _ (1675613 / 100000) (52363 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18936064 :
    ThetaLowerSegment 18936064 18952448 (236636986023 / 12500) (118422697869 / 6250) := by
  exact
    packedTile8192 18936064 18952448 11 995 4351 24 _ _ (209457 / 12500) (1675659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18952448 :
    ThetaLowerSegment 18952448 18968832 (118422697869 / 6250) (47408961831 / 2500) := by
  exact
    packedTile8192 18952448 18968832 11 952 4353 24 _ _ (1675743 / 100000) (837873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18968832 :
    ThetaLowerSegment 18968832 18985216 (47408961831 / 2500) (379601832961 / 20000) := by
  exact
    packedTile8192 18968832 18985216 11 985 4355 24 _ _ (1675829 / 100000) (209479 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell18985216 :
    ThetaLowerSegment 18985216 19001600 (379601832961 / 20000) (1899654914317 / 100000) := by
  exact
    packedTile8192 18985216 19001600 11 982 4357 24 _ _ (418979 / 25000) (1675919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19001600 :
    ThetaLowerSegment 19001600 19017984 (1899654914317 / 100000) (1901289016267 / 100000) := by
  exact
    packedTile8192 19001600 19017984 11 975 4359 24 _ _ (838001 / 50000) (335201 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19017984 :
    ThetaLowerSegment 19017984 19034368 (1901289016267 / 100000) (1902919849891 / 100000) := by
  exact
    packedTile8192 19017984 19034368 11 973 4360 24 _ _ (209511 / 12500) (1676091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19034368 :
    ThetaLowerSegment 19034368 19050752 (1902919849891 / 100000) (1904567528933 / 100000) := by
  exact
    packedTile8192 19034368 19050752 11 983 4362 24 _ _ (838087 / 50000) (1676177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19050752 :
    ThetaLowerSegment 19050752 19067136 (1904567528933 / 100000) (1906156623413 / 100000) := by
  exact
    packedTile8192 19050752 19067136 11 948 4364 24 _ _ (83813 / 5000) (1676263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19067136 :
    ThetaLowerSegment 19067136 19075328 (1906156623413 / 100000) (1906999825451 / 100000) := by
  exact
    packedTile8192 19067136 19075328 10 503 4366 24 _ _ (838173 / 50000) (1676349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19075328 :
    ThetaLowerSegment 19075328 19091712 (1906999825451 / 100000) (381730549001 / 20000) := by
  exact
    packedTile8192 19075328 19091712 11 986 4367 24 _ _ (1676389 / 100000) (209549 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19091712 :
    ThetaLowerSegment 19091712 19108096 (381730549001 / 20000) (382051091021 / 20000) := by
  exact
    packedTile8192 19091712 19108096 11 956 4369 24 _ _ (67059 / 4000) (838239 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19108096 :
    ThetaLowerSegment 19108096 19116288 (382051091021 / 20000) (477756249151 / 25000) := by
  exact
    packedTile8192 19108096 19116288 10 459 4371 24 _ _ (1676561 / 100000) (419141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19116288 :
    ThetaLowerSegment 19116288 19124480 (477756249151 / 25000) (119493866281 / 6250) := by
  exact
    packedTile8192 19116288 19124480 10 523 4372 24 _ _ (419151 / 25000) (1676607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19124480 :
    ThetaLowerSegment 19124480 19140864 (119493866281 / 6250) (478382051779 / 25000) := by
  exact
    packedTile8192 19124480 19140864 11 970 4373 24 _ _ (838323 / 50000) (1676649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19140864 :
    ThetaLowerSegment 19140864 19149056 (478382051779 / 25000) (95717657963 / 5000) := by
  exact
    packedTile8192 19140864 19149056 10 492 4375 24 _ _ (419183 / 25000) (335347 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19149056 :
    ThetaLowerSegment 19149056 19157248 (95717657963 / 5000) (383035961867 / 20000) := by
  exact
    packedTile8192 19149056 19157248 10 493 4375 24 _ _ (67071 / 4000) (838389 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19157248 :
    ThetaLowerSegment 19157248 19173632 (383035961867 / 20000) (1916816383703 / 100000) := by
  exact
    packedTile8192 19157248 19173632 11 976 4376 24 _ _ (838409 / 50000) (1676821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19173632 :
    ThetaLowerSegment 19173632 19190016 (1916816383703 / 100000) (1918436272001 / 100000) := by
  exact
    packedTile8192 19173632 19190016 11 966 4378 24 _ _ (1676903 / 100000) (838453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19190016 :
    ThetaLowerSegment 19190016 19198208 (1918436272001 / 100000) (1919261350589 / 100000) := by
  exact
    packedTile8192 19190016 19198208 10 492 4380 24 _ _ (1676989 / 100000) (52406 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19198208 :
    ThetaLowerSegment 19198208 19206400 (1919261350589 / 100000) (1920099866089 / 100000) := by
  exact
    packedTile8192 19198208 19206400 10 500 4381 24 _ _ (1677031 / 100000) (838517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19206400 :
    ThetaLowerSegment 19206400 19222784 (1920099866089 / 100000) (76866985543 / 4000) := by
  exact
    packedTile8192 19206400 19222784 11 939 4382 24 _ _ (838537 / 50000) (1677077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19222784 :
    ThetaLowerSegment 19222784 19230976 (76866985543 / 4000) (1922503155121 / 100000) := by
  exact
    packedTile8192 19222784 19230976 10 494 4384 24 _ _ (1677159 / 100000) (838581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19230976 :
    ThetaLowerSegment 19230976 19239168 (1922503155121 / 100000) (1923301503273 / 100000) := by
  exact
    packedTile8192 19230976 19239168 10 476 4385 24 _ _ (838601 / 50000) (335441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19239168 :
    ThetaLowerSegment 19239168 19247360 (1923301503273 / 100000) (1924131739053 / 100000) := by
  exact
    packedTile8192 19239168 19247360 10 495 4386 24 _ _ (419311 / 25000) (1677247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19247360 :
    ThetaLowerSegment 19247360 19255552 (1924131739053 / 100000) (1924953609683 / 100000) := by
  exact
    packedTile8192 19247360 19255552 10 490 4387 24 _ _ (1677287 / 100000) (167729 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19255552 :
    ThetaLowerSegment 19255552 19263744 (1924953609683 / 100000) (1925792274183 / 100000) := by
  exact
    packedTile8192 19255552 19263744 10 500 4388 24 _ _ (1677329 / 100000) (419333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19263744 :
    ThetaLowerSegment 19263744 19271936 (1925792274183 / 100000) (1926595735371 / 100000) := by
  exact
    packedTile8192 19263744 19271936 10 479 4389 24 _ _ (419343 / 25000) (13419 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19271936 :
    ThetaLowerSegment 19271936 19280128 (1926595735371 / 100000) (963707995653 / 50000) := by
  exact
    packedTile8192 19271936 19280128 10 489 4389 24 _ _ (335483 / 20000) (838709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19280128 :
    ThetaLowerSegment 19280128 19288320 (963707995653 / 50000) (1928229557951 / 100000) := by
  exact
    packedTile8192 19280128 19288320 10 485 4390 24 _ _ (1677457 / 100000) (83873 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19288320 :
    ThetaLowerSegment 19288320 19296512 (1928229557951 / 100000) (1929041467951 / 100000) := by
  exact
    packedTile8192 19288320 19296512 10 484 4391 24 _ _ (671 / 40) (1677503 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19296512 :
    ThetaLowerSegment 19296512 19304704 (1929041467951 / 100000) (1929878561409 / 100000) := by
  exact
    packedTile8192 19296512 19304704 10 499 4392 24 _ _ (838771 / 50000) (335509 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19304704 :
    ThetaLowerSegment 19304704 19312896 (1929878561409 / 100000) (1930713998241 / 100000) := by
  exact
    packedTile8192 19304704 19312896 10 498 4393 24 _ _ (104849 / 6250) (1677587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19312896 :
    ThetaLowerSegment 19312896 19321088 (1930713998241 / 100000) (1931532680217 / 100000) := by
  exact
    packedTile8192 19312896 19321088 10 488 4394 24 _ _ (1677627 / 100000) (167763 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19321088 :
    ThetaLowerSegment 19321088 19329280 (1931532680217 / 100000) (966179885517 / 50000) := by
  exact
    packedTile8192 19321088 19329280 10 493 4395 24 _ _ (1677669 / 100000) (209709 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19329280 :
    ThetaLowerSegment 19329280 19337472 (966179885517 / 50000) (193317849449 / 10000) := by
  exact
    packedTile8192 19329280 19337472 10 488 4396 24 _ _ (104857 / 6250) (335543 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19337472 :
    ThetaLowerSegment 19337472 19345664 (193317849449 / 10000) (60436941833 / 3125) := by
  exact
    packedTile8192 19337472 19345664 10 479 4397 24 _ _ (838877 / 50000) (1677757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19345664 :
    ThetaLowerSegment 19345664 19353856 (60436941833 / 3125) (483705678613 / 25000) := by
  exact
    packedTile8192 19345664 19353856 10 501 4398 24 _ _ (419449 / 25000) (1677799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19353856 :
    ThetaLowerSegment 19353856 19362048 (483705678613 / 25000) (48391205281 / 2500) := by
  exact
    packedTile8192 19353856 19362048 10 492 4399 24 _ _ (1677839 / 100000) (838921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19362048 :
    ThetaLowerSegment 19362048 19378432 (48391205281 / 2500) (387453473281 / 20000) := by
  exact
    packedTile8192 19362048 19378432 11 965 4400 24 _ _ (1677881 / 100000) (419471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19378432 :
    ThetaLowerSegment 19378432 19386624 (387453473281 / 20000) (1938126484997 / 100000) := by
  exact
    packedTile8192 19378432 19386624 10 512 4402 24 _ _ (838983 / 50000) (1677969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19386624 :
    ThetaLowerSegment 19386624 19403008 (1938126484997 / 100000) (77589897629 / 4000) := by
  exact
    packedTile8192 19386624 19403008 11 966 4403 24 _ _ (209751 / 12500) (1678011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19403008 :
    ThetaLowerSegment 19403008 19419392 (77589897629 / 4000) (1941437279369 / 100000) := by
  exact
    packedTile8192 19403008 19419392 11 1007 4404 24 _ _ (419523 / 25000) (335619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19419392 :
    ThetaLowerSegment 19419392 19435776 (1941437279369 / 100000) (485766697309 / 25000) := by
  exact
    packedTile8192 19419392 19435776 11 971 4406 24 _ _ (1678177 / 100000) (83909 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19435776 :
    ThetaLowerSegment 19435776 19452160 (485766697309 / 25000) (60772653472 / 3125) := by
  exact
    packedTile8192 19435776 19452160 11 988 4408 24 _ _ (1678261 / 100000) (209783 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19452160 :
    ThetaLowerSegment 19452160 19468544 (60772653472 / 3125) (1946351227409 / 100000) := by
  exact
    packedTile8192 19452160 19468544 11 969 4410 24 _ _ (335669 / 20000) (419587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19468544 :
    ThetaLowerSegment 19468544 19484928 (1946351227409 / 100000) (1947992731949 / 100000) := by
  exact
    packedTile8192 19468544 19484928 11 978 4412 24 _ _ (167843 / 10000) (1678433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19484928 :
    ThetaLowerSegment 19484928 19501312 (1947992731949 / 100000) (1949595712819 / 100000) := by
  exact
    packedTile8192 19484928 19501312 11 955 4414 24 _ _ (839257 / 50000) (1678517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19501312 :
    ThetaLowerSegment 19501312 19517696 (1949595712819 / 100000) (1951250810447 / 100000) := by
  exact
    packedTile8192 19501312 19517696 11 986 4416 24 _ _ (839299 / 50000) (1678601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19517696 :
    ThetaLowerSegment 19517696 19534080 (1951250810447 / 100000) (1952845558347 / 100000) := by
  exact
    packedTile8192 19517696 19534080 11 950 4417 24 _ _ (839341 / 50000) (335737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19534080 :
    ThetaLowerSegment 19534080 19550464 (1952845558347 / 100000) (1954457173707 / 100000) := by
  exact
    packedTile8192 19534080 19550464 11 960 4419 24 _ _ (839383 / 50000) (1678769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19550464 :
    ThetaLowerSegment 19550464 19558656 (1954457173707 / 100000) (1955242875039 / 100000) := by
  exact
    packedTile8192 19550464 19558656 10 468 4421 24 _ _ (1678849 / 100000) (419713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19558656 :
    ThetaLowerSegment 19558656 19566848 (1955242875039 / 100000) (61126680606 / 3125) := by
  exact
    packedTile8192 19558656 19566848 10 483 4422 24 _ _ (1678891 / 100000) (839447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19566848 :
    ThetaLowerSegment 19566848 19575040 (61126680606 / 3125) (1956874777629 / 100000) := by
  exact
    packedTile8192 19566848 19575040 10 489 4423 24 _ _ (1678933 / 100000) (209867 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19575040 :
    ThetaLowerSegment 19575040 19583232 (1956874777629 / 100000) (978832787427 / 50000) := by
  exact
    packedTile8192 19575040 19583232 10 471 4424 24 _ _ (67159 / 4000) (839489 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19583232 :
    ThetaLowerSegment 19583232 19591424 (978832787427 / 50000) (78337718389 / 4000) := by
  exact
    packedTile8192 19583232 19591424 10 463 4425 24 _ _ (1679017 / 100000) (83951 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19591424 :
    ThetaLowerSegment 19591424 19599616 (78337718389 / 4000) (1959292563579 / 100000) := by
  exact
    packedTile8192 19591424 19599616 10 506 4426 24 _ _ (1679059 / 100000) (839531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19599616 :
    ThetaLowerSegment 19599616 19607808 (1959292563579 / 100000) (1960148905089 / 100000) := by
  exact
    packedTile8192 19599616 19607808 10 510 4427 24 _ _ (1679101 / 100000) (52472 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19607808 :
    ThetaLowerSegment 19607808 19616000 (1960148905089 / 100000) (392188627851 / 20000) := by
  exact
    packedTile8192 19607808 19616000 10 473 4428 24 _ _ (839571 / 50000) (335829 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19616000 :
    ThetaLowerSegment 19616000 19624192 (392188627851 / 20000) (1961792806359 / 100000) := by
  exact
    packedTile8192 19616000 19624192 10 506 4428 24 _ _ (104949 / 6250) (1679187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19624192 :
    ThetaLowerSegment 19624192 19632384 (1961792806359 / 100000) (1962627381681 / 100000) := by
  exact
    packedTile8192 19624192 19632384 10 497 4429 24 _ _ (839613 / 50000) (1679229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19632384 :
    ThetaLowerSegment 19632384 19640576 (1962627381681 / 100000) (1963436788857 / 100000) := by
  exact
    packedTile8192 19632384 19640576 10 482 4430 24 _ _ (419817 / 25000) (1679271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19640576 :
    ThetaLowerSegment 19640576 19648768 (1963436788857 / 100000) (24552762827 / 1250) := by
  exact
    packedTile8192 19640576 19648768 10 467 4431 24 _ _ (1679309 / 100000) (104957 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19648768 :
    ThetaLowerSegment 19648768 19656960 (24552762827 / 1250) (39300878163 / 2000) := by
  exact
    packedTile8192 19648768 19656960 10 490 4432 24 _ _ (1679351 / 100000) (839677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19656960 :
    ThetaLowerSegment 19656960 19665152 (39300878163 / 2000) (78633664793 / 4000) := by
  exact
    packedTile8192 19656960 19665152 10 475 4433 24 _ _ (1679393 / 100000) (419849 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19665152 :
    ThetaLowerSegment 19665152 19673344 (78633664793 / 4000) (1966686375127 / 100000) := by
  exact
    packedTile8192 19665152 19673344 10 503 4434 24 _ _ (839717 / 50000) (1679437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19673344 :
    ThetaLowerSegment 19673344 19681536 (1966686375127 / 100000) (1967499241511 / 100000) := by
  exact
    packedTile8192 19673344 19681536 10 484 4435 24 _ _ (419869 / 25000) (1679479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19681536 :
    ThetaLowerSegment 19681536 19689728 (1967499241511 / 100000) (1968303730633 / 100000) := by
  exact
    packedTile8192 19681536 19689728 10 479 4436 24 _ _ (839759 / 50000) (1679521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19689728 :
    ThetaLowerSegment 19689728 19697920 (1968303730633 / 100000) (393831389321 / 20000) := by
  exact
    packedTile8192 19689728 19697920 10 508 4437 24 _ _ (1679559 / 100000) (839781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19697920 :
    ThetaLowerSegment 19697920 19706112 (393831389321 / 20000) (393995990219 / 20000) := by
  exact
    packedTile8192 19697920 19706112 10 490 4438 24 _ _ (1679601 / 100000) (419901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19706112 :
    ThetaLowerSegment 19706112 19714304 (393995990219 / 20000) (394165634061 / 20000) := by
  exact
    packedTile8192 19706112 19714304 10 505 4439 24 _ _ (839821 / 50000) (335929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19714304 :
    ThetaLowerSegment 19714304 19722496 (394165634061 / 20000) (1971619301469 / 100000) := by
  exact
    packedTile8192 19714304 19722496 10 471 4440 24 _ _ (419921 / 25000) (1679687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19722496 :
    ThetaLowerSegment 19722496 19730688 (1971619301469 / 100000) (394483770209 / 20000) := by
  exact
    packedTile8192 19722496 19730688 10 476 4441 24 _ _ (839863 / 50000) (1679729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19730688 :
    ThetaLowerSegment 19730688 19738880 (394483770209 / 20000) (986615089253 / 50000) := by
  exact
    packedTile8192 19730688 19738880 10 483 4441 24 _ _ (1679767 / 100000) (167977 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19738880 :
    ThetaLowerSegment 19738880 19747072 (986615089253 / 50000) (1974081841669 / 100000) := by
  exact
    packedTile8192 19738880 19747072 10 507 4442 24 _ _ (1679809 / 100000) (419953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19747072 :
    ThetaLowerSegment 19747072 19755264 (1974081841669 / 100000) (1974915047269 / 100000) := by
  exact
    packedTile8192 19747072 19755264 10 496 4443 24 _ _ (33597 / 2000) (1679853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19755264 :
    ThetaLowerSegment 19755264 19763456 (1974915047269 / 100000) (1975731474781 / 100000) := by
  exact
    packedTile8192 19755264 19763456 10 486 4444 24 _ _ (419973 / 25000) (335979 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19763456 :
    ThetaLowerSegment 19763456 19771648 (1975731474781 / 100000) (1976564721549 / 100000) := by
  exact
    packedTile8192 19763456 19771648 10 496 4445 24 _ _ (1679933 / 100000) (52498 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19771648 :
    ThetaLowerSegment 19771648 19779840 (1976564721549 / 100000) (1977374469017 / 100000) := by
  exact
    packedTile8192 19771648 19779840 10 482 4446 24 _ _ (839987 / 50000) (1679977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19779840 :
    ThetaLowerSegment 19779840 19788032 (1977374469017 / 100000) (1978204396921 / 100000) := by
  exact
    packedTile8192 19779840 19788032 10 494 4447 24 _ _ (105001 / 6250) (1680019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19788032 :
    ThetaLowerSegment 19788032 19796224 (1978204396921 / 100000) (989516332511 / 50000) := by
  exact
    packedTile8192 19788032 19796224 10 493 4448 24 _ _ (1680057 / 100000) (84003 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19796224 :
    ThetaLowerSegment 19796224 19804416 (989516332511 / 50000) (395976895043 / 20000) := by
  exact
    packedTile8192 19796224 19804416 10 507 4449 24 _ _ (1680099 / 100000) (840051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19804416 :
    ThetaLowerSegment 19804416 19820800 (395976895043 / 20000) (396301498091 / 20000) := by
  exact
    packedTile8192 19804416 19820800 11 966 4450 24 _ _ (84007 / 5000) (1680143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19820800 :
    ThetaLowerSegment 19820800 19837184 (396301498091 / 20000) (991571173717 / 50000) := by
  exact
    packedTile8192 19820800 19837184 11 973 4452 24 _ _ (1680223 / 100000) (840113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19837184 :
    ThetaLowerSegment 19837184 19853568 (991571173717 / 50000) (1984807529689 / 100000) := by
  exact
    packedTile8192 19837184 19853568 11 991 4453 24 _ _ (336061 / 20000) (420077 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19853568 :
    ThetaLowerSegment 19853568 19869952 (1984807529689 / 100000) (1986417341393 / 100000) := by
  exact
    packedTile8192 19853568 19869952 11 958 4455 24 _ _ (420097 / 25000) (1680391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19869952 :
    ThetaLowerSegment 19869952 19886336 (1986417341393 / 100000) (1988097811393 / 100000) := by
  exact
    packedTile8192 19869952 19886336 11 1000 4457 24 _ _ (168047 / 10000) (1680473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19886336 :
    ThetaLowerSegment 19886336 19902720 (1988097811393 / 100000) (497415601559 / 25000) := by
  exact
    packedTile8192 19886336 19902720 11 931 4459 24 _ _ (1680553 / 100000) (420139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19902720 :
    ThetaLowerSegment 19902720 19910912 (497415601559 / 25000) (1990501043101 / 100000) := by
  exact
    packedTile8192 19902720 19910912 10 499 4461 24 _ _ (336127 / 20000) (840319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19910912 :
    ThetaLowerSegment 19910912 19927296 (1990501043101 / 100000) (1992181719101 / 100000) := by
  exact
    packedTile8192 19910912 19927296 11 1000 4462 24 _ _ (420169 / 25000) (1680679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19927296 :
    ThetaLowerSegment 19927296 19943680 (1992181719101 / 100000) (1993808693813 / 100000) := by
  exact
    packedTile8192 19927296 19943680 11 968 4464 24 _ _ (1680759 / 100000) (840381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19943680 :
    ThetaLowerSegment 19943680 19960064 (1993808693813 / 100000) (997745607827 / 50000) := by
  exact
    packedTile8192 19943680 19960064 11 1001 4465 24 _ _ (1680841 / 100000) (420211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19960064 :
    ThetaLowerSegment 19960064 19976448 (997745607827 / 50000) (998535641637 / 50000) := by
  exact
    packedTile8192 19960064 19976448 11 940 4467 24 _ _ (1680923 / 100000) (840463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19976448 :
    ThetaLowerSegment 19976448 19992832 (998535641637 / 50000) (999376144137 / 50000) := by
  exact
    packedTile8192 19976448 19992832 11 1000 4469 24 _ _ (336201 / 20000) (105063 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell19992832 :
    ThetaLowerSegment 19992832 20009216 (999376144137 / 50000) (2000384623751 / 100000) := by
  exact
    packedTile8192 19992832 20009216 11 971 4471 24 _ _ (1681087 / 100000) (168109 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20009216 :
    ThetaLowerSegment 20009216 20025600 (2000384623751 / 100000) (250253390733 / 12500) := by
  exact
    packedTile8192 20009216 20025600 11 977 4473 24 _ _ (1681169 / 100000) (420293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20025600 :
    ThetaLowerSegment 20025600 20041984 (250253390733 / 12500) (2003716783119 / 100000) := by
  exact
    packedTile8192 20025600 20041984 11 1005 4474 24 _ _ (1681251 / 100000) (840627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20041984 :
    ThetaLowerSegment 20041984 20058368 (2003716783119 / 100000) (2005342631163 / 100000) := by
  exact
    packedTile8192 20041984 20058368 11 967 4476 24 _ _ (420333 / 25000) (336267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20058368 :
    ThetaLowerSegment 20058368 20074752 (2005342631163 / 100000) (2006998823953 / 100000) := by
  exact
    packedTile8192 20058368 20074752 11 985 4478 24 _ _ (840707 / 50000) (1681417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20074752 :
    ThetaLowerSegment 20074752 20091136 (2006998823953 / 100000) (2008631556569 / 100000) := by
  exact
    packedTile8192 20074752 20091136 11 971 4480 24 _ _ (210187 / 12500) (1681499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20091136 :
    ThetaLowerSegment 20091136 20107520 (2008631556569 / 100000) (16082209111 / 800) := by
  exact
    packedTile8192 20091136 20107520 11 978 4482 24 _ _ (1681577 / 100000) (84079 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20107520 :
    ThetaLowerSegment 20107520 20123904 (16082209111 / 800) (251484424573 / 12500) := by
  exact
    packedTile8192 20107520 20123904 11 951 4484 24 _ _ (1681659 / 100000) (840831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20123904 :
    ThetaLowerSegment 20123904 20140288 (251484424573 / 12500) (251683710763 / 12500) := by
  exact
    packedTile8192 20123904 20140288 11 948 4485 24 _ _ (84087 / 5000) (1681743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20140288 :
    ThetaLowerSegment 20140288 20156672 (251683710763 / 12500) (1007558094921 / 50000) := by
  exact
    packedTile8192 20140288 20156672 11 979 4487 24 _ _ (840911 / 50000) (67273 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20156672 :
    ThetaLowerSegment 20156672 20173056 (1007558094921 / 50000) (504205409871 / 25000) := by
  exact
    packedTile8192 20156672 20173056 11 1014 4489 24 _ _ (1681903 / 100000) (840953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20173056 :
    ThetaLowerSegment 20173056 20189440 (504205409871 / 25000) (504615393471 / 25000) := by
  exact
    packedTile8192 20173056 20189440 11 975 4491 24 _ _ (52562 / 3125) (1681987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20189440 :
    ThetaLowerSegment 20189440 20205824 (504615393471 / 25000) (1010035655523 / 50000) := by
  exact
    packedTile8192 20189440 20205824 11 957 4493 24 _ _ (841033 / 50000) (1682069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20205824 :
    ThetaLowerSegment 20205824 20222208 (1010035655523 / 50000) (1010829628907 / 50000) := by
  exact
    packedTile8192 20205824 20222208 11 944 4495 24 _ _ (1682147 / 100000) (33643 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20222208 :
    ThetaLowerSegment 20222208 20238592 (1010829628907 / 50000) (1011650556171 / 50000) := by
  exact
    packedTile8192 20222208 20238592 11 976 4496 24 _ _ (420557 / 25000) (1682231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20238592 :
    ThetaLowerSegment 20238592 20254976 (1011650556171 / 50000) (1012471522963 / 50000) := by
  exact
    packedTile8192 20238592 20254976 11 976 4498 24 _ _ (1682309 / 100000) (210289 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20254976 :
    ThetaLowerSegment 20254976 20271360 (1012471522963 / 50000) (506636590899 / 25000) := by
  exact
    packedTile8192 20254976 20271360 11 953 4500 24 _ _ (168239 / 10000) (1682393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20271360 :
    ThetaLowerSegment 20271360 20287744 (506636590899 / 25000) (1014105163213 / 50000) := by
  exact
    packedTile8192 20271360 20287744 11 989 4502 24 _ _ (168247 / 10000) (1682473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20287744 :
    ThetaLowerSegment 20287744 20304128 (1014105163213 / 50000) (2029810432427 / 100000) := by
  exact
    packedTile8192 20287744 20304128 11 951 4504 24 _ _ (1682551 / 100000) (841277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20304128 :
    ThetaLowerSegment 20304128 20320512 (2029810432427 / 100000) (2031494747059 / 100000) := by
  exact
    packedTile8192 20304128 20320512 11 1001 4506 24 _ _ (210329 / 12500) (336527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20320512 :
    ThetaLowerSegment 20320512 20336896 (2031494747059 / 100000) (406615972541 / 20000) := by
  exact
    packedTile8192 20320512 20336896 11 942 4507 24 _ _ (1682713 / 100000) (420679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20336896 :
    ThetaLowerSegment 20336896 20353280 (406615972541 / 20000) (1017361975733 / 50000) := by
  exact
    packedTile8192 20336896 20353280 11 977 4509 24 _ _ (1682793 / 100000) (420699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20353280 :
    ThetaLowerSegment 20353280 20369664 (1017361975733 / 50000) (254549801387 / 12500) := by
  exact
    packedTile8192 20353280 20369664 11 995 4511 24 _ _ (841437 / 50000) (1682877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20369664 :
    ThetaLowerSegment 20369664 20386048 (254549801387 / 12500) (10190204871 / 500) := by
  exact
    packedTile8192 20369664 20386048 11 976 4513 24 _ _ (841477 / 50000) (1682957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20386048 :
    ThetaLowerSegment 20386048 20402432 (10190204871 / 500) (407932347381 / 20000) := by
  exact
    packedTile8192 20386048 20402432 11 963 4515 24 _ _ (336607 / 20000) (841519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20402432 :
    ThetaLowerSegment 20402432 20418816 (407932347381 / 20000) (81650293197 / 4000) := by
  exact
    packedTile8192 20402432 20418816 11 948 4516 24 _ _ (336623 / 20000) (841559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20418816 :
    ThetaLowerSegment 20418816 20427008 (81650293197 / 4000) (408415745817 / 20000) := by
  exact
    packedTile8192 20418816 20427008 10 488 4518 24 _ _ (336639 / 20000) (841599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20427008 :
    ThetaLowerSegment 20427008 20435200 (408415745817 / 20000) (81715063299 / 4000) := by
  exact
    packedTile8192 20427008 20435200 10 474 4519 24 _ _ (336647 / 20000) (841619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20435200 :
    ThetaLowerSegment 20435200 20443392 (81715063299 / 4000) (40872916783 / 2000) := by
  exact
    packedTile8192 20435200 20443392 10 457 4520 24 _ _ (67331 / 4000) (841639 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20443392 :
    ThetaLowerSegment 20443392 20451584 (40872916783 / 2000) (1022244590233 / 50000) := by
  exact
    packedTile8192 20443392 20451584 10 501 4521 24 _ _ (420829 / 25000) (1683319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20451584 :
    ThetaLowerSegment 20451584 20459776 (1022244590233 / 50000) (1022662904199 / 50000) := by
  exact
    packedTile8192 20451584 20459776 10 497 4522 24 _ _ (420839 / 25000) (1683359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20459776 :
    ThetaLowerSegment 20459776 20467968 (1022662904199 / 50000) (1023071969427 / 50000) := by
  exact
    packedTile8192 20459776 20467968 10 486 4523 24 _ _ (420849 / 25000) (1683399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20467968 :
    ThetaLowerSegment 20467968 20476160 (1023071969427 / 50000) (1023481886093 / 50000) := by
  exact
    packedTile8192 20467968 20476160 10 487 4524 24 _ _ (420859 / 25000) (1683439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20476160 :
    ThetaLowerSegment 20476160 20484352 (1023481886093 / 50000) (204776173981 / 10000) := by
  exact
    packedTile8192 20476160 20484352 10 474 4525 24 _ _ (420869 / 25000) (1683479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20484352 :
    ThetaLowerSegment 20484352 20492544 (204776173981 / 10000) (1024286597261 / 50000) := by
  exact
    packedTile8192 20484352 20492544 10 482 4525 24 _ _ (420879 / 25000) (1683519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20492544 :
    ThetaLowerSegment 20492544 20500736 (1024286597261 / 50000) (204940318763 / 10000) := by
  exact
    packedTile8192 20492544 20500736 10 493 4526 24 _ _ (420889 / 25000) (1683559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20500736 :
    ThetaLowerSegment 20500736 20508928 (204940318763 / 10000) (1025119125623 / 50000) := by
  exact
    packedTile8192 20500736 20508928 10 496 4527 24 _ _ (420899 / 25000) (1683599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20508928 :
    ThetaLowerSegment 20508928 20517120 (1025119125623 / 50000) (205105313107 / 10000) := by
  exact
    packedTile8192 20508928 20517120 10 484 4528 24 _ _ (420909 / 25000) (1683639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20517120 :
    ThetaLowerSegment 20517120 20525312 (205105313107 / 10000) (1025953377401 / 50000) := by
  exact
    packedTile8192 20517120 20525312 10 507 4529 24 _ _ (420919 / 25000) (1683679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20525312 :
    ThetaLowerSegment 20525312 20541696 (1025953377401 / 50000) (2053518070057 / 100000) := by
  exact
    packedTile8192 20525312 20541696 11 957 4530 24 _ _ (336743 / 20000) (841859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20541696 :
    ThetaLowerSegment 20541696 20549888 (2053518070057 / 100000) (1027169039111 / 50000) := by
  exact
    packedTile8192 20541696 20549888 10 487 4532 24 _ _ (336759 / 20000) (841899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20549888 :
    ThetaLowerSegment 20549888 20558080 (1027169039111 / 50000) (1027579894851 / 50000) := by
  exact
    packedTile8192 20549888 20558080 10 488 4533 24 _ _ (336767 / 20000) (841919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20558080 :
    ThetaLowerSegment 20558080 20566272 (1027579894851 / 50000) (2055969733577 / 100000) := by
  exact
    packedTile8192 20558080 20566272 10 481 4534 24 _ _ (13471 / 800) (841939 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20566272 :
    ThetaLowerSegment 20566272 20574464 (2055969733577 / 100000) (257103355789 / 12500) := by
  exact
    packedTile8192 20566272 20574464 10 509 4535 24 _ _ (336783 / 20000) (841959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20574464 :
    ThetaLowerSegment 20574464 20590848 (257103355789 / 12500) (2058461966617 / 100000) := by
  exact
    packedTile8192 20574464 20590848 11 971 4535 24 _ _ (336791 / 20000) (841979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20590848 :
    ThetaLowerSegment 20590848 20607232 (2058461966617 / 100000) (412014717431 / 20000) := by
  exact
    packedTile8192 20590848 20607232 11 957 4537 24 _ _ (842017 / 50000) (1684037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20607232 :
    ThetaLowerSegment 20607232 20615424 (412014717431 / 20000) (2060905539471 / 100000) := by
  exact
    packedTile8192 20607232 20615424 10 494 4539 24 _ _ (842057 / 50000) (1684117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20615424 :
    ThetaLowerSegment 20615424 20623616 (2060905539471 / 100000) (2061710565083 / 100000) := by
  exact
    packedTile8192 20615424 20623616 10 478 4540 24 _ _ (842077 / 50000) (1684157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20623616 :
    ThetaLowerSegment 20623616 20631808 (2061710565083 / 100000) (2062566135127 / 100000) := by
  exact
    packedTile8192 20623616 20631808 10 508 4541 24 _ _ (1684193 / 100000) (421049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20631808 :
    ThetaLowerSegment 20631808 20648192 (2062566135127 / 100000) (1032070446491 / 50000) := by
  exact
    packedTile8192 20631808 20648192 11 935 4542 24 _ _ (1684233 / 100000) (421059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20648192 :
    ThetaLowerSegment 20648192 20656384 (1032070446491 / 50000) (1032491524491 / 50000) := by
  exact
    packedTile8192 20648192 20656384 10 500 4544 24 _ _ (210539 / 12500) (336863 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20656384 :
    ThetaLowerSegment 20656384 20664576 (1032491524491 / 50000) (1032887347211 / 50000) := by
  exact
    packedTile8192 20656384 20664576 10 470 4544 24 _ _ (52636 / 3125) (336871 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20664576 :
    ThetaLowerSegment 20664576 20672768 (1032887347211 / 50000) (206660678407 / 10000) := by
  exact
    packedTile8192 20664576 20672768 10 494 4545 24 _ _ (210549 / 12500) (336879 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20672768 :
    ThetaLowerSegment 20672768 20680960 (206660678407 / 10000) (206748268819 / 10000) := by
  exact
    packedTile8192 20672768 20680960 10 520 4546 24 _ _ (1684431 / 100000) (842217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20680960 :
    ThetaLowerSegment 20680960 20697344 (206748268819 / 10000) (2069155367893 / 100000) := by
  exact
    packedTile8192 20680960 20697344 11 993 4547 24 _ _ (1684471 / 100000) (842237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20697344 :
    ThetaLowerSegment 20697344 20713728 (2069155367893 / 100000) (2070853394293 / 100000) := by
  exact
    packedTile8192 20697344 20713728 11 1008 4549 24 _ _ (33691 / 2000) (1684553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20713728 :
    ThetaLowerSegment 20713728 20730112 (2070853394293 / 100000) (414496823033 / 20000) := by
  exact
    packedTile8192 20713728 20730112 11 968 4551 24 _ _ (1684629 / 100000) (210579 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20730112 :
    ThetaLowerSegment 20730112 20746496 (414496823033 / 20000) (414818602261 / 20000) := by
  exact
    packedTile8192 20730112 20746496 11 955 4553 24 _ _ (421177 / 25000) (1684711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20746496 :
    ThetaLowerSegment 20746496 20762880 (414818602261 / 20000) (129734954103 / 6250) := by
  exact
    packedTile8192 20746496 20762880 11 989 4554 24 _ _ (1684787 / 100000) (168479 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20762880 :
    ThetaLowerSegment 20762880 20779264 (129734954103 / 6250) (1038695950401 / 50000) := by
  exact
    packedTile8192 20762880 20779264 11 969 4556 24 _ _ (842433 / 50000) (1684869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20779264 :
    ThetaLowerSegment 20779264 20795648 (1038695950401 / 50000) (1039501354111 / 50000) := by
  exact
    packedTile8192 20779264 20795648 11 956 4558 24 _ _ (336989 / 20000) (421237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20795648 :
    ThetaLowerSegment 20795648 20812032 (1039501354111 / 50000) (1040314378191 / 50000) := by
  exact
    packedTile8192 20795648 20812032 11 965 4560 24 _ _ (52657 / 3125) (1685027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20812032 :
    ThetaLowerSegment 20812032 20828416 (1040314378191 / 50000) (1041116487219 / 50000) := by
  exact
    packedTile8192 20812032 20828416 11 952 4562 24 _ _ (1685103 / 100000) (842553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20828416 :
    ThetaLowerSegment 20828416 20844800 (1041116487219 / 50000) (1041948966633 / 50000) := by
  exact
    packedTile8192 20828416 20844800 11 988 4563 24 _ _ (1685181 / 100000) (52662 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20844800 :
    ThetaLowerSegment 20844800 20861184 (1041948966633 / 50000) (1042754520913 / 50000) := by
  exact
    packedTile8192 20844800 20861184 11 956 4565 24 _ _ (84263 / 5000) (1685263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20861184 :
    ThetaLowerSegment 20861184 20877568 (1042754520913 / 50000) (1043580337023 / 50000) := by
  exact
    packedTile8192 20861184 20877568 11 980 4567 24 _ _ (1685339 / 100000) (842671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20877568 :
    ThetaLowerSegment 20877568 20893952 (1043580337023 / 50000) (2088814068123 / 100000) := by
  exact
    packedTile8192 20877568 20893952 11 981 4569 24 _ _ (1685417 / 100000) (84271 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20893952 :
    ThetaLowerSegment 20893952 20910336 (2088814068123 / 100000) (418083732063 / 20000) := by
  exact
    packedTile8192 20893952 20910336 11 952 4570 24 _ _ (210687 / 12500) (1685499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20910336 :
    ThetaLowerSegment 20910336 20926720 (418083732063 / 20000) (2092057038243 / 100000) := by
  exact
    packedTile8192 20910336 20926720 11 972 4572 24 _ _ (842787 / 50000) (1685577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20926720 :
    ThetaLowerSegment 20926720 20943104 (2092057038243 / 100000) (2093655036339 / 100000) := by
  exact
    packedTile8192 20926720 20943104 11 948 4574 24 _ _ (421413 / 25000) (337131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20943104 :
    ThetaLowerSegment 20943104 20951296 (2093655036339 / 100000) (2094492844149 / 100000) := by
  exact
    packedTile8192 20943104 20951296 10 497 4576 24 _ _ (168573 / 10000) (1685733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20951296 :
    ThetaLowerSegment 20951296 20967680 (2094492844149 / 100000) (2096131412589 / 100000) := by
  exact
    packedTile8192 20951296 20967680 11 972 4577 24 _ _ (168577 / 10000) (1685773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20967680 :
    ThetaLowerSegment 20967680 20984064 (2096131412589 / 100000) (2097788601173 / 100000) := by
  exact
    packedTile8192 20967680 20984064 11 983 4579 24 _ _ (210731 / 12500) (1685851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell20984064 :
    ThetaLowerSegment 20984064 21000448 (2097788601173 / 100000) (2099407090133 / 100000) := by
  exact
    packedTile8192 20984064 21000448 11 960 4580 24 _ _ (842963 / 50000) (1685929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21000448 :
    ThetaLowerSegment 21000448 21016832 (2099407090133 / 100000) (2101111640177 / 100000) := by
  exact
    packedTile8192 21000448 21016832 11 1011 4582 24 _ _ (421501 / 25000) (1686007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21016832 :
    ThetaLowerSegment 21016832 21033216 (2101111640177 / 100000) (2102731964979 / 100000) := by
  exact
    packedTile8192 21016832 21033216 11 961 4584 24 _ _ (843041 / 50000) (337217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21033216 :
    ThetaLowerSegment 21033216 21049600 (2102731964979 / 100000) (2104374284819 / 100000) := by
  exact
    packedTile8192 21033216 21049600 11 974 4586 24 _ _ (21077 / 1250) (1686163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21049600 :
    ThetaLowerSegment 21049600 21065984 (2104374284819 / 100000) (2106033543011 / 100000) := by
  exact
    packedTile8192 21049600 21065984 11 984 4587 24 _ _ (843119 / 50000) (1686241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21065984 :
    ThetaLowerSegment 21065984 21082368 (2106033543011 / 100000) (421531830327 / 20000) := by
  exact
    packedTile8192 21065984 21082368 11 964 4589 24 _ _ (421579 / 25000) (1686319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21082368 :
    ThetaLowerSegment 21082368 21098752 (421531830327 / 20000) (105462639651 / 5000) := by
  exact
    packedTile8192 21082368 21098752 11 945 4591 24 _ _ (1686393 / 100000) (421599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21098752 :
    ThetaLowerSegment 21098752 21115136 (105462639651 / 5000) (527724697179 / 25000) := by
  exact
    packedTile8192 21098752 21115136 11 976 4593 24 _ _ (1686471 / 100000) (843237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21115136 :
    ThetaLowerSegment 21115136 21131520 (527724697179 / 25000) (2112543173991 / 100000) := by
  exact
    packedTile8192 21115136 21131520 11 975 4595 24 _ _ (1686549 / 100000) (210819 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21131520 :
    ThetaLowerSegment 21131520 21147904 (2112543173991 / 100000) (2114206187227 / 100000) := by
  exact
    packedTile8192 21131520 21147904 11 986 4596 24 _ _ (843313 / 50000) (1686629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21147904 :
    ThetaLowerSegment 21147904 21164288 (2114206187227 / 100000) (2115747834683 / 100000) := by
  exact
    packedTile8192 21147904 21164288 11 914 4598 24 _ _ (105419 / 6250) (1686707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21164288 :
    ThetaLowerSegment 21164288 21172480 (2115747834683 / 100000) (42332060653 / 2000) := by
  exact
    packedTile8192 21164288 21172480 10 507 4600 24 _ _ (1686781 / 100000) (52712 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21172480 :
    ThetaLowerSegment 21172480 21188864 (42332060653 / 2000) (211821563257 / 10000) := by
  exact
    packedTile8192 21172480 21188864 11 956 4601 24 _ _ (84341 / 5000) (1686823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21188864 :
    ThetaLowerSegment 21188864 21197056 (211821563257 / 10000) (1059526166741 / 50000) := by
  exact
    packedTile8192 21188864 21197056 10 496 4603 24 _ _ (1686897 / 100000) (16869 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21197056 :
    ThetaLowerSegment 21197056 21213440 (1059526166741 / 50000) (1060329148277 / 50000) := by
  exact
    packedTile8192 21197056 21213440 11 952 4604 24 _ _ (210867 / 12500) (1686939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21213440 :
    ThetaLowerSegment 21213440 21221632 (1060329148277 / 50000) (2121486619937 / 100000) := by
  exact
    packedTile8192 21213440 21221632 10 491 4605 24 _ _ (1687013 / 100000) (210877 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21221632 :
    ThetaLowerSegment 21221632 21229824 (2121486619937 / 100000) (2122276160273 / 100000) := by
  exact
    packedTile8192 21221632 21229824 10 468 4606 24 _ _ (421763 / 25000) (337411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21229824 :
    ThetaLowerSegment 21229824 21238016 (2122276160273 / 100000) (2123091024743 / 100000) := by
  exact
    packedTile8192 21229824 21238016 10 483 4607 24 _ _ (168709 / 10000) (1687093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21238016 :
    ThetaLowerSegment 21238016 21246208 (2123091024743 / 100000) (424776120223 / 20000) := by
  exact
    packedTile8192 21238016 21246208 10 468 4608 24 _ _ (1687129 / 100000) (421783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21246208 :
    ThetaLowerSegment 21246208 21254400 (424776120223 / 20000) (531185685863 / 25000) := by
  exact
    packedTile8192 21246208 21254400 10 511 4609 24 _ _ (1687167 / 100000) (168717 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21254400 :
    ThetaLowerSegment 21254400 21262592 (531185685863 / 25000) (1062777144769 / 50000) := by
  exact
    packedTile8192 21254400 21262592 10 481 4610 24 _ _ (843603 / 50000) (1687209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21262592 :
    ThetaLowerSegment 21262592 21270784 (1062777144769 / 50000) (212640297327 / 10000) := by
  exact
    packedTile8192 21262592 21270784 10 503 4611 24 _ _ (421811 / 25000) (1687247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21270784 :
    ThetaLowerSegment 21270784 21278976 (212640297327 / 10000) (212724661477 / 10000) := by
  exact
    packedTile8192 21270784 21278976 10 500 4612 24 _ _ (1687283 / 100000) (843643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21278976 :
    ThetaLowerSegment 21278976 21295360 (212724661477 / 10000) (266114843859 / 12500) := by
  exact
    packedTile8192 21278976 21295360 11 991 4612 24 _ _ (843661 / 50000) (67493 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21295360 :
    ThetaLowerSegment 21295360 21311744 (266114843859 / 12500) (1065273544971 / 50000) := by
  exact
    packedTile8192 21295360 21311744 11 965 4614 24 _ _ (843699 / 50000) (1687401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21311744 :
    ThetaLowerSegment 21311744 21328128 (1065273544971 / 50000) (66630959081 / 3125) := by
  exact
    packedTile8192 21311744 21328128 11 974 4616 24 _ _ (67499 / 4000) (843739 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21328128 :
    ThetaLowerSegment 21328128 21344512 (66630959081 / 3125) (13336412053 / 625) := by
  exact
    packedTile8192 21328128 21344512 11 969 4618 24 _ _ (52736 / 3125) (337511 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21344512 :
    ThetaLowerSegment 21344512 21360896 (13336412053 / 625) (2135447739949 / 100000) := by
  exact
    packedTile8192 21344512 21360896 11 961 4620 24 _ _ (1687629 / 100000) (105477 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21360896 :
    ThetaLowerSegment 21360896 21377280 (2135447739949 / 100000) (2137076376239 / 100000) := by
  exact
    packedTile8192 21360896 21377280 11 965 4621 24 _ _ (843853 / 50000) (1687709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21377280 :
    ThetaLowerSegment 21377280 21393664 (2137076376239 / 100000) (2138745592637 / 100000) := by
  exact
    packedTile8192 21377280 21393664 11 989 4623 24 _ _ (843891 / 50000) (337557 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21393664 :
    ThetaLowerSegment 21393664 21410048 (2138745592637 / 100000) (21403608737 / 1000) := by
  exact
    packedTile8192 21393664 21410048 11 957 4625 24 _ _ (1687859 / 100000) (843931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21410048 :
    ThetaLowerSegment 21410048 21426432 (21403608737 / 1000) (535491525209 / 25000) := by
  exact
    packedTile8192 21410048 21426432 11 951 4627 24 _ _ (52748 / 3125) (1687939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21426432 :
    ThetaLowerSegment 21426432 21434624 (535491525209 / 25000) (535697462673 / 25000) := by
  exact
    packedTile8192 21426432 21434624 10 488 4628 24 _ _ (422003 / 25000) (337603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21434624 :
    ThetaLowerSegment 21434624 21451008 (535697462673 / 25000) (1072222913871 / 50000) := by
  exact
    packedTile8192 21434624 21451008 11 981 4629 24 _ _ (33761 / 2000) (1688053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21451008 :
    ThetaLowerSegment 21451008 21467392 (1072222913871 / 50000) (2146155900393 / 100000) := by
  exact
    packedTile8192 21451008 21467392 11 1013 4631 24 _ _ (1688127 / 100000) (168813 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21467392 :
    ThetaLowerSegment 21467392 21483776 (2146155900393 / 100000) (2147823844957 / 100000) := by
  exact
    packedTile8192 21467392 21483776 11 988 4633 24 _ _ (1688203 / 100000) (844103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21483776 :
    ThetaLowerSegment 21483776 21500160 (2147823844957 / 100000) (2149461475587 / 100000) := by
  exact
    packedTile8192 21483776 21500160 11 970 4635 24 _ _ (1688279 / 100000) (844141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21500160 :
    ThetaLowerSegment 21500160 21516544 (2149461475587 / 100000) (2151014763107 / 100000) := by
  exact
    packedTile8192 21500160 21516544 11 920 4636 24 _ _ (422089 / 25000) (1688359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21516544 :
    ThetaLowerSegment 21516544 21532928 (2151014763107 / 100000) (2152649165283 / 100000) := by
  exact
    packedTile8192 21516544 21532928 11 968 4638 24 _ _ (105527 / 6250) (337687 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21532928 :
    ThetaLowerSegment 21532928 21549312 (2152649165283 / 100000) (2154295460583 / 100000) := by
  exact
    packedTile8192 21532928 21549312 11 975 4640 24 _ _ (422127 / 25000) (1688511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21549312 :
    ThetaLowerSegment 21549312 21557504 (2154295460583 / 100000) (2155090783647 / 100000) := by
  exact
    packedTile8192 21549312 21557504 10 471 4642 24 _ _ (211073 / 12500) (1688587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21557504 :
    ThetaLowerSegment 21557504 21561600 (2155090783647 / 100000) (2155531513989 / 100000) := by
  exact
    packedTile8192 21557504 21561600 9 261 4643 24 _ _ (844311 / 50000) (13509 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21561600 :
    ThetaLowerSegment 21561600 21563648 (2155531513989 / 100000) (107785947657 / 5000) := by
  exact
    packedTile8192 21561600 21563648 8 111 4643 24 _ _ (1688641 / 100000) (422161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_13922560_21563648 :
    ThetaLowerSegment 13922560 21563648 (1391841141353 / 100000) (107785947657 / 5000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell13922560 cell13930752)
                      (ThetaLowerSegment.join cell13938944 cell13947136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell13955328 cell13963520)
                      (ThetaLowerSegment.join cell13971712 cell13979904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell13988096 cell13996288)
                      (ThetaLowerSegment.join cell14004480 cell14012672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14020864 cell14029056)
                      (ThetaLowerSegment.join cell14037248 cell14045440))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14053632 cell14061824)
                      (ThetaLowerSegment.join cell14070016 cell14078208))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14086400 cell14094592)
                      (ThetaLowerSegment.join cell14102784 cell14110976)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14119168 cell14127360)
                      (ThetaLowerSegment.join cell14135552 cell14143744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14151936 cell14160128)
                      (ThetaLowerSegment.join cell14168320 cell14176512)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14184704 cell14192896)
                      (ThetaLowerSegment.join cell14201088 cell14209280))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14217472 cell14225664)
                      (ThetaLowerSegment.join cell14233856 cell14242048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14250240 cell14258432)
                      (ThetaLowerSegment.join cell14266624 cell14274816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14283008 cell14291200)
                      (ThetaLowerSegment.join cell14299392 cell14307584))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14315776 cell14323968)
                      (ThetaLowerSegment.join cell14332160 cell14340352))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14348544 cell14356736)
                      (ThetaLowerSegment.join cell14364928 cell14373120)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14381312 cell14389504)
                      (ThetaLowerSegment.join cell14397696 cell14405888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14414080 cell14422272)
                      (ThetaLowerSegment.join cell14430464 cell14438656))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14446848 cell14455040)
                      (ThetaLowerSegment.join cell14463232 cell14471424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14479616 cell14487808)
                      (ThetaLowerSegment.join cell14496000 cell14504192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14512384 cell14520576)
                      (ThetaLowerSegment.join cell14528768 cell14536960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14545152 cell14553344)
                      (ThetaLowerSegment.join cell14561536 cell14569728))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14577920 cell14586112)
                      (ThetaLowerSegment.join cell14594304 cell14602496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14610688 cell14618880)
                      (ThetaLowerSegment.join cell14627072 cell14635264)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14643456 cell14651648)
                      (ThetaLowerSegment.join cell14659840 cell14668032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14676224 cell14684416)
                      (ThetaLowerSegment.join cell14692608 cell14700800)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14708992 cell14717184)
                      (ThetaLowerSegment.join cell14725376 cell14733568))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14741760 cell14749952)
                      (ThetaLowerSegment.join cell14758144 cell14766336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14774528 cell14782720)
                      (ThetaLowerSegment.join cell14790912 cell14799104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14807296 cell14815488)
                      (ThetaLowerSegment.join cell14823680 cell14831872))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14840064 cell14848256)
                      (ThetaLowerSegment.join cell14856448 cell14864640))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14872832 cell14881024)
                      (ThetaLowerSegment.join cell14889216 cell14897408)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14905600 cell14913792)
                      (ThetaLowerSegment.join cell14921984 cell14930176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14938368 cell14946560)
                      (ThetaLowerSegment.join cell14954752 cell14962944)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell14971136 cell14979328)
                      (ThetaLowerSegment.join cell14987520 cell14995712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15003904 cell15012096)
                      (ThetaLowerSegment.join cell15020288 cell15028480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15036672 cell15044864)
                      (ThetaLowerSegment.join cell15053056 cell15061248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15069440 cell15077632)
                      (ThetaLowerSegment.join cell15085824 cell15094016))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15102208 cell15110400)
                      (ThetaLowerSegment.join cell15118592 cell15126784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15134976 cell15143168)
                      (ThetaLowerSegment.join cell15151360 cell15159552)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15167744 cell15175936)
                      (ThetaLowerSegment.join cell15184128 cell15192320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15200512 cell15208704)
                      (ThetaLowerSegment.join cell15216896 cell15225088)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15233280 cell15241472)
                      (ThetaLowerSegment.join cell15249664 cell15257856))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15266048 cell15274240)
                      (ThetaLowerSegment.join cell15282432 cell15290624)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15298816 cell15307008)
                      (ThetaLowerSegment.join cell15315200 cell15323392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15331584 cell15339776)
                      (ThetaLowerSegment.join cell15347968 cell15356160))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15364352 cell15372544)
                      (ThetaLowerSegment.join cell15380736 cell15388928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15397120 cell15405312)
                      (ThetaLowerSegment.join cell15413504 cell15421696)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15429888 cell15438080)
                      (ThetaLowerSegment.join cell15446272 cell15454464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15462656 cell15470848)
                      (ThetaLowerSegment.join cell15479040 cell15487232))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15495424 cell15503616)
                      (ThetaLowerSegment.join cell15511808 cell15520000))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15528192 cell15536384)
                      (ThetaLowerSegment.join cell15544576 cell15552768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15560960 cell15569152)
                      (ThetaLowerSegment.join cell15577344 cell15585536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15593728 cell15601920)
                      (ThetaLowerSegment.join cell15610112 cell15618304))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15626496 cell15634688)
                      (ThetaLowerSegment.join cell15642880 cell15651072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15659264 cell15667456)
                      (ThetaLowerSegment.join cell15675648 cell15683840)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15692032 cell15700224)
                      (ThetaLowerSegment.join cell15708416 cell15716608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15724800 cell15732992)
                      (ThetaLowerSegment.join cell15741184 cell15749376)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15757568 cell15765760)
                      (ThetaLowerSegment.join cell15773952 cell15782144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15790336 cell15798528)
                      (ThetaLowerSegment.join cell15806720 cell15814912)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15823104 cell15831296)
                      (ThetaLowerSegment.join cell15839488 cell15847680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15855872 cell15864064)
                      (ThetaLowerSegment.join cell15872256 cell15880448))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15888640 cell15896832)
                      (ThetaLowerSegment.join cell15905024 cell15913216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15921408 cell15929600)
                      (ThetaLowerSegment.join cell15937792 cell15945984)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15954176 cell15962368)
                      (ThetaLowerSegment.join cell15970560 cell15978752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell15986944 cell15995136)
                      (ThetaLowerSegment.join cell16003328 cell16011520))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16019712 cell16027904)
                      (ThetaLowerSegment.join cell16036096 cell16044288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16052480 cell16060672)
                      (ThetaLowerSegment.join cell16068864 cell16077056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16085248 cell16093440)
                      (ThetaLowerSegment.join cell16101632 cell16109824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16118016 cell16126208)
                      (ThetaLowerSegment.join cell16134400 cell16142592))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16150784 cell16158976)
                      (ThetaLowerSegment.join cell16167168 cell16175360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16183552 cell16191744)
                      (ThetaLowerSegment.join cell16199936 cell16208128)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16216320 cell16224512)
                      (ThetaLowerSegment.join cell16232704 cell16240896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16249088 cell16257280)
                      (ThetaLowerSegment.join cell16265472 cell16273664)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16281856 cell16290048)
                      (ThetaLowerSegment.join cell16298240 cell16306432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16314624 cell16322816)
                      (ThetaLowerSegment.join cell16331008 cell16339200)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16347392 cell16355584)
                      (ThetaLowerSegment.join cell16363776 cell16371968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16380160 cell16388352)
                      (ThetaLowerSegment.join cell16396544 cell16404736))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16412928 cell16421120)
                      (ThetaLowerSegment.join cell16429312 cell16437504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16445696 cell16453888)
                      (ThetaLowerSegment.join cell16462080 cell16470272)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16478464 cell16486656)
                      (ThetaLowerSegment.join cell16494848 cell16503040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16511232 cell16519424)
                      (ThetaLowerSegment.join cell16527616 cell16535808))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16544000 cell16552192)
                      (ThetaLowerSegment.join cell16560384 cell16568576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16576768 cell16584960)
                      (ThetaLowerSegment.join cell16593152 cell16601344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16609536 cell16617728)
                      (ThetaLowerSegment.join cell16625920 cell16634112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16642304 cell16650496)
                      (ThetaLowerSegment.join cell16658688 cell16666880))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16675072 cell16683264)
                      (ThetaLowerSegment.join cell16691456 cell16699648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16707840 cell16716032)
                      (ThetaLowerSegment.join cell16724224 cell16732416)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16740608 cell16748800)
                      (ThetaLowerSegment.join cell16756992 cell16765184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16773376 cell16781568)
                      (ThetaLowerSegment.join cell16789760 cell16797952)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16806144 cell16814336)
                      (ThetaLowerSegment.join cell16822528 cell16830720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16838912 cell16847104)
                      (ThetaLowerSegment.join cell16855296 cell16863488)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16871680 cell16879872)
                      (ThetaLowerSegment.join cell16888064 cell16896256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16904448 cell16912640)
                      (ThetaLowerSegment.join cell16920832 cell16929024))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16937216 cell16945408)
                      (ThetaLowerSegment.join cell16953600 cell16961792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell16969984 cell16978176)
                      (ThetaLowerSegment.join cell16986368 cell16994560)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17002752 cell17010944)
                      (ThetaLowerSegment.join cell17019136 cell17027328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17035520 cell17043712)
                      (ThetaLowerSegment.join cell17051904 cell17060096)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17068288 cell17076480)
                      (ThetaLowerSegment.join cell17084672 cell17092864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17101056 cell17109248)
                      (ThetaLowerSegment.join cell17117440 cell17125632)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17133824 cell17142016)
                      (ThetaLowerSegment.join cell17150208 cell17158400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17166592 cell17174784)
                      (ThetaLowerSegment.join cell17182976 cell17191168))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17199360 cell17207552)
                      (ThetaLowerSegment.join cell17215744 cell17223936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17232128 cell17240320)
                      (ThetaLowerSegment.join cell17248512 cell17256704)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17264896 cell17273088)
                      (ThetaLowerSegment.join cell17281280 cell17289472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17297664 cell17305856)
                      (ThetaLowerSegment.join cell17314048 cell17322240)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17330432 cell17338624)
                      (ThetaLowerSegment.join cell17346816 cell17355008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17363200 cell17371392)
                      (ThetaLowerSegment.join cell17379584 cell17387776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17395968 cell17404160)
                      (ThetaLowerSegment.join cell17412352 cell17420544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17428736 cell17436928)
                      (ThetaLowerSegment.join cell17445120 cell17453312))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17461504 cell17469696)
                      (ThetaLowerSegment.join cell17477888 cell17486080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17502464 cell17518848)
                      (ThetaLowerSegment.join cell17535232 cell17551616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17568000 cell17584384)
                      (ThetaLowerSegment.join cell17600768 cell17617152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17633536 cell17649920)
                      (ThetaLowerSegment.join cell17666304 cell17682688))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17699072 cell17715456)
                      (ThetaLowerSegment.join cell17731840 cell17748224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17756416 cell17764608)
                      (ThetaLowerSegment.join cell17772800 cell17780992)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17789184 cell17805568)
                      (ThetaLowerSegment.join cell17821952 cell17838336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17846528 cell17854720)
                      (ThetaLowerSegment.join cell17862912 cell17871104))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17887488 cell17895680)
                      (ThetaLowerSegment.join cell17903872 cell17912064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17920256 cell17928448)
                      (ThetaLowerSegment.join cell17936640 cell17944832)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell17953024 cell17969408)
                      (ThetaLowerSegment.join cell17985792 cell18002176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18018560 cell18034944)
                      (ThetaLowerSegment.join cell18051328 cell18067712)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18084096 cell18100480)
                      (ThetaLowerSegment.join cell18108672 cell18125056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18133248 cell18141440)
                      (ThetaLowerSegment.join cell18157824 cell18166016)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18174208 cell18182400)
                      (ThetaLowerSegment.join cell18190592 cell18198784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18206976 cell18215168)
                      (ThetaLowerSegment.join cell18223360 cell18231552))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18239744 cell18247936)
                      (ThetaLowerSegment.join cell18256128 cell18272512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18288896 cell18305280)
                      (ThetaLowerSegment.join cell18321664 cell18338048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18354432 cell18370816)
                      (ThetaLowerSegment.join cell18387200 cell18403584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell18419968 cell18436352)
                      (ThetaLowerSegment.join cell18452736 cell18469120)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18485504 cell18493696)
                    (ThetaLowerSegment.join cell18501888 cell18510080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18518272 cell18526464)
                    (ThetaLowerSegment.join cell18534656 cell18542848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18551040 cell18559232)
                    (ThetaLowerSegment.join cell18567424 cell18575616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18583808 cell18592000)
                    (ThetaLowerSegment.join cell18600192 cell18608384))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18616576 cell18632960)
                    (ThetaLowerSegment.join cell18649344 cell18665728))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18682112 cell18698496)
                    (ThetaLowerSegment.join cell18714880 cell18723072)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18731264 cell18747648)
                    (ThetaLowerSegment.join cell18764032 cell18780416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18796800 cell18813184)
                    (ThetaLowerSegment.join cell18829568 cell18845952)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18854144 cell18870528)
                    (ThetaLowerSegment.join cell18886912 cell18903296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18911488 cell18919680)
                    (ThetaLowerSegment.join cell18927872 cell18936064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell18952448 cell18968832)
                    (ThetaLowerSegment.join cell18985216 cell19001600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19017984 cell19034368)
                    (ThetaLowerSegment.join cell19050752 cell19067136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19075328 cell19091712)
                    (ThetaLowerSegment.join cell19108096 cell19116288))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19124480 cell19140864)
                    (ThetaLowerSegment.join cell19149056 cell19157248)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19173632 cell19190016)
                    (ThetaLowerSegment.join cell19198208 cell19206400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19222784 cell19230976)
                    (ThetaLowerSegment.join cell19239168 cell19247360))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19255552 cell19263744)
                    (ThetaLowerSegment.join cell19271936 cell19280128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19288320 cell19296512)
                    (ThetaLowerSegment.join cell19304704 cell19312896)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19321088 cell19329280)
                    (ThetaLowerSegment.join cell19337472 cell19345664))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19353856 cell19362048)
                    (ThetaLowerSegment.join cell19378432 cell19386624))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19403008 cell19419392)
                    (ThetaLowerSegment.join cell19435776 cell19452160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19468544 cell19484928)
                    (ThetaLowerSegment.join cell19501312 cell19517696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19534080 cell19550464)
                    (ThetaLowerSegment.join cell19558656 cell19566848))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19575040 cell19583232)
                    (ThetaLowerSegment.join cell19591424 cell19599616)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19607808 cell19616000)
                    (ThetaLowerSegment.join cell19624192 cell19632384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19640576 cell19648768)
                    (ThetaLowerSegment.join cell19656960 cell19665152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19673344 cell19681536)
                    (ThetaLowerSegment.join cell19689728 cell19697920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19706112 cell19714304)
                    (ThetaLowerSegment.join cell19722496 cell19730688))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19738880 cell19747072)
                    (ThetaLowerSegment.join cell19755264 cell19763456))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19771648 cell19779840)
                    (ThetaLowerSegment.join cell19788032 cell19796224)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19804416 cell19820800)
                    (ThetaLowerSegment.join cell19837184 cell19853568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19869952 cell19886336)
                    (ThetaLowerSegment.join cell19902720 cell19910912)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19927296 cell19943680)
                    (ThetaLowerSegment.join cell19960064 cell19976448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell19992832 cell20009216)
                    (ThetaLowerSegment.join cell20025600 cell20041984)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20058368 cell20074752)
                    (ThetaLowerSegment.join cell20091136 cell20107520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20123904 cell20140288)
                    (ThetaLowerSegment.join cell20156672 cell20173056))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20189440 cell20205824)
                    (ThetaLowerSegment.join cell20222208 cell20238592))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20254976 cell20271360)
                    (ThetaLowerSegment.join cell20287744 cell20304128)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20320512 cell20336896)
                    (ThetaLowerSegment.join cell20353280 cell20369664))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20386048 cell20402432)
                    (ThetaLowerSegment.join cell20418816 cell20427008)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20435200 cell20443392)
                    (ThetaLowerSegment.join cell20451584 cell20459776))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20467968 cell20476160)
                    (ThetaLowerSegment.join cell20484352 cell20492544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20500736 cell20508928)
                    (ThetaLowerSegment.join cell20517120 cell20525312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20541696 cell20549888)
                    (ThetaLowerSegment.join cell20558080 cell20566272))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20574464 cell20590848)
                    (ThetaLowerSegment.join cell20607232 cell20615424))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20623616 cell20631808)
                    (ThetaLowerSegment.join cell20648192 cell20656384)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20664576 cell20672768)
                    (ThetaLowerSegment.join cell20680960 cell20697344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20713728 cell20730112)
                    (ThetaLowerSegment.join cell20746496 cell20762880))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20779264 cell20795648)
                    (ThetaLowerSegment.join cell20812032 cell20828416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20844800 cell20861184)
                    (ThetaLowerSegment.join cell20877568 cell20893952)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20910336 cell20926720)
                    (ThetaLowerSegment.join cell20943104 cell20951296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell20967680 cell20984064)
                    (ThetaLowerSegment.join cell21000448 cell21016832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell21033216 cell21049600)
                    (ThetaLowerSegment.join cell21065984 cell21082368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell21098752 cell21115136)
                    (ThetaLowerSegment.join cell21131520 cell21147904)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell21164288 cell21172480)
                    (ThetaLowerSegment.join cell21188864 cell21197056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell21213440 cell21221632)
                    (ThetaLowerSegment.join cell21229824 cell21238016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell21246208 cell21254400)
                    (ThetaLowerSegment.join cell21262592 cell21270784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell21278976 cell21295360)
                    (ThetaLowerSegment.join cell21311744 cell21328128)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell21344512 cell21360896)
                    (ThetaLowerSegment.join cell21377280 cell21393664))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell21410048 cell21426432)
                    (ThetaLowerSegment.join cell21434624 cell21451008))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell21467392 cell21483776)
                  (ThetaLowerSegment.join cell21500160 cell21516544))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell21532928 cell21549312)
                  (ThetaLowerSegment.join cell21557504 cell21561600))))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
