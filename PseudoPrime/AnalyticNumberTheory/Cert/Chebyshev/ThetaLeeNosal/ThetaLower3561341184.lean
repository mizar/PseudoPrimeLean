/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3561341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3529341184 :
    ThetaLowerSegment 3529341184 3529472256 (88231801307081 / 25000) (22058757564989 / 6250) := by
  exact
    packedTile65536 3529341184 3529472256 14 5875 59408 32 _ _ (549609 / 25000) (2198439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529472256 :
    ThetaLowerSegment 3529472256 3529603328 (22058757564989 / 6250) (44119146097653 / 12500) := by
  exact
    packedTile65536 3529472256 3529603328 14 5935 59409 32 _ _ (54961 / 2500) (2198443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529603328 :
    ThetaLowerSegment 3529603328 3529734400 (44119146097653 / 12500) (88241568426477 / 25000) := by
  exact
    packedTile65536 3529603328 3529734400 14 5961 59410 32 _ _ (549611 / 25000) (2198447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529734400 :
    ThetaLowerSegment 3529734400 3529865472 (88241568426477 / 25000)
      (352979361060899 / 100000) := by
  exact
    packedTile65536 3529734400 3529865472 14 5953 59411 32 _ _ (2198447 / 100000) (43969 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529865472 :
    ThetaLowerSegment 3529865472 3529996544 (352979361060899 / 100000)
      (352992578148311 / 100000) := by
  exact
    packedTile65536 3529865472 3529996544 14 6012 59412 32 _ _ (2198451 / 100000) (1099227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529996544 :
    ThetaLowerSegment 3529996544 3530127616 (352992578148311 / 100000)
      (353005716115391 / 100000) := by
  exact
    packedTile65536 3529996544 3530127616 14 5976 59413 32 _ _ (439691 / 20000) (1099229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3530127616 :
    ThetaLowerSegment 3530127616 3530258688 (353005716115391 / 100000)
      (353018812329697 / 100000) := by
  exact
    packedTile65536 3530127616 3530258688 14 5957 59414 32 _ _ (1099229 / 50000) (2198461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3530258688 :
    ThetaLowerSegment 3530258688 3530389760 (353018812329697 / 100000)
      (353031860201667 / 100000) := by
  exact
    packedTile65536 3530258688 3530389760 14 5935 59415 32 _ _ (1099231 / 50000) (439693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3530389760 :
    ThetaLowerSegment 3530389760 3530520832 (353031860201667 / 100000)
      (353045040005337 / 100000) := by
  exact
    packedTile65536 3530389760 3530520832 14 5995 59417 32 _ _ (1099233 / 50000) (2198469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3530520832 :
    ThetaLowerSegment 3530520832 3530651904 (353045040005337 / 100000)
      (353058054947737 / 100000) := by
  exact
    packedTile65536 3530520832 3530651904 14 5920 59418 32 _ _ (219847 / 10000) (2198473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3530651904 :
    ThetaLowerSegment 3530651904 3530782976 (353058054947737 / 100000)
      (44133863677421 / 12500) := by
  exact
    packedTile65536 3530651904 3530782976 14 5847 59419 32 _ _ (2198473 / 100000) (549619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3530782976 :
    ThetaLowerSegment 3530782976 3530914048 (44133863677421 / 12500) (44135499344309 / 12500) := by
  exact
    packedTile65536 3530782976 3530914048 14 5952 59420 32 _ _ (2198477 / 100000) (27481 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3530914048 :
    ThetaLowerSegment 3530914048 3531045120 (44135499344309 / 12500) (44137126220249 / 12500) := by
  exact
    packedTile65536 3530914048 3531045120 14 5920 59421 32 _ _ (2198481 / 100000) (549621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531045120 :
    ThetaLowerSegment 3531045120 3531176192 (44137126220249 / 12500) (22069388915677 / 6250) := by
  exact
    packedTile65536 3531045120 3531176192 14 6010 59422 32 _ _ (549621 / 25000) (2198487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531176192 :
    ThetaLowerSegment 3531176192 3531307264 (22069388915677 / 6250) (8828084844811 / 2500) := by
  exact
    packedTile65536 3531176192 3531307264 14 5991 59423 32 _ _ (274811 / 12500) (2198491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531307264 :
    ThetaLowerSegment 3531307264 3531438336 (8828084844811 / 2500) (88284152231963 / 25000) := by
  exact
    packedTile65536 3531307264 3531438336 14 6011 59424 32 _ _ (549623 / 25000) (439699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531438336 :
    ThetaLowerSegment 3531438336 3531569408 (88284152231963 / 25000) (88287454922579 / 25000) := by
  exact
    packedTile65536 3531438336 3531569408 14 6009 59425 32 _ _ (68703 / 3125) (2198499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531569408 :
    ThetaLowerSegment 3531569408 3531700480 (88287454922579 / 25000) (88290735083087 / 25000) := by
  exact
    packedTile65536 3531569408 3531700480 14 5968 59427 32 _ _ (2198499 / 100000) (1099251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531700480 :
    ThetaLowerSegment 3531700480 3531831552 (88290735083087 / 25000) (35317603021921 / 10000) := by
  exact
    packedTile65536 3531700480 3531831552 14 5954 59428 32 _ _ (2198503 / 100000) (1099253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531831552 :
    ThetaLowerSegment 3531831552 3531962624 (35317603021921 / 10000) (11037162202566 / 3125) := by
  exact
    packedTile65536 3531831552 3531962624 14 5986 59429 32 _ _ (2198507 / 100000) (219851 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531962624 :
    ThetaLowerSegment 3531962624 3532093696 (11037162202566 / 3125) (88300537125013 / 25000) := by
  exact
    packedTile65536 3531962624 3532093696 14 5894 59430 32 _ _ (219851 / 10000) (2198513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3532093696 :
    ThetaLowerSegment 3532093696 3532224768 (88300537125013 / 25000) (176607719258591 / 50000) := by
  exact
    packedTile65536 3532093696 3532224768 14 6045 59431 32 _ _ (1099257 / 50000) (2198517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3532224768 :
    ThetaLowerSegment 3532224768 3532355840 (176607719258591 / 50000) (11038394881898 / 3125) := by
  exact
    packedTile65536 3532224768 3532355840 14 6003 59432 32 _ _ (1099259 / 50000) (2198521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3532355840 :
    ThetaLowerSegment 3532355840 3532486912 (11038394881898 / 3125) (176620879599277 / 50000) := by
  exact
    packedTile65536 3532355840 3532486912 14 5969 59433 32 _ _ (1099261 / 50000) (87941 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3532486912 :
    ThetaLowerSegment 3532486912 3532617984 (176620879599277 / 50000)
      (353254904179529 / 100000) := by
  exact
    packedTile65536 3532486912 3532617984 14 5979 59434 32 _ _ (87941 / 4000) (68704 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3532617984 :
    ThetaLowerSegment 3532617984 3532749056 (353254904179529 / 100000) (2207923933322 / 625) := by
  exact
    packedTile65536 3532617984 3532749056 14 5879 59435 32 _ _ (2198529 / 100000) (549633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3532749056 :
    ThetaLowerSegment 3532749056 3532880128 (2207923933322 / 625) (88320279316243 / 25000) := by
  exact
    packedTile65536 3532749056 3532880128 14 6044 59436 32 _ _ (2198533 / 100000) (274817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3532880128 :
    ThetaLowerSegment 3532880128 3533011200 (88320279316243 / 25000) (88323535897693 / 25000) := by
  exact
    packedTile65536 3532880128 3533011200 14 5925 59438 32 _ _ (274817 / 12500) (2198539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3533011200 :
    ThetaLowerSegment 3533011200 3533142272 (88323535897693 / 25000) (44163422075379 / 12500) := by
  exact
    packedTile65536 3533011200 3533142272 14 6019 59439 32 _ _ (109927 / 5000) (2198543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3533142272 :
    ThetaLowerSegment 3533142272 3533273344 (44163422075379 / 12500) (44165067135927 / 12500) := by
  exact
    packedTile65536 3533142272 3533273344 14 5986 59440 32 _ _ (137409 / 6250) (2198547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3533273344 :
    ThetaLowerSegment 3533273344 3533404416 (44165067135927 / 12500) (88333369984873 / 25000) := by
  exact
    packedTile65536 3533273344 3533404416 14 5887 59441 32 _ _ (549637 / 25000) (2198551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3533404416 :
    ThetaLowerSegment 3533404416 3533535488 (88333369984873 / 25000) (22084163105379 / 6250) := by
  exact
    packedTile65536 3533404416 3533535488 14 5972 59442 32 _ _ (2198551 / 100000) (1099277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3533535488 :
    ThetaLowerSegment 3533535488 3533666560 (22084163105379 / 6250) (353359680095539 / 100000) := by
  exact
    packedTile65536 3533535488 3533666560 14 5945 59443 32 _ _ (439711 / 20000) (1099279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3533666560 :
    ThetaLowerSegment 3533666560 3533797632 (353359680095539 / 100000)
      (70674571651637 / 20000) := by
  exact
    packedTile65536 3533666560 3533797632 14 5994 59444 32 _ _ (2198559 / 100000) (1099281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3533797632 :
    ThetaLowerSegment 3533797632 3533928704 (70674571651637 / 20000)
      (353386067218681 / 100000) := by
  exact
    packedTile65536 3533797632 3533928704 14 6008 59445 32 _ _ (1099281 / 50000) (439713 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3533928704 :
    ThetaLowerSegment 3533928704 3534059776 (353386067218681 / 100000)
      (353399159679211 / 100000) := by
  exact
    packedTile65536 3533928704 3534059776 14 5955 59446 32 _ _ (1099283 / 50000) (2198569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3534059776 :
    ThetaLowerSegment 3534059776 3534190848 (353399159679211 / 100000)
      (353412263156411 / 100000) := by
  exact
    packedTile65536 3534059776 3534190848 14 5960 59447 32 _ _ (219857 / 10000) (2198573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3534190848 :
    ThetaLowerSegment 3534190848 3534321920 (353412263156411 / 100000)
      (353425333678841 / 100000) := by
  exact
    packedTile65536 3534190848 3534321920 14 5945 59449 32 _ _ (1099287 / 50000) (2198577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3534321920 :
    ThetaLowerSegment 3534321920 3534452992 (353425333678841 / 100000)
      (353438467977839 / 100000) := by
  exact
    packedTile65536 3534321920 3534452992 14 5974 59450 32 _ _ (2198577 / 100000) (109929 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3534452992 :
    ThetaLowerSegment 3534452992 3534584064 (353438467977839 / 100000)
      (353451734215593 / 100000) := by
  exact
    packedTile65536 3534452992 3534584064 14 6034 59451 32 _ _ (2198581 / 100000) (274823 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3534584064 :
    ThetaLowerSegment 3534584064 3534715136 (353451734215593 / 100000)
      (353464714661433 / 100000) := by
  exact
    packedTile65536 3534584064 3534715136 14 5904 59452 32 _ _ (439717 / 20000) (549647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3534715136 :
    ThetaLowerSegment 3534715136 3534846208 (353464714661433 / 100000)
      (353477807252973 / 100000) := by
  exact
    packedTile65536 3534715136 3534846208 14 5955 59453 32 _ _ (549647 / 25000) (2198591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3534846208 :
    ThetaLowerSegment 3534846208 3534977280 (353477807252973 / 100000)
      (353490910861293 / 100000) := by
  exact
    packedTile65536 3534846208 3534977280 14 5960 59454 32 _ _ (68706 / 3125) (439719 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3534977280 :
    ThetaLowerSegment 3534977280 3535108352 (353490910861293 / 100000)
      (70700788387957 / 20000) := by
  exact
    packedTile65536 3534977280 3535108352 14 5927 59455 32 _ _ (549649 / 25000) (2198599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3535108352 :
    ThetaLowerSegment 3535108352 3535239424 (70700788387957 / 20000)
      (353517120342191 / 100000) := by
  exact
    packedTile65536 3535108352 3535239424 14 5994 59456 32 _ _ (2198599 / 100000) (1099301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3535239424 :
    ThetaLowerSegment 3535239424 3535370496 (353517120342191 / 100000)
      (88382511482307 / 25000) := by
  exact
    packedTile65536 3535239424 3535370496 14 5879 59457 32 _ _ (2198603 / 100000) (1099303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3535370496 :
    ThetaLowerSegment 3535370496 3535501568 (88382511482307 / 25000) (17677154843019 / 5000) := by
  exact
    packedTile65536 3535370496 3535501568 14 5936 59458 32 _ _ (2198607 / 100000) (219861 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3535501568 :
    ThetaLowerSegment 3535501568 3535632640 (17677154843019 / 5000) (7071128848583 / 2000) := by
  exact
    packedTile65536 3535501568 3535632640 14 6070 59460 32 _ _ (2198611 / 100000) (1099307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3535632640 :
    ThetaLowerSegment 3535632640 3535763712 (7071128848583 / 2000) (176784735707857 / 50000) := by
  exact
    packedTile65536 3535632640 3535763712 14 5926 59461 32 _ _ (1099307 / 50000) (2198617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3535763712 :
    ThetaLowerSegment 3535763712 3535894784 (176784735707857 / 50000) (22098910261619 / 6250) := by
  exact
    packedTile65536 3535763712 3535894784 14 5955 59462 32 _ _ (1099309 / 50000) (2198621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3535894784 :
    ThetaLowerSegment 3535894784 3536025856 (22098910261619 / 6250) (7071917009173 / 2000) := by
  exact
    packedTile65536 3535894784 3536025856 14 6043 59463 32 _ _ (1099311 / 50000) (17589 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536025856 :
    ThetaLowerSegment 3536025856 3536156928 (7071917009173 / 2000) (14144362655741 / 4000) := by
  exact
    packedTile65536 3536025856 3536156928 14 6011 59464 32 _ _ (17589 / 800) (549657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536156928 :
    ThetaLowerSegment 3536156928 3536288000 (14144362655741 / 4000) (353622288948331 / 100000) := by
  exact
    packedTile65536 3536156928 3536288000 14 6014 59465 32 _ _ (2198629 / 100000) (274829 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536288000 :
    ThetaLowerSegment 3536288000 3536419072 (353622288948331 / 100000)
      (353635357622883 / 100000) := by
  exact
    packedTile65536 3536288000 3536419072 14 5944 59466 32 _ _ (2198633 / 100000) (549659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536419072 :
    ThetaLowerSegment 3536419072 3536550144 (353635357622883 / 100000)
      (88412153301339 / 25000) := by
  exact
    packedTile65536 3536419072 3536550144 14 6029 59467 32 _ _ (2198637 / 100000) (27483 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536550144 :
    ThetaLowerSegment 3536550144 3536681216 (88412153301339 / 25000) (88415358918459 / 25000) := by
  exact
    packedTile65536 3536550144 3536681216 14 5832 59468 32 _ _ (27483 / 1250) (2198643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536681216 :
    ThetaLowerSegment 3536681216 3536812288 (88415358918459 / 25000) (11052331629604 / 3125) := by
  exact
    packedTile65536 3536681216 3536812288 14 5993 59470 32 _ _ (549661 / 25000) (2198647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536812288 :
    ThetaLowerSegment 3536812288 3536943360 (11052331629604 / 3125) (8842196145241 / 2500) := by
  exact
    packedTile65536 3536812288 3536943360 14 6019 59471 32 _ _ (274831 / 12500) (2198651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536943360 :
    ThetaLowerSegment 3536943360 3537074432 (8842196145241 / 2500) (353700929981741 / 100000) := by
  exact
    packedTile65536 3536943360 3537074432 14 5951 59472 32 _ _ (2198651 / 100000) (1099327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3537074432 :
    ThetaLowerSegment 3537074432 3537205504 (353700929981741 / 100000)
      (176857037869993 / 50000) := by
  exact
    packedTile65536 3537074432 3537205504 14 5979 59473 32 _ _ (439731 / 20000) (1099329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3537205504 :
    ThetaLowerSegment 3537205504 3537336576 (176857037869993 / 50000) (88431771850987 / 25000) := by
  exact
    packedTile65536 3537205504 3537336576 14 5918 59474 32 _ _ (2198659 / 100000) (1099331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3537336576 :
    ThetaLowerSegment 3537336576 3537467648 (88431771850987 / 25000) (11054382493751 / 3125) := by
  exact
    packedTile65536 3537336576 3537467648 14 5982 59475 32 _ _ (1099331 / 50000) (439733 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3537467648 :
    ThetaLowerSegment 3537467648 3537598720 (11054382493751 / 3125) (17687669171269 / 5000) := by
  exact
    packedTile65536 3537467648 3537598720 14 5978 59476 32 _ _ (1099333 / 50000) (2198669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3537598720 :
    ThetaLowerSegment 3537598720 3537729792 (17687669171269 / 5000) (17688334049077 / 5000) := by
  exact
    packedTile65536 3537598720 3537729792 14 6048 59477 32 _ _ (219867 / 10000) (2198673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3537729792 :
    ThetaLowerSegment 3537729792 3537860864 (17688334049077 / 5000) (88444955064341 / 25000) := by
  exact
    packedTile65536 3537729792 3537860864 14 5976 59478 32 _ _ (1099337 / 50000) (2198677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3537860864 :
    ThetaLowerSegment 3537860864 3537991936 (88444955064341 / 25000) (176896490768943 / 50000) := by
  exact
    packedTile65536 3537860864 3537991936 14 5986 59479 32 _ _ (2198677 / 100000) (54967 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3537991936 :
    ThetaLowerSegment 3537991936 3538123008 (176896490768943 / 50000) (88451471948839 / 25000) := by
  exact
    packedTile65536 3537991936 3538123008 14 5870 59481 32 _ _ (2198681 / 100000) (549671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3538123008 :
    ThetaLowerSegment 3538123008 3538254080 (88451471948839 / 25000) (176909546548733 / 50000) := by
  exact
    packedTile65536 3538123008 3538254080 14 6006 59482 32 _ _ (439737 / 20000) (68709 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3538254080 :
    ThetaLowerSegment 3538254080 3538385152 (176909546548733 / 50000)
      (176916172295021 / 50000) := by
  exact
    packedTile65536 3538254080 3538385152 14 6027 59483 32 _ _ (68709 / 3125) (2198691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3538385152 :
    ThetaLowerSegment 3538385152 3538516224 (176916172295021 / 50000)
      (176922633151463 / 50000) := by
  exact
    packedTile65536 3538385152 3538516224 14 5877 59484 32 _ _ (549673 / 25000) (439739 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3538516224 :
    ThetaLowerSegment 3538516224 3538647296 (176922633151463 / 50000)
      (176929220444679 / 50000) := by
  exact
    packedTile65536 3538516224 3538647296 14 5992 59485 32 _ _ (274837 / 12500) (2198699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3538647296 :
    ThetaLowerSegment 3538647296 3538778368 (176929220444679 / 50000)
      (176935743987579 / 50000) := by
  exact
    packedTile65536 3538647296 3538778368 14 5934 59486 32 _ _ (21987 / 1000) (2198703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3538778368 :
    ThetaLowerSegment 3538778368 3538909440 (176935743987579 / 50000)
      (353884651610019 / 100000) := by
  exact
    packedTile65536 3538778368 3538909440 14 5987 59487 32 _ _ (2198703 / 100000) (1099353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3538909440 :
    ThetaLowerSegment 3538909440 3539040512 (353884651610019 / 100000)
      (353897650365803 / 100000) := by
  exact
    packedTile65536 3538909440 3539040512 14 5912 59488 32 _ _ (2198707 / 100000) (219871 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3539040512 :
    ThetaLowerSegment 3539040512 3539171584 (353897650365803 / 100000)
      (353910754683363 / 100000) := by
  exact
    packedTile65536 3539040512 3539171584 14 5960 59489 32 _ _ (2198711 / 100000) (1099357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3539171584 :
    ThetaLowerSegment 3539171584 3539302656 (353910754683363 / 100000)
      (353923702910109 / 100000) := by
  exact
    packedTile65536 3539171584 3539302656 14 5889 59490 32 _ _ (1099357 / 50000) (2198717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3539302656 :
    ThetaLowerSegment 3539302656 3539433728 (353923702910109 / 100000)
      (353936725916823 / 100000) := by
  exact
    packedTile65536 3539302656 3539433728 14 5923 59492 32 _ _ (1099359 / 50000) (2198721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3539433728 :
    ThetaLowerSegment 3539433728 3539564800 (353936725916823 / 100000)
      (353949660998349 / 100000) := by
  exact
    packedTile65536 3539433728 3539564800 14 5883 59493 32 _ _ (1099361 / 50000) (87949 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3539564800 :
    ThetaLowerSegment 3539564800 3539695872 (353949660998349 / 100000)
      (88490714986131 / 25000) := by
  exact
    packedTile65536 3539564800 3539695872 14 6003 59494 32 _ _ (87949 / 4000) (274841 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3539695872 :
    ThetaLowerSegment 3539695872 3539826944 (88490714986131 / 25000) (176987993178327 / 50000) := by
  exact
    packedTile65536 3539695872 3539826944 14 5970 59495 32 _ _ (2198729 / 100000) (549683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3539826944 :
    ThetaLowerSegment 3539826944 3539958016 (176987993178327 / 50000) (44248630304151 / 12500) := by
  exact
    packedTile65536 3539826944 3539958016 14 5938 59496 32 _ _ (2198733 / 100000) (137421 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3539958016 :
    ThetaLowerSegment 3539958016 3540089088 (44248630304151 / 12500)
      (354002052360037 / 100000) := by
  exact
    packedTile65536 3539958016 3540089088 14 5917 59497 32 _ _ (2198737 / 100000) (109937 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3540089088 :
    ThetaLowerSegment 3540089088 3540220160 (354002052360037 / 100000)
      (354015392115617 / 100000) := by
  exact
    packedTile65536 3540089088 3540220160 14 6067 59498 32 _ _ (109937 / 5000) (2198743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3540220160 :
    ThetaLowerSegment 3540220160 3540351232 (354015392115617 / 100000)
      (354028428468793 / 100000) := by
  exact
    packedTile65536 3540220160 3540351232 14 5929 59499 32 _ _ (274843 / 12500) (2198747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3540351232 :
    ThetaLowerSegment 3540351232 3540482304 (354028428468793 / 100000)
      (70808332546601 / 20000) := by
  exact
    packedTile65536 3540351232 3540482304 14 6019 59500 32 _ _ (549687 / 25000) (2198751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3540482304 :
    ThetaLowerSegment 3540482304 3540613376 (70808332546601 / 20000)
      (354054754096459 / 100000) := by
  exact
    packedTile65536 3540482304 3540613376 14 5954 59501 32 _ _ (2198751 / 100000) (1099377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3540613376 :
    ThetaLowerSegment 3540613376 3540744448 (354054754096459 / 100000)
      (177033978810117 / 50000) := by
  exact
    packedTile65536 3540613376 3540744448 14 6005 59503 32 _ _ (439751 / 20000) (1099379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3540744448 :
    ThetaLowerSegment 3540744448 3540875520 (177033978810117 / 50000)
      (354081002857381 / 100000) := by
  exact
    packedTile65536 3540744448 3540875520 14 5933 59504 32 _ _ (2198759 / 100000) (1099381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3540875520 :
    ThetaLowerSegment 3540875520 3541006592 (354081002857381 / 100000)
      (354094136062807 / 100000) := by
  exact
    packedTile65536 3540875520 3541006592 14 5973 59505 32 _ _ (1099381 / 50000) (439753 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3541006592 :
    ThetaLowerSegment 3541006592 3541137664 (354094136062807 / 100000)
      (354107040620461 / 100000) := by
  exact
    packedTile65536 3541006592 3541137664 14 5869 59506 32 _ _ (1099383 / 50000) (2198769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3541137664 :
    ThetaLowerSegment 3541137664 3541268736 (354107040620461 / 100000)
      (354120231041691 / 100000) := by
  exact
    packedTile65536 3541137664 3541268736 14 5999 59507 32 _ _ (219877 / 10000) (2198773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3541268736 :
    ThetaLowerSegment 3541268736 3541399808 (354120231041691 / 100000)
      (70826693971989 / 20000) := by
  exact
    packedTile65536 3541268736 3541399808 14 6021 59508 32 _ _ (1099387 / 50000) (2198777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3541399808 :
    ThetaLowerSegment 3541399808 3541530880 (70826693971989 / 20000)
      (354146521800217 / 100000) := by
  exact
    packedTile65536 3541399808 3541530880 14 5936 59509 32 _ _ (2198777 / 100000) (109939 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3541530880 :
    ThetaLowerSegment 3541530880 3541661952 (354146521800217 / 100000) (11067489085049 / 3125) := by
  exact
    packedTile65536 3541530880 3541661952 14 5971 59510 32 _ _ (2198781 / 100000) (68712 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3541661952 :
    ThetaLowerSegment 3541661952 3541793024 (11067489085049 / 3125) (354172709305683 / 100000) := by
  exact
    packedTile65536 3541661952 3541793024 14 5939 59511 32 _ _ (439757 / 20000) (549697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3541793024 :
    ThetaLowerSegment 3541793024 3541924096 (354172709305683 / 100000)
      (354185763510039 / 100000) := by
  exact
    packedTile65536 3541793024 3541924096 14 5937 59512 32 _ _ (549697 / 25000) (2198791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3541924096 :
    ThetaLowerSegment 3541924096 3542055168 (354185763510039 / 100000)
      (70839803565643 / 20000) := by
  exact
    packedTile65536 3541924096 3542055168 14 6028 59514 32 _ _ (274849 / 12500) (439759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3542055168 :
    ThetaLowerSegment 3542055168 3542186240 (70839803565643 / 20000)
      (354212047893311 / 100000) := by
  exact
    packedTile65536 3542055168 3542186240 14 5926 59515 32 _ _ (549699 / 25000) (2198799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3542186240 :
    ThetaLowerSegment 3542186240 3542317312 (354212047893311 / 100000)
      (354225003217019 / 100000) := by
  exact
    packedTile65536 3542186240 3542317312 14 5892 59516 32 _ _ (2198799 / 100000) (1099401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3542317312 :
    ThetaLowerSegment 3542317312 3542448384 (354225003217019 / 100000)
      (354237940973871 / 100000) := by
  exact
    packedTile65536 3542317312 3542448384 14 5884 59517 32 _ _ (2198803 / 100000) (1099403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3542448384 :
    ThetaLowerSegment 3542448384 3542579456 (354237940973871 / 100000)
      (177125502043129 / 50000) := by
  exact
    packedTile65536 3542448384 3542579456 14 5941 59518 32 _ _ (2198807 / 100000) (219881 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3542579456 :
    ThetaLowerSegment 3542579456 3542710528 (177125502043129 / 50000) (88566070126769 / 25000) := by
  exact
    packedTile65536 3542579456 3542710528 14 6038 59519 32 _ _ (2198811 / 100000) (1099407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3542710528 :
    ThetaLowerSegment 3542710528 3542841600 (88566070126769 / 25000) (35427732167291 / 10000) := by
  exact
    packedTile65536 3542710528 3542841600 14 5931 59520 32 _ _ (1099407 / 50000) (2198817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3542841600 :
    ThetaLowerSegment 3542841600 3542972672 (35427732167291 / 10000) (17714525179341 / 5000) := by
  exact
    packedTile65536 3542841600 3542972672 14 5995 59521 32 _ _ (1099409 / 50000) (2198821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3542972672 :
    ThetaLowerSegment 3542972672 3543103744 (17714525179341 / 5000) (88575899942663 / 25000) := by
  exact
    packedTile65536 3542972672 3543103744 14 5956 59522 32 _ _ (1099411 / 50000) (87953 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3543103744 :
    ThetaLowerSegment 3543103744 3543234816 (88575899942663 / 25000)
      (354316601422877 / 100000) := by
  exact
    packedTile65536 3543103744 3543234816 14 5913 59523 32 _ _ (87953 / 4000) (549707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3543234816 :
    ThetaLowerSegment 3543234816 3543365888 (354316601422877 / 100000)
      (88582428260051 / 25000) := by
  exact
    packedTile65536 3543234816 3543365888 14 5963 59525 32 _ _ (2198829 / 100000) (137427 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3543365888 :
    ThetaLowerSegment 3543365888 3543496960 (88582428260051 / 25000) (177171402445943 / 50000) := by
  exact
    packedTile65536 3543365888 3543496960 14 5954 59526 32 _ _ (2198833 / 100000) (549709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3543496960 :
    ThetaLowerSegment 3543496960 3543628032 (177171402445943 / 50000) (35435596272651 / 10000) := by
  exact
    packedTile65536 3543496960 3543628032 14 5984 59527 32 _ _ (549709 / 25000) (2198839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3543628032 :
    ThetaLowerSegment 3543628032 3543759104 (35435596272651 / 10000) (35436896886511 / 10000) := by
  exact
    packedTile65536 3543628032 3543759104 14 5915 59528 32 _ _ (54971 / 2500) (2198843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3543759104 :
    ThetaLowerSegment 3543759104 3543890176 (35436896886511 / 10000) (35438205198691 / 10000) := by
  exact
    packedTile65536 3543759104 3543890176 14 5950 59529 32 _ _ (549711 / 25000) (2198847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3543890176 :
    ThetaLowerSegment 3543890176 3544021248 (35438205198691 / 10000) (35439501419587 / 10000) := by
  exact
    packedTile65536 3543890176 3544021248 14 5895 59530 32 _ _ (68714 / 3125) (2198851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3544021248 :
    ThetaLowerSegment 3544021248 3544152320 (35439501419587 / 10000)
      (354408068774257 / 100000) := by
  exact
    packedTile65536 3544021248 3544152320 14 5937 59531 32 _ _ (2198851 / 100000) (1099427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3544152320 :
    ThetaLowerSegment 3544152320 3544283392 (354408068774257 / 100000)
      (354421138768377 / 100000) := by
  exact
    packedTile65536 3544152320 3544283392 14 5944 59532 32 _ _ (439771 / 20000) (1099429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3544283392 :
    ThetaLowerSegment 3544283392 3544414464 (354421138768377 / 100000)
      (44304277472571 / 12500) := by
  exact
    packedTile65536 3544283392 3544414464 14 5949 59533 32 _ _ (2198859 / 100000) (1099431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3544414464 :
    ThetaLowerSegment 3544414464 3544545536 (44304277472571 / 12500) (177223703177991 / 50000) := by
  exact
    packedTile65536 3544414464 3544545536 14 5997 59534 32 _ _ (1099431 / 50000) (439773 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3544545536 :
    ThetaLowerSegment 3544545536 3544676608 (177223703177991 / 50000) (44307591710351 / 12500) := by
  exact
    packedTile65536 3544545536 3544676608 14 6061 59536 32 _ _ (1099433 / 50000) (2198869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3544676608 :
    ThetaLowerSegment 3544676608 3544807680 (44307591710351 / 12500) (177236938164399 / 50000) := by
  exact
    packedTile65536 3544676608 3544807680 14 5977 59537 32 _ _ (219887 / 10000) (2198873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3544807680 :
    ThetaLowerSegment 3544807680 3544938752 (177236938164399 / 50000)
      (354486829889641 / 100000) := by
  exact
    packedTile65536 3544807680 3544938752 14 5891 59538 32 _ _ (2198873 / 100000) (549719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3544938752 :
    ThetaLowerSegment 3544938752 3545069824 (354486829889641 / 100000)
      (177250025868521 / 50000) := by
  exact
    packedTile65536 3544938752 3545069824 14 6013 59539 32 _ _ (2198877 / 100000) (13743 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3545069824 :
    ThetaLowerSegment 3545069824 3545200896 (177250025868521 / 50000) (70902606346317 / 20000) := by
  exact
    packedTile65536 3545069824 3545200896 14 5903 59540 32 _ _ (2198881 / 100000) (549721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3545200896 :
    ThetaLowerSegment 3545200896 3545331968 (70902606346317 / 20000) (35452635037803 / 10000) := by
  exact
    packedTile65536 3545200896 3545331968 14 6057 59541 32 _ _ (439777 / 20000) (274861 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3545331968 :
    ThetaLowerSegment 3545331968 3545463040 (35452635037803 / 10000) (177269761958019 / 50000) := by
  exact
    packedTile65536 3545331968 3545463040 14 5991 59542 32 _ _ (274861 / 12500) (2198891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3545463040 :
    ThetaLowerSegment 3545463040 3545594112 (177269761958019 / 50000)
      (177276279473907 / 50000) := by
  exact
    packedTile65536 3545463040 3545594112 14 5928 59543 32 _ _ (549723 / 25000) (439779 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3545594112 :
    ThetaLowerSegment 3545594112 3545725184 (177276279473907 / 50000)
      (177282829985091 / 50000) := by
  exact
    packedTile65536 3545594112 3545725184 14 5958 59544 32 _ _ (137431 / 6250) (2198899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3545725184 :
    ThetaLowerSegment 3545725184 3545856256 (177282829985091 / 50000)
      (354578842369687 / 100000) := by
  exact
    packedTile65536 3545725184 3545856256 14 5995 59545 32 _ _ (2198899 / 100000) (1099451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3545856256 :
    ThetaLowerSegment 3545856256 3545987328 (354578842369687 / 100000)
      (177295891456921 / 50000) := by
  exact
    packedTile65536 3545856256 3545987328 14 5885 59547 32 _ _ (2198903 / 100000) (1099453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3545987328 :
    ThetaLowerSegment 3545987328 3546118400 (177295891456921 / 50000) (443256203953 / 125) := by
  exact
    packedTile65536 3545987328 3546118400 14 5994 59548 32 _ _ (2198907 / 100000) (219891 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3546118400 :
    ThetaLowerSegment 3546118400 3546249472 (443256203953 / 125) (4432722779851 / 1250) := by
  exact
    packedTile65536 3546118400 3546249472 14 5848 59549 32 _ _ (219891 / 10000) (2198913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3546249472 :
    ThetaLowerSegment 3546249472 3546380544 (4432722779851 / 1250) (177315449664819 / 50000) := by
  exact
    packedTile65536 3546249472 3546380544 14 5947 59550 32 _ _ (1099457 / 50000) (2198917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3546380544 :
    ThetaLowerSegment 3546380544 3546511616 (177315449664819 / 50000)
      (177322101391769 / 50000) := by
  exact
    packedTile65536 3546380544 3546511616 14 6050 59551 32 _ _ (1099459 / 50000) (2198921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3546511616 :
    ThetaLowerSegment 3546511616 3546642688 (177322101391769 / 50000) (35465721160609 / 10000) := by
  exact
    packedTile65536 3546511616 3546642688 14 5916 59552 32 _ _ (1099461 / 50000) (87957 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3546642688 :
    ThetaLowerSegment 3546642688 3546773760 (35465721160609 / 10000) (17733516079847 / 5000) := by
  exact
    packedTile65536 3546642688 3546773760 14 5962 59553 32 _ _ (87957 / 4000) (137433 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3546773760 :
    ThetaLowerSegment 3546773760 3546904832 (17733516079847 / 5000) (22167713651129 / 6250) := by
  exact
    packedTile65536 3546773760 3546904832 14 5956 59554 32 _ _ (2198929 / 100000) (549733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3546904832 :
    ThetaLowerSegment 3546904832 3547035904 (22167713651129 / 6250) (354696438300357 / 100000) := by
  exact
    packedTile65536 3546904832 3547035904 14 5921 59555 32 _ _ (2198933 / 100000) (274867 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3547035904 :
    ThetaLowerSegment 3547035904 3547166976 (354696438300357 / 100000)
      (354709565948277 / 100000) := by
  exact
    packedTile65536 3547035904 3547166976 14 5970 59556 32 _ _ (274867 / 12500) (2198939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3547166976 :
    ThetaLowerSegment 3547166976 3547298048 (354709565948277 / 100000)
      (354722651840217 / 100000) := by
  exact
    packedTile65536 3547166976 3547298048 14 5951 59558 32 _ _ (109947 / 5000) (2198943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3547298048 :
    ThetaLowerSegment 3547298048 3547429120 (354722651840217 / 100000)
      (354735647599257 / 100000) := by
  exact
    packedTile65536 3547298048 3547429120 14 5910 59559 32 _ _ (68717 / 3125) (2198947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3547429120 :
    ThetaLowerSegment 3547429120 3547560192 (354735647599257 / 100000)
      (35474892704019 / 10000) := by
  exact
    packedTile65536 3547429120 3547560192 14 6039 59560 32 _ _ (2198947 / 100000) (43979 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3547560192 :
    ThetaLowerSegment 3547560192 3547691264 (35474892704019 / 10000) (11086311737982 / 3125) := by
  exact
    packedTile65536 3547560192 3547691264 14 5934 59561 32 _ _ (2198951 / 100000) (1099477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3547691264 :
    ThetaLowerSegment 3547691264 3547822336 (11086311737982 / 3125) (354775123167369 / 100000) := by
  exact
    packedTile65536 3547691264 3547822336 14 5979 59562 32 _ _ (439791 / 20000) (1099479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3547822336 :
    ThetaLowerSegment 3547822336 3547953408 (354775123167369 / 100000)
      (354788281732041 / 100000) := by
  exact
    packedTile65536 3547822336 3547953408 14 5984 59563 32 _ _ (1099479 / 50000) (2198961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3547953408 :
    ThetaLowerSegment 3547953408 3548084480 (354788281732041 / 100000) (14192059635871 / 4000) := by
  exact
    packedTile65536 3547953408 3548084480 14 6007 59564 32 _ _ (1099481 / 50000) (439793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3548084480 :
    ThetaLowerSegment 3548084480 3548215552 (14192059635871 / 4000) (70962932540623 / 20000) := by
  exact
    packedTile65536 3548084480 3548215552 14 5990 59565 32 _ _ (1099483 / 50000) (2198969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3548215552 :
    ThetaLowerSegment 3548215552 3548346624 (70962932540623 / 20000) (70965536121103 / 20000) := by
  exact
    packedTile65536 3548215552 3548346624 14 5920 59566 32 _ _ (219897 / 10000) (2198973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3548346624 :
    ThetaLowerSegment 3548346624 3548477696 (70965536121103 / 20000) (177420458112001 / 50000) := by
  exact
    packedTile65536 3548346624 3548477696 14 6019 59568 32 _ _ (2198973 / 100000) (68718 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3548477696 :
    ThetaLowerSegment 3548477696 3548608768 (177420458112001 / 50000)
      (177427033053231 / 50000) := by
  exact
    packedTile65536 3548477696 3548608768 14 5980 59569 32 _ _ (2198977 / 100000) (109949 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3548608768 :
    ThetaLowerSegment 3548608768 3548739840 (177427033053231 / 50000) (44358403650841 / 12500) := by
  exact
    packedTile65536 3548608768 3548739840 14 5986 59570 32 _ _ (2198981 / 100000) (274873 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3548739840 :
    ThetaLowerSegment 3548739840 3548870912 (44358403650841 / 12500) (11090010954508 / 3125) := by
  exact
    packedTile65536 3548739840 3548870912 14 5967 59571 32 _ _ (274873 / 12500) (2198987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3548870912 :
    ThetaLowerSegment 3548870912 3549001984 (11090010954508 / 3125) (17744683050931 / 5000) := by
  exact
    packedTile65536 3548870912 3549001984 14 6053 59572 32 _ _ (549747 / 25000) (2198991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3549001984 :
    ThetaLowerSegment 3549001984 3549133056 (17744683050931 / 5000) (88726664815083 / 25000) := by
  exact
    packedTile65536 3549001984 3549133056 14 5911 59573 32 _ _ (137437 / 6250) (439799 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3549133056 :
    ThetaLowerSegment 3549133056 3549264128 (88726664815083 / 25000)
      (354919732285607 / 100000) := by
  exact
    packedTile65536 3549133056 3549264128 14 5945 59574 32 _ _ (439799 / 20000) (1099499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3549264128 :
    ThetaLowerSegment 3549264128 3549395200 (354919732285607 / 100000)
      (177466358687351 / 50000) := by
  exact
    packedTile65536 3549264128 3549395200 14 5905 59575 32 _ _ (2198999 / 100000) (1099501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3549395200 :
    ThetaLowerSegment 3549395200 3549526272 (177466358687351 / 50000)
      (354945997153819 / 100000) := by
  exact
    packedTile65536 3549395200 3549526272 14 6039 59576 32 _ _ (2199003 / 100000) (1099503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3549526272 :
    ThetaLowerSegment 3549526272 3549657344 (354945997153819 / 100000)
      (354959228572921 / 100000) := by
  exact
    packedTile65536 3549526272 3549657344 14 6017 59577 32 _ _ (1099503 / 50000) (2199009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3549657344 :
    ThetaLowerSegment 3549657344 3549788416 (354959228572921 / 100000)
      (354972303886381 / 100000) := by
  exact
    packedTile65536 3549657344 3549788416 14 5946 59579 32 _ _ (219901 / 10000) (2199013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3549788416 :
    ThetaLowerSegment 3549788416 3549919488 (354972303886381 / 100000)
      (354985209899547 / 100000) := by
  exact
    packedTile65536 3549788416 3549919488 14 5869 59580 32 _ _ (1099507 / 50000) (2199017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3549919488 :
    ThetaLowerSegment 3549919488 3550050560 (354985209899547 / 100000)
      (70999659251133 / 20000) := by
  exact
    packedTile65536 3549919488 3550050560 14 5951 59581 32 _ _ (1099509 / 50000) (2199021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3550050560 :
    ThetaLowerSegment 3550050560 3550181632 (70999659251133 / 20000)
      (355011516769917 / 100000) := by
  exact
    packedTile65536 3550050560 3550181632 14 6012 59582 32 _ _ (2199021 / 100000) (137439 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3550181632 :
    ThetaLowerSegment 3550181632 3550312704 (355011516769917 / 100000)
      (177512290588721 / 50000) := by
  exact
    packedTile65536 3550181632 3550312704 14 5941 59583 32 _ _ (87961 / 4000) (549757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3550312704 :
    ThetaLowerSegment 3550312704 3550443776 (177512290588721 / 50000)
      (177518852491257 / 50000) := by
  exact
    packedTile65536 3550312704 3550443776 14 5968 59584 32 _ _ (2199029 / 100000) (274879 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3550443776 :
    ThetaLowerSegment 3550443776 3550574848 (177518852491257 / 50000) (35505102671837 / 10000) := by
  exact
    packedTile65536 3550443776 3550574848 14 6058 59585 32 _ _ (274879 / 12500) (439807 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3550574848 :
    ThetaLowerSegment 3550574848 3550705920 (35505102671837 / 10000) (177532041197551 / 50000) := by
  exact
    packedTile65536 3550574848 3550705920 14 5937 59586 32 _ _ (549759 / 25000) (2199039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3550705920 :
    ThetaLowerSegment 3550705920 3550836992 (177532041197551 / 50000)
      (177538617426671 / 50000) := by
  exact
    packedTile65536 3550705920 3550836992 14 5981 59587 32 _ _ (13744 / 625) (2199043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3550836992 :
    ThetaLowerSegment 3550836992 3550968064 (177538617426671 / 50000) (35509037633431 / 10000) := by
  exact
    packedTile65536 3550836992 3550968064 14 5976 59588 32 _ _ (2199043 / 100000) (1099523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3550968064 :
    ThetaLowerSegment 3550968064 3551099136 (35509037633431 / 10000) (177551767715779 / 50000) := by
  exact
    packedTile65536 3550968064 3551099136 14 5984 59589 32 _ _ (2199047 / 100000) (43981 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3551099136 :
    ThetaLowerSegment 3551099136 3551230208 (177551767715779 / 50000)
      (355116749529017 / 100000) := by
  exact
    packedTile65536 3551099136 3551230208 14 6009 59591 32 _ _ (2199051 / 100000) (1099527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3551230208 :
    ThetaLowerSegment 3551230208 3551361280 (355116749529017 / 100000)
      (355129820705993 / 100000) := by
  exact
    packedTile65536 3551230208 3551361280 14 5944 59592 32 _ _ (1099527 / 50000) (2199057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3551361280 :
    ThetaLowerSegment 3551361280 3551492352 (355129820705993 / 100000)
      (355143043641747 / 100000) := by
  exact
    packedTile65536 3551361280 3551492352 14 6013 59593 32 _ _ (1099529 / 50000) (2199061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3551492352 :
    ThetaLowerSegment 3551492352 3551623424 (355143043641747 / 100000)
      (355156066486911 / 100000) := by
  exact
    packedTile65536 3551492352 3551623424 14 5922 59594 32 _ _ (1099531 / 50000) (439813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3551623424 :
    ThetaLowerSegment 3551623424 3551754496 (355156066486911 / 100000)
      (355169010189387 / 100000) := by
  exact
    packedTile65536 3551623424 3551754496 14 5886 59595 32 _ _ (1099533 / 50000) (2199069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3551754496 :
    ThetaLowerSegment 3551754496 3551885568 (355169010189387 / 100000)
      (35518213203411 / 10000) := by
  exact
    packedTile65536 3551754496 3551885568 14 5967 59596 32 _ _ (2199069 / 100000) (68721 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3551885568 :
    ThetaLowerSegment 3551885568 3552016640 (35518213203411 / 10000) (88798777740739 / 25000) := by
  exact
    packedTile65536 3551885568 3552016640 14 5902 59597 32 _ _ (2199073 / 100000) (549769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552016640 :
    ThetaLowerSegment 3552016640 3552147712 (88798777740739 / 25000) (177604031763243 / 50000) := by
  exact
    packedTile65536 3552016640 3552147712 14 5890 59598 32 _ _ (2199077 / 100000) (54977 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552147712 :
    ThetaLowerSegment 3552147712 3552278784 (177604031763243 / 50000)
      (177610517949703 / 50000) := by
  exact
    packedTile65536 3552147712 3552278784 14 5899 59599 32 _ _ (54977 / 2500) (2199083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552278784 :
    ThetaLowerSegment 3552278784 3552409856 (177610517949703 / 50000)
      (177617125097581 / 50000) := by
  exact
    packedTile65536 3552278784 3552409856 14 6009 59600 32 _ _ (549771 / 25000) (2199087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552409856 :
    ThetaLowerSegment 3552409856 3552540928 (177617125097581 / 50000)
      (177623691574349 / 50000) := by
  exact
    packedTile65536 3552409856 3552540928 14 5972 59602 32 _ _ (137443 / 6250) (2199091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552540928 :
    ThetaLowerSegment 3552540928 3552672000 (177623691574349 / 50000)
      (355260601884699 / 100000) := by
  exact
    packedTile65536 3552540928 3552672000 14 6011 59603 32 _ _ (2199091 / 100000) (1099547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552672000 :
    ThetaLowerSegment 3552672000 3552803072 (355260601884699 / 100000)
      (177636908123277 / 50000) := by
  exact
    packedTile65536 3552672000 3552803072 14 6009 59604 32 _ _ (439819 / 20000) (1099549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552803072 :
    ThetaLowerSegment 3552803072 3552934144 (177636908123277 / 50000) (71057379737301 / 20000) := by
  exact
    packedTile65536 3552803072 3552934144 14 5949 59605 32 _ _ (2199099 / 100000) (1099551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552934144 :
    ThetaLowerSegment 3552934144 3553065216 (71057379737301 / 20000)
      (355299879985611 / 100000) := by
  exact
    packedTile65536 3552934144 3553065216 14 5903 59606 32 _ _ (1099551 / 50000) (439821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3553065216 :
    ThetaLowerSegment 3553065216 3553196288 (355299879985611 / 100000)
      (71062583697017 / 20000) := by
  exact
    packedTile65536 3553065216 3553196288 14 5929 59607 32 _ _ (1099553 / 50000) (2199109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3553196288 :
    ThetaLowerSegment 3553196288 3553327360 (71062583697017 / 20000) (14213038720153 / 4000) := by
  exact
    packedTile65536 3553196288 3553327360 14 5934 59608 32 _ _ (219911 / 10000) (2199113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3553327360 :
    ThetaLowerSegment 3553327360 3553458432 (14213038720153 / 4000) (355339125302887 / 100000) := by
  exact
    packedTile65536 3553327360 3553458432 14 5983 59609 32 _ _ (1099557 / 50000) (2199117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3553458432 :
    ThetaLowerSegment 3553458432 3553589504 (355339125302887 / 100000) (2220951299062 / 625) := by
  exact
    packedTile65536 3553458432 3553589504 14 5949 59610 32 _ _ (2199117 / 100000) (27489 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3553589504 :
    ThetaLowerSegment 3553589504 3553720576 (2220951299062 / 625) (355365316810201 / 100000) := by
  exact
    packedTile65536 3553589504 3553720576 14 5961 59611 32 _ _ (2199121 / 100000) (549781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3553720576 :
    ThetaLowerSegment 3553720576 3553851648 (355365316810201 / 100000)
      (355378524754951 / 100000) := by
  exact
    packedTile65536 3553720576 3553851648 14 6006 59613 32 _ _ (17593 / 800) (274891 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3553851648 :
    ThetaLowerSegment 3553851648 3553982720 (355378524754951 / 100000)
      (355391664544751 / 100000) := by
  exact
    packedTile65536 3553851648 3553982720 14 5975 59614 32 _ _ (274891 / 12500) (2199131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3553982720 :
    ThetaLowerSegment 3553982720 3554113792 (355391664544751 / 100000)
      (71080948556551 / 20000) := by
  exact
    packedTile65536 3553982720 3554113792 14 5947 59615 32 _ _ (549783 / 25000) (439827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3554113792 :
    ThetaLowerSegment 3554113792 3554244864 (71080948556551 / 20000)
      (355418001373699 / 100000) := by
  exact
    packedTile65536 3554113792 3554244864 14 6029 59616 32 _ _ (68723 / 3125) (2199139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3554244864 :
    ThetaLowerSegment 3554244864 3554375936 (355418001373699 / 100000)
      (88857796303001 / 25000) := by
  exact
    packedTile65536 3554244864 3554375936 14 5995 59617 32 _ _ (2199139 / 100000) (1099571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3554375936 :
    ThetaLowerSegment 3554375936 3554507008 (88857796303001 / 25000) (177722196632431 / 50000) := by
  exact
    packedTile65536 3554375936 3554507008 14 6006 59618 32 _ _ (2199143 / 100000) (1099573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3554507008 :
    ThetaLowerSegment 3554507008 3554638080 (177722196632431 / 50000) (44432171578807 / 12500) := by
  exact
    packedTile65536 3554507008 3554638080 14 5902 59619 32 _ _ (2199147 / 100000) (43983 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3554638080 :
    ThetaLowerSegment 3554638080 3554769152 (44432171578807 / 12500) (177735210093703 / 50000) := by
  exact
    packedTile65536 3554638080 3554769152 14 5933 59620 32 _ _ (43983 / 2000) (2199153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3554769152 :
    ThetaLowerSegment 3554769152 3554900224 (177735210093703 / 50000) (11108865240109 / 3125) := by
  exact
    packedTile65536 3554769152 3554900224 14 6033 59621 32 _ _ (1099577 / 50000) (2199157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3554900224 :
    ThetaLowerSegment 3554900224 3555031296 (11108865240109 / 3125) (177748457809429 / 50000) := by
  exact
    packedTile65536 3554900224 3555031296 14 6015 59622 32 _ _ (1099579 / 50000) (2199161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3555031296 :
    ThetaLowerSegment 3555031296 3555162368 (177748457809429 / 50000)
      (177754932139413 / 50000) := by
  exact
    packedTile65536 3555031296 3555162368 14 5888 59624 32 _ _ (2199161 / 100000) (549791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3555162368 :
    ThetaLowerSegment 3555162368 3555293440 (177754932139413 / 50000) (88880752721799 / 25000) := by
  exact
    packedTile65536 3555162368 3555293440 14 5978 59625 32 _ _ (439833 / 20000) (68724 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3555293440 :
    ThetaLowerSegment 3555293440 3555424512 (88880752721799 / 25000) (177768113946443 / 50000) := by
  exact
    packedTile65536 3555293440 3555424512 14 6010 59626 32 _ _ (2199169 / 100000) (549793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3555424512 :
    ThetaLowerSegment 3555424512 3555555584 (177768113946443 / 50000) (88887363429827 / 25000) := by
  exact
    packedTile65536 3555424512 3555555584 14 6014 59627 32 _ _ (2199173 / 100000) (274897 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3555555584 :
    ThetaLowerSegment 3555555584 3555686656 (88887363429827 / 25000) (88890634154333 / 25000) := by
  exact
    packedTile65536 3555555584 3555686656 14 5949 59628 32 _ _ (274897 / 12500) (2199179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3555686656 :
    ThetaLowerSegment 3555686656 3555817728 (88890634154333 / 25000) (88893887841143 / 25000) := by
  exact
    packedTile65536 3555686656 3555817728 14 5918 59629 32 _ _ (109959 / 5000) (2199183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3555817728 :
    ThetaLowerSegment 3555817728 3555948800 (88893887841143 / 25000) (3555885639363 / 1000) := by
  exact
    packedTile65536 3555817728 3555948800 14 5917 59630 32 _ _ (137449 / 6250) (2199187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3555948800 :
    ThetaLowerSegment 3555948800 3556079872 (3555885639363 / 1000) (177800952102321 / 50000) := by
  exact
    packedTile65536 3555948800 3556079872 14 6066 59631 32 _ _ (2199187 / 100000) (219919 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556079872 :
    ThetaLowerSegment 3556079872 3556210944 (177800952102321 / 50000)
      (177807523285029 / 50000) := by
  exact
    packedTile65536 3556079872 3556210944 14 5976 59632 32 _ _ (2199191 / 100000) (1099597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556210944 :
    ThetaLowerSegment 3556210944 3556342016 (177807523285029 / 50000)
      (355628160369843 / 100000) := by
  exact
    packedTile65536 3556210944 3556342016 14 5963 59633 32 _ _ (439839 / 20000) (1099599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556342016 :
    ThetaLowerSegment 3556342016 3556473088 (355628160369843 / 100000)
      (355641236801151 / 100000) := by
  exact
    packedTile65536 3556342016 3556473088 14 5946 59635 32 _ _ (1099599 / 50000) (2199201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556473088 :
    ThetaLowerSegment 3556473088 3556604160 (355641236801151 / 100000)
      (355654335248263 / 100000) := by
  exact
    packedTile65536 3556473088 3556604160 14 5956 59636 32 _ _ (1099601 / 50000) (439841 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556604160 :
    ThetaLowerSegment 3556604160 3556735232 (355654335248263 / 100000)
      (355667334754929 / 100000) := by
  exact
    packedTile65536 3556604160 3556735232 14 5911 59637 32 _ _ (1099603 / 50000) (2199209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556735232 :
    ThetaLowerSegment 3556735232 3556866304 (355667334754929 / 100000)
      (355680459634241 / 100000) := by
  exact
    packedTile65536 3556735232 3556866304 14 5968 59638 32 _ _ (2199209 / 100000) (549803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556866304 :
    ThetaLowerSegment 3556866304 3556997376 (355680459634241 / 100000)
      (71138708110633 / 20000) := by
  exact
    packedTile65536 3556866304 3556997376 14 5948 59639 32 _ _ (2199213 / 100000) (137451 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556997376 :
    ThetaLowerSegment 3556997376 3557128448 (71138708110633 / 20000) (71141325178863 / 20000) := by
  exact
    packedTile65536 3556997376 3557128448 14 5950 59640 32 _ _ (2199217 / 100000) (109961 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3557128448 :
    ThetaLowerSegment 3557128448 3557259520 (71141325178863 / 20000) (71143939611599 / 20000) := by
  exact
    packedTile65536 3557128448 3557259520 14 5944 59641 32 _ _ (109961 / 5000) (2199223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3557259520 :
    ThetaLowerSegment 3557259520 3557390592 (71143939611599 / 20000)
      (355732834022947 / 100000) := by
  exact
    packedTile65536 3557259520 3557390592 14 5973 59642 32 _ _ (274903 / 12500) (2199227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3557390592 :
    ThetaLowerSegment 3557390592 3557521664 (355732834022947 / 100000)
      (355745827061971 / 100000) := by
  exact
    packedTile65536 3557390592 3557521664 14 5908 59643 32 _ _ (549807 / 25000) (2199231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3557521664 :
    ThetaLowerSegment 3557521664 3557652736 (355745827061971 / 100000)
      (88939741866799 / 25000) := by
  exact
    packedTile65536 3557521664 3557652736 14 5975 59644 32 _ _ (2199231 / 100000) (1099617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3557652736 :
    ThetaLowerSegment 3557652736 3557783808 (88939741866799 / 25000) (11117877615773 / 3125) := by
  exact
    packedTile65536 3557652736 3557783808 14 5964 59646 32 _ _ (439847 / 20000) (1099619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3557783808 :
    ThetaLowerSegment 3557783808 3557914880 (11117877615773 / 3125) (355785114195811 / 100000) := by
  exact
    packedTile65536 3557783808 3557914880 14 5925 59647 32 _ _ (2199239 / 100000) (1099621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3557914880 :
    ThetaLowerSegment 3557914880 3558045952 (355785114195811 / 100000)
      (355798120518913 / 100000) := by
  exact
    packedTile65536 3557914880 3558045952 14 5914 59648 32 _ _ (2199243 / 100000) (1099623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3558045952 :
    ThetaLowerSegment 3558045952 3558177024 (355798120518913 / 100000)
      (71162244285467 / 20000) := by
  exact
    packedTile65536 3558045952 3558177024 14 5957 59649 32 _ _ (1099623 / 50000) (2199249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3558177024 :
    ThetaLowerSegment 3558177024 3558308096 (71162244285467 / 20000) (71164854795217 / 20000) := by
  exact
    packedTile65536 3558177024 3558308096 14 5935 59650 32 _ _ (8797 / 400) (2199253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3558308096 :
    ThetaLowerSegment 3558308096 3558439168 (71164854795217 / 20000)
      (355837506887403 / 100000) := by
  exact
    packedTile65536 3558308096 3558439168 14 6017 59651 32 _ _ (1099627 / 50000) (2199257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3558439168 :
    ThetaLowerSegment 3558439168 3558570240 (355837506887403 / 100000)
      (355850636451693 / 100000) := by
  exact
    packedTile65536 3558439168 3558570240 14 5970 59652 32 _ _ (2199257 / 100000) (109963 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3558570240 :
    ThetaLowerSegment 3558570240 3558701312 (355850636451693 / 100000)
      (177931833536559 / 50000) := by
  exact
    packedTile65536 3558570240 3558701312 14 5925 59653 32 _ _ (2199261 / 100000) (68727 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3558701312 :
    ThetaLowerSegment 3558701312 3558832384 (177931833536559 / 50000)
      (355876983622693 / 100000) := by
  exact
    packedTile65536 3558701312 3558832384 14 6055 59654 32 _ _ (439853 / 20000) (549817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3558832384 :
    ThetaLowerSegment 3558832384 3558963456 (355876983622693 / 100000)
      (355890201223373 / 100000) := by
  exact
    packedTile65536 3558832384 3558963456 14 6010 59655 32 _ _ (549817 / 25000) (2199271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3558963456 :
    ThetaLowerSegment 3558963456 3559094528 (355890201223373 / 100000)
      (355903258301237 / 100000) := by
  exact
    packedTile65536 3558963456 3559094528 14 5937 59657 32 _ _ (274909 / 12500) (87971 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3559094528 :
    ThetaLowerSegment 3559094528 3559225600 (355903258301237 / 100000)
      (355916511138413 / 100000) := by
  exact
    packedTile65536 3559094528 3559225600 14 6026 59658 32 _ _ (549819 / 25000) (2199279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3559225600 :
    ThetaLowerSegment 3559225600 3559356672 (355916511138413 / 100000)
      (355929530870093 / 100000) := by
  exact
    packedTile65536 3559225600 3559356672 14 5920 59659 32 _ _ (2199279 / 100000) (1099641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3559356672 :
    ThetaLowerSegment 3559356672 3559487744 (355929530870093 / 100000)
      (355942818937979 / 100000) := by
  exact
    packedTile65536 3559356672 3559487744 14 6042 59660 32 _ _ (2199283 / 100000) (1099643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3559487744 :
    ThetaLowerSegment 3559487744 3559618816 (355942818937979 / 100000)
      (177977990835337 / 50000) := by
  exact
    packedTile65536 3559487744 3559618816 14 5985 59661 32 _ _ (2199287 / 100000) (219929 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3559618816 :
    ThetaLowerSegment 3559618816 3559749888 (177977990835337 / 50000) (44496142502843 / 12500) := by
  exact
    packedTile65536 3559618816 3559749888 14 5983 59662 32 _ _ (219929 / 10000) (2199293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3559749888 :
    ThetaLowerSegment 3559749888 3559880960 (44496142502843 / 12500) (88995556455511 / 25000) := by
  exact
    packedTile65536 3559749888 3559880960 14 5950 59663 32 _ _ (1099647 / 50000) (2199297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3559880960 :
    ThetaLowerSegment 3559880960 3560012032 (88995556455511 / 25000) (177997698708883 / 50000) := by
  exact
    packedTile65536 3559880960 3560012032 14 5989 59664 32 _ _ (1099649 / 50000) (2199301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560012032 :
    ThetaLowerSegment 3560012032 3560143104 (177997698708883 / 50000)
      (178004155856619 / 50000) := by
  exact
    packedTile65536 3560012032 3560143104 14 5872 59665 32 _ _ (2199301 / 100000) (274913 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560143104 :
    ThetaLowerSegment 3560143104 3560274176 (178004155856619 / 50000)
      (356021368987023 / 100000) := by
  exact
    packedTile65536 3560143104 3560274176 14 5937 59666 32 _ _ (439861 / 20000) (549827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560274176 :
    ThetaLowerSegment 3560274176 3560405248 (356021368987023 / 100000)
      (35603430752187 / 10000) := by
  exact
    packedTile65536 3560274176 3560405248 14 5883 59668 32 _ _ (2199309 / 100000) (137457 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560405248 :
    ThetaLowerSegment 3560405248 3560536320 (35603430752187 / 10000) (35604737144109 / 10000) := by
  exact
    packedTile65536 3560405248 3560536320 14 5940 59669 32 _ _ (2199313 / 100000) (549829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560536320 :
    ThetaLowerSegment 3560536320 3560667392 (35604737144109 / 10000) (178030266074017 / 50000) := by
  exact
    packedTile65536 3560536320 3560667392 14 5984 59670 32 _ _ (549829 / 25000) (2199319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560667392 :
    ThetaLowerSegment 3560667392 3560798464 (178030266074017 / 50000)
      (178036832143877 / 50000) := by
  exact
    packedTile65536 3560667392 3560798464 14 5971 59671 32 _ _ (54983 / 2500) (2199323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560798464 :
    ThetaLowerSegment 3560798464 3560929536 (178036832143877 / 50000)
      (178043305854071 / 50000) := by
  exact
    packedTile65536 3560798464 3560929536 14 5887 59672 32 _ _ (549831 / 25000) (2199327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560929536 :
    ThetaLowerSegment 3560929536 3561060608 (178043305854071 / 50000) (14243986060717 / 4000) := by
  exact
    packedTile65536 3560929536 3561060608 14 5929 59673 32 _ _ (2199327 / 100000) (219933 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561060608 :
    ThetaLowerSegment 3561060608 3561191680 (14243986060717 / 4000) (178056343476381 / 50000) := by
  exact
    packedTile65536 3561060608 3561191680 14 5927 59674 32 _ _ (2199331 / 100000) (1099667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561191680 :
    ThetaLowerSegment 3561191680 3561322752 (178056343476381 / 50000) (89031438850333 / 25000) := by
  exact
    packedTile65536 3561191680 3561322752 14 5942 59675 32 _ _ (439867 / 20000) (1099669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561322752 :
    ThetaLowerSegment 3561322752 3561339136 (89031438850333 / 25000) (89031823734483 / 25000) := by
  exact
    packedTile65536 3561322752 3561339136 11 700 59676 32 _ _ (1099669 / 50000) (2199341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561339136 :
    ThetaLowerSegment 3561339136 3561341184 (89031823734483 / 25000)
      (356127495077781 / 100000) := by
  exact
    packedTile65536 3561339136 3561341184 8 91 59676 32 _ _ (2199339 / 100000) (1099671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3529341184_3561341184 :
    ThetaLowerSegment 3529341184 3561341184 (88231801307081 / 25000)
      (356127495077781 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3529341184 cell3529472256)
                  (ThetaLowerSegment.join cell3529603328 cell3529734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3529865472 cell3529996544)
                  (ThetaLowerSegment.join cell3530127616 cell3530258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3530389760 cell3530520832)
                  (ThetaLowerSegment.join cell3530651904 cell3530782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3530914048 cell3531045120)
                  (ThetaLowerSegment.join cell3531176192 cell3531307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3531438336 cell3531569408)
                  (ThetaLowerSegment.join cell3531700480 cell3531831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3531962624 cell3532093696)
                  (ThetaLowerSegment.join cell3532224768 cell3532355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3532486912 cell3532617984)
                  (ThetaLowerSegment.join cell3532749056 cell3532880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3533011200 cell3533142272)
                  (ThetaLowerSegment.join cell3533273344 cell3533404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3533535488 cell3533666560)
                  (ThetaLowerSegment.join cell3533797632 cell3533928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3534059776 cell3534190848)
                  (ThetaLowerSegment.join cell3534321920 cell3534452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3534584064 cell3534715136)
                  (ThetaLowerSegment.join cell3534846208 cell3534977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3535108352 cell3535239424)
                  (ThetaLowerSegment.join cell3535370496 cell3535501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3535632640 cell3535763712)
                  (ThetaLowerSegment.join cell3535894784 cell3536025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3536156928 cell3536288000)
                  (ThetaLowerSegment.join cell3536419072 cell3536550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3536681216 cell3536812288)
                  (ThetaLowerSegment.join cell3536943360 cell3537074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3537205504 cell3537336576)
                  (ThetaLowerSegment.join cell3537467648 cell3537598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3537729792 cell3537860864)
                  (ThetaLowerSegment.join cell3537991936 cell3538123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3538254080 cell3538385152)
                  (ThetaLowerSegment.join cell3538516224 cell3538647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3538778368 cell3538909440)
                  (ThetaLowerSegment.join cell3539040512 cell3539171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3539302656 cell3539433728)
                  (ThetaLowerSegment.join cell3539564800 cell3539695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3539826944 cell3539958016)
                  (ThetaLowerSegment.join cell3540089088 cell3540220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3540351232 cell3540482304)
                  (ThetaLowerSegment.join cell3540613376 cell3540744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3540875520 cell3541006592)
                  (ThetaLowerSegment.join cell3541137664 cell3541268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3541399808 cell3541530880)
                  (ThetaLowerSegment.join cell3541661952 cell3541793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3541924096 cell3542055168)
                  (ThetaLowerSegment.join cell3542186240 cell3542317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3542448384 cell3542579456)
                  (ThetaLowerSegment.join cell3542710528 cell3542841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3542972672 cell3543103744)
                  (ThetaLowerSegment.join cell3543234816 cell3543365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3543496960 cell3543628032)
                  (ThetaLowerSegment.join cell3543759104 cell3543890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3544021248 cell3544152320)
                  (ThetaLowerSegment.join cell3544283392 cell3544414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3544545536 cell3544676608)
                  (ThetaLowerSegment.join cell3544807680 cell3544938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3545069824 cell3545200896)
                  (ThetaLowerSegment.join cell3545331968 cell3545463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3545594112 cell3545725184)
                  (ThetaLowerSegment.join cell3545856256 cell3545987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3546118400 cell3546249472)
                  (ThetaLowerSegment.join cell3546380544 cell3546511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3546642688 cell3546773760)
                  (ThetaLowerSegment.join cell3546904832 cell3547035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3547166976 cell3547298048)
                  (ThetaLowerSegment.join cell3547429120 cell3547560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3547691264 cell3547822336)
                  (ThetaLowerSegment.join cell3547953408 cell3548084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3548215552 cell3548346624)
                  (ThetaLowerSegment.join cell3548477696 cell3548608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3548739840 cell3548870912)
                  (ThetaLowerSegment.join cell3549001984 cell3549133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3549264128 cell3549395200)
                  (ThetaLowerSegment.join cell3549526272 cell3549657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3549788416 cell3549919488)
                  (ThetaLowerSegment.join cell3550050560 cell3550181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3550312704 cell3550443776)
                  (ThetaLowerSegment.join cell3550574848 cell3550705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3550836992 cell3550968064)
                  (ThetaLowerSegment.join cell3551099136 cell3551230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3551361280 cell3551492352)
                  (ThetaLowerSegment.join cell3551623424 cell3551754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3551885568 cell3552016640)
                  (ThetaLowerSegment.join cell3552147712 cell3552278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3552409856 cell3552540928)
                  (ThetaLowerSegment.join cell3552672000 cell3552803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3552934144 cell3553065216)
                  (ThetaLowerSegment.join cell3553196288 cell3553327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3553458432 cell3553589504)
                  (ThetaLowerSegment.join cell3553720576 cell3553851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3553982720 cell3554113792)
                  (ThetaLowerSegment.join cell3554244864 cell3554375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3554507008 cell3554638080)
                  (ThetaLowerSegment.join cell3554769152 cell3554900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3555031296 cell3555162368)
                  (ThetaLowerSegment.join cell3555293440 cell3555424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3555555584 cell3555686656)
                  (ThetaLowerSegment.join cell3555817728 cell3555948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3556079872 cell3556210944)
                  (ThetaLowerSegment.join cell3556342016 cell3556473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3556604160 cell3556735232)
                  (ThetaLowerSegment.join cell3556866304 cell3556997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3557128448 cell3557259520)
                  (ThetaLowerSegment.join cell3557390592 cell3557521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3557652736 cell3557783808)
                  (ThetaLowerSegment.join cell3557914880 cell3558045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3558177024 cell3558308096)
                  (ThetaLowerSegment.join cell3558439168 cell3558570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3558701312 cell3558832384)
                  (ThetaLowerSegment.join cell3558963456 cell3559094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3559225600 cell3559356672)
                  (ThetaLowerSegment.join cell3559487744 cell3559618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3559749888 cell3559880960)
                  (ThetaLowerSegment.join cell3560012032 cell3560143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3560274176 cell3560405248)
                  (ThetaLowerSegment.join cell3560536320 cell3560667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3560798464 cell3560929536)
                (ThetaLowerSegment.join cell3561060608 cell3561191680))
              (ThetaLowerSegment.join cell3561322752 cell3561339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
