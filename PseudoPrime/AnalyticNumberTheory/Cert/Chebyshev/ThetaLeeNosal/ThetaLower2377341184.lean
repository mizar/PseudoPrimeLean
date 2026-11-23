/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2377341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2345341184 :
    ThetaLowerSegment 2345341184 2345472256 (11726432528937 / 5000) (58635443226829 / 25000) := by
  exact
    packedTile65536 2345341184 2345472256 14 6082 48428 31 _ _ (67424 / 3125) (2157571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345472256 :
    ThetaLowerSegment 2345472256 2345603328 (58635443226829 / 25000) (14659669087867 / 6250) := by
  exact
    packedTile65536 2345472256 2345603328 14 5994 48430 31 _ _ (1078787 / 50000) (2157577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345603328 :
    ThetaLowerSegment 2345603328 2345734400 (14659669087867 / 6250) (234567834274087 / 100000) := by
  exact
    packedTile65536 2345603328 2345734400 14 6085 48431 31 _ _ (2157579 / 100000) (1078791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345734400 :
    ThetaLowerSegment 2345734400 2345865472 (234567834274087 / 100000)
      (117290496692501 / 50000) := by
  exact
    packedTile65536 2345734400 2345865472 14 6099 48432 31 _ _ (431517 / 20000) (539397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345865472 :
    ThetaLowerSegment 2345865472 2345996544 (117290496692501 / 50000)
      (234594105065509 / 100000) := by
  exact
    packedTile65536 2345865472 2345996544 14 6077 48434 31 _ _ (2157591 / 100000) (1078797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345996544 :
    ThetaLowerSegment 2345996544 2346127616 (234594105065509 / 100000)
      (234607316025817 / 100000) := by
  exact
    packedTile65536 2345996544 2346127616 14 6123 48435 31 _ _ (539399 / 25000) (2157599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2346127616 :
    ThetaLowerSegment 2346127616 2346258688 (234607316025817 / 100000)
      (46924045423237 / 20000) := by
  exact
    packedTile65536 2346127616 2346258688 14 5984 48436 31 _ _ (1078801 / 50000) (431521 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2346258688 :
    ThetaLowerSegment 2346258688 2346389760 (46924045423237 / 20000) (5865834982673 / 2500) := by
  exact
    packedTile65536 2346258688 2346389760 14 6105 48438 31 _ _ (2157607 / 100000) (215761 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2346389760 :
    ThetaLowerSegment 2346389760 2346520832 (5865834982673 / 2500) (1466540195559 / 625) := by
  exact
    packedTile65536 2346389760 2346520832 14 6040 48439 31 _ _ (2157613 / 100000) (134851 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2346520832 :
    ThetaLowerSegment 2346520832 2346651904 (1466540195559 / 625) (14666229402093 / 6250) := by
  exact
    packedTile65536 2346520832 2346651904 14 6136 48440 31 _ _ (1078809 / 50000) (2157621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2346651904 :
    ThetaLowerSegment 2346651904 2346782976 (14666229402093 / 6250) (29334106419813 / 12500) := by
  exact
    packedTile65536 2346651904 2346782976 14 6109 48442 31 _ _ (269703 / 12500) (2157627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2346782976 :
    ThetaLowerSegment 2346782976 2346914048 (29334106419813 / 12500) (58671497831301 / 25000) := by
  exact
    packedTile65536 2346782976 2346914048 14 6090 48443 31 _ _ (215763 / 10000) (2157633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2346914048 :
    ThetaLowerSegment 2346914048 2347045120 (58671497831301 / 25000)
      (234698943608109 / 100000) := by
  exact
    packedTile65536 2346914048 2347045120 14 6003 48444 31 _ _ (431527 / 20000) (1078819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2347045120 :
    ThetaLowerSegment 2347045120 2347176192 (234698943608109 / 100000)
      (234712057750107 / 100000) := by
  exact
    packedTile65536 2347045120 2347176192 14 6078 48446 31 _ _ (2157641 / 100000) (539411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2347176192 :
    ThetaLowerSegment 2347176192 2347307264 (234712057750107 / 100000)
      (234725184868371 / 100000) := by
  exact
    packedTile65536 2347176192 2347307264 14 6084 48447 31 _ _ (1078823 / 50000) (2157649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2347307264 :
    ThetaLowerSegment 2347307264 2347438336 (234725184868371 / 100000)
      (234738217086451 / 100000) := by
  exact
    packedTile65536 2347307264 2347438336 14 6040 48449 31 _ _ (539413 / 25000) (431531 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2347438336 :
    ThetaLowerSegment 2347438336 2347569408 (234738217086451 / 100000)
      (234751411165121 / 100000) := by
  exact
    packedTile65536 2347438336 2347569408 14 6115 48450 31 _ _ (1078829 / 50000) (2157661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2347569408 :
    ThetaLowerSegment 2347569408 2347700480 (234751411165121 / 100000)
      (234764495233553 / 100000) := by
  exact
    packedTile65536 2347569408 2347700480 14 6064 48451 31 _ _ (2157663 / 100000) (1078833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2347700480 :
    ThetaLowerSegment 2347700480 2347831552 (234764495233553 / 100000)
      (29347200384091 / 12500) := by
  exact
    packedTile65536 2347700480 2347831552 14 6075 48453 31 _ _ (2157669 / 100000) (269709 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2347831552 :
    ThetaLowerSegment 2347831552 2347962624 (29347200384091 / 12500) (58697653461737 / 25000) := by
  exact
    packedTile65536 2347831552 2347962624 14 6030 48454 31 _ _ (1078837 / 50000) (2157677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2347962624 :
    ThetaLowerSegment 2347962624 2348093696 (58697653461737 / 25000) (58700952554457 / 25000) := by
  exact
    packedTile65536 2347962624 2348093696 14 6116 48455 31 _ _ (26971 / 1250) (2157683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2348093696 :
    ThetaLowerSegment 2348093696 2348224768 (58700952554457 / 25000) (117408449367519 / 50000) := by
  exact
    packedTile65536 2348093696 2348224768 14 6066 48457 31 _ _ (431537 / 20000) (269711 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2348224768 :
    ThetaLowerSegment 2348224768 2348355840 (117408449367519 / 50000) (4696598278543 / 2000) := by
  exact
    packedTile65536 2348224768 2348355840 14 6032 48458 31 _ _ (2157691 / 100000) (1078847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2348355840 :
    ThetaLowerSegment 2348355840 2348486912 (4696598278543 / 2000) (234843017621031 / 100000) := by
  exact
    packedTile65536 2348355840 2348486912 14 6073 48459 31 _ _ (2157697 / 100000) (21577 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2348486912 :
    ThetaLowerSegment 2348486912 2348617984 (234843017621031 / 100000)
      (234855976779243 / 100000) := by
  exact
    packedTile65536 2348486912 2348617984 14 6006 48461 31 _ _ (1078851 / 50000) (431541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2348617984 :
    ThetaLowerSegment 2348617984 2348749056 (234855976779243 / 100000)
      (234869080539927 / 100000) := by
  exact
    packedTile65536 2348617984 2348749056 14 6073 48462 31 _ _ (539427 / 25000) (2157711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2348749056 :
    ThetaLowerSegment 2348749056 2348880128 (234869080539927 / 100000)
      (234882242589227 / 100000) := by
  exact
    packedTile65536 2348749056 2348880128 14 6100 48463 31 _ _ (2157713 / 100000) (539429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2348880128 :
    ThetaLowerSegment 2348880128 2349011200 (234882242589227 / 100000)
      (46979060220923 / 20000) := by
  exact
    packedTile65536 2348880128 2349011200 14 6052 48465 31 _ _ (2157719 / 100000) (1078861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2349011200 :
    ThetaLowerSegment 2349011200 2349142272 (46979060220923 / 20000) (11745423700787 / 5000) := by
  exact
    packedTile65536 2349011200 2349142272 14 6105 48466 31 _ _ (86309 / 4000) (67429 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2349142272 :
    ThetaLowerSegment 2349142272 2349273344 (11745423700787 / 5000) (11746073609063 / 5000) := by
  exact
    packedTile65536 2349142272 2349273344 14 6024 48467 31 _ _ (215773 / 10000) (2157733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2349273344 :
    ThetaLowerSegment 2349273344 2349404416 (11746073609063 / 5000) (11746733876279 / 5000) := by
  exact
    packedTile65536 2349273344 2349404416 14 6120 48469 31 _ _ (269717 / 12500) (2157739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2349404416 :
    ThetaLowerSegment 2349404416 2349535488 (11746733876279 / 5000) (234947816010529 / 100000) := by
  exact
    packedTile65536 2349404416 2349535488 14 6089 48470 31 _ _ (2157741 / 100000) (134859 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2349535488 :
    ThetaLowerSegment 2349535488 2349666560 (234947816010529 / 100000) (7342529559407 / 3125) := by
  exact
    packedTile65536 2349535488 2349666560 14 6085 48472 31 _ _ (2157747 / 100000) (8631 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2349666560 :
    ThetaLowerSegment 2349666560 2349797632 (7342529559407 / 3125) (29371747610107 / 12500) := by
  exact
    packedTile65536 2349666560 2349797632 14 6041 48473 31 _ _ (269719 / 12500) (431551 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2349797632 :
    ThetaLowerSegment 2349797632 2349928704 (29371747610107 / 12500) (117493548945869 / 50000) := by
  exact
    packedTile65536 2349797632 2349928704 14 6079 48474 31 _ _ (1078879 / 50000) (2157761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2349928704 :
    ThetaLowerSegment 2349928704 2350059776 (117493548945869 / 50000) (23500024514779 / 10000) := by
  exact
    packedTile65536 2349928704 2350059776 14 6093 48476 31 _ _ (539441 / 25000) (2157767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2350059776 :
    ThetaLowerSegment 2350059776 2350190848 (23500024514779 / 10000)
      (235013336332313 / 100000) := by
  exact
    packedTile65536 2350059776 2350190848 14 6067 48477 31 _ _ (2157769 / 100000) (539443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2350190848 :
    ThetaLowerSegment 2350190848 2350321920 (235013336332313 / 100000)
      (117513200829969 / 50000) := by
  exact
    packedTile65536 2350190848 2350321920 14 6055 48478 31 _ _ (86311 / 4000) (1078889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2350321920 :
    ThetaLowerSegment 2350321920 2350452992 (117513200829969 / 50000)
      (117519796084539 / 50000) := by
  exact
    packedTile65536 2350321920 2350452992 14 6113 48480 31 _ _ (107889 / 5000) (2157783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2350452992 :
    ThetaLowerSegment 2350452992 2350584064 (117519796084539 / 50000) (14690798919681 / 6250) := by
  exact
    packedTile65536 2350452992 2350584064 14 6113 48481 31 _ _ (1078893 / 50000) (2157789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2350584064 :
    ThetaLowerSegment 2350584064 2350715136 (14690798919681 / 6250) (23506580282579 / 10000) := by
  exact
    packedTile65536 2350584064 2350715136 14 6034 48482 31 _ _ (2157791 / 100000) (1078897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2350715136 :
    ThetaLowerSegment 2350715136 2350846208 (23506580282579 / 10000) (14692425356907 / 6250) := by
  exact
    packedTile65536 2350715136 2350846208 14 6026 48484 31 _ _ (2157797 / 100000) (10789 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2350846208 :
    ThetaLowerSegment 2350846208 2350977280 (14692425356907 / 6250) (235092108566007 / 100000) := by
  exact
    packedTile65536 2350846208 2350977280 14 6165 48485 31 _ _ (2157803 / 100000) (1078903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2350977280 :
    ThetaLowerSegment 2350977280 2351108352 (235092108566007 / 100000)
      (47021035250251 / 20000) := by
  exact
    packedTile65536 2350977280 2351108352 14 6056 48486 31 _ _ (134863 / 6250) (2157811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2351108352 :
    ThetaLowerSegment 2351108352 2351239424 (47021035250251 / 20000)
      (235118267708793 / 100000) := by
  exact
    packedTile65536 2351108352 2351239424 14 6067 48488 31 _ _ (1078907 / 50000) (2157817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2351239424 :
    ThetaLowerSegment 2351239424 2351370496 (235118267708793 / 100000)
      (235131357038847 / 100000) := by
  exact
    packedTile65536 2351239424 2351370496 14 6066 48489 31 _ _ (2157819 / 100000) (1078911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2351370496 :
    ThetaLowerSegment 2351370496 2351501568 (235131357038847 / 100000)
      (117572224281561 / 50000) := by
  exact
    packedTile65536 2351370496 2351501568 14 6067 48490 31 _ _ (86313 / 4000) (539457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2351501568 :
    ThetaLowerSegment 2351501568 2351632640 (117572224281561 / 50000) (58789372082453 / 25000) := by
  exact
    packedTile65536 2351501568 2351632640 14 6043 48492 31 _ _ (215783 / 10000) (2157833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2351632640 :
    ThetaLowerSegment 2351632640 2351763712 (58789372082453 / 25000) (58792657387763 / 25000) := by
  exact
    packedTile65536 2351632640 2351763712 14 6090 48493 31 _ _ (539459 / 25000) (2157839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2351763712 :
    ThetaLowerSegment 2351763712 2351894784 (58792657387763 / 25000) (29397955167289 / 12500) := by
  exact
    packedTile65536 2351763712 2351894784 14 6030 48494 31 _ _ (1078921 / 50000) (431569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2351894784 :
    ThetaLowerSegment 2351894784 2352025856 (29397955167289 / 12500) (47039356093739 / 20000) := by
  exact
    packedTile65536 2351894784 2352025856 14 6089 48496 31 _ _ (2157847 / 100000) (43157 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352025856 :
    ThetaLowerSegment 2352025856 2352156928 (47039356093739 / 20000)
      (235209757796637 / 100000) := by
  exact
    packedTile65536 2352025856 2352156928 14 6014 48497 31 _ _ (2157853 / 100000) (67433 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352156928 :
    ThetaLowerSegment 2352156928 2352288000 (235209757796637 / 100000)
      (235222970361171 / 100000) := by
  exact
    packedTile65536 2352156928 2352288000 14 6123 48499 31 _ _ (1078929 / 50000) (2157861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352288000 :
    ThetaLowerSegment 2352288000 2352419072 (235222970361171 / 100000)
      (235236021122643 / 100000) := by
  exact
    packedTile65536 2352288000 2352419072 14 6048 48500 31 _ _ (269733 / 12500) (2157867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352419072 :
    ThetaLowerSegment 2352419072 2352550144 (235236021122643 / 100000)
      (235249080551883 / 100000) := by
  exact
    packedTile65536 2352419072 2352550144 14 6052 48501 31 _ _ (215787 / 10000) (2157873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352550144 :
    ThetaLowerSegment 2352550144 2352681216 (235249080551883 / 100000)
      (58815534463377 / 25000) := by
  exact
    packedTile65536 2352550144 2352681216 14 6051 48503 31 _ _ (17263 / 800) (1078939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352681216 :
    ThetaLowerSegment 2352681216 2352812288 (58815534463377 / 25000) (117637756199973 / 50000) := by
  exact
    packedTile65536 2352681216 2352812288 14 6198 48504 31 _ _ (2157881 / 100000) (539471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352812288 :
    ThetaLowerSegment 2352812288 2352943360 (117637756199973 / 50000)
      (117644357173247 / 50000) := by
  exact
    packedTile65536 2352812288 2352943360 14 6118 48505 31 _ _ (1078943 / 50000) (2157889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352943360 :
    ThetaLowerSegment 2352943360 2353074432 (117644357173247 / 50000) (4706039405541 / 2000) := by
  exact
    packedTile65536 2352943360 2353074432 14 6143 48507 31 _ _ (539473 / 25000) (431579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2353074432 :
    ThetaLowerSegment 2353074432 2353205504 (4706039405541 / 2000) (235315118343471 / 100000) := by
  exact
    packedTile65536 2353074432 2353205504 14 6093 48508 31 _ _ (2157897 / 100000) (21579 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2353205504 :
    ThetaLowerSegment 2353205504 2353336576 (235315118343471 / 100000)
      (23532818013033 / 10000) := by
  exact
    packedTile65536 2353205504 2353336576 14 6053 48509 31 _ _ (2157903 / 100000) (1078953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2353336576 :
    ThetaLowerSegment 2353336576 2353467648 (23532818013033 / 10000) (23534123547373 / 10000) := by
  exact
    packedTile65536 2353336576 2353467648 14 6050 48511 31 _ _ (539477 / 25000) (2157911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2353467648 :
    ThetaLowerSegment 2353467648 2353598720 (23534123547373 / 10000) (117677171321683 / 50000) := by
  exact
    packedTile65536 2353467648 2353598720 14 6074 48512 31 _ _ (1078957 / 50000) (2157917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2353598720 :
    ThetaLowerSegment 2353598720 2353729792 (117677171321683 / 50000)
      (117683799372963 / 50000) := by
  exact
    packedTile65536 2353598720 2353729792 14 6143 48513 31 _ _ (13487 / 625) (2157923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2353729792 :
    ThetaLowerSegment 2353729792 2353860864 (117683799372963 / 50000)
      (235380703824451 / 100000) := by
  exact
    packedTile65536 2353729792 2353860864 14 6073 48515 31 _ _ (86317 / 4000) (269741 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2353860864 :
    ThetaLowerSegment 2353860864 2353991936 (235380703824451 / 100000)
      (58848414471061 / 25000) := by
  exact
    packedTile65536 2353860864 2353991936 14 6003 48516 31 _ _ (2157931 / 100000) (1078967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2353991936 :
    ThetaLowerSegment 2353991936 2354123008 (58848414471061 / 25000) (11770330922393 / 5000) := by
  exact
    packedTile65536 2353991936 2354123008 14 6006 48517 31 _ _ (134871 / 6250) (2157939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2354123008 :
    ThetaLowerSegment 2354123008 2354254080 (11770330922393 / 5000) (23541979268377 / 10000) := by
  exact
    packedTile65536 2354123008 2354254080 14 6105 48519 31 _ _ (1078971 / 50000) (431589 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2354254080 :
    ThetaLowerSegment 2354254080 2354385152 (23541979268377 / 10000) (58858227171409 / 25000) := by
  exact
    packedTile65536 2354254080 2354385152 14 6078 48520 31 _ _ (2157947 / 100000) (43159 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2354385152 :
    ThetaLowerSegment 2354385152 2354516224 (58858227171409 / 25000) (29430759024867 / 12500) := by
  exact
    packedTile65536 2354385152 2354516224 14 6100 48522 31 _ _ (2157953 / 100000) (539489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2354516224 :
    ThetaLowerSegment 2354516224 2354647296 (29430759024867 / 12500) (117729611400541 / 50000) := by
  exact
    packedTile65536 2354516224 2354647296 14 6094 48523 31 _ _ (2157959 / 100000) (1078981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2354647296 :
    ThetaLowerSegment 2354647296 2354778368 (117729611400541 / 50000)
      (117736140320623 / 50000) := by
  exact
    packedTile65536 2354647296 2354778368 14 6051 48524 31 _ _ (539491 / 25000) (2157967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2354778368 :
    ThetaLowerSegment 2354778368 2354909440 (117736140320623 / 50000) (14717837703551 / 6250) := by
  exact
    packedTile65536 2354778368 2354909440 14 6081 48526 31 _ _ (215797 / 10000) (2157973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2354909440 :
    ThetaLowerSegment 2354909440 2355040512 (14717837703551 / 6250) (117749199291133 / 50000) := by
  exact
    packedTile65536 2354909440 2355040512 14 6022 48527 31 _ _ (86319 / 4000) (1078989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2355040512 :
    ThetaLowerSegment 2355040512 2355171584 (117749199291133 / 50000) (47102277493981 / 20000) := by
  exact
    packedTile65536 2355040512 2355171584 14 6019 48528 31 _ _ (2157981 / 100000) (67437 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2355171584 :
    ThetaLowerSegment 2355171584 2355302656 (47102277493981 / 20000)
      (235524553342491 / 100000) := by
  exact
    packedTile65536 2355171584 2355302656 14 6101 48530 31 _ _ (1078993 / 50000) (2157989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2355302656 :
    ThetaLowerSegment 2355302656 2355433728 (235524553342491 / 100000)
      (47107527017999 / 20000) := by
  exact
    packedTile65536 2355302656 2355433728 14 6062 48531 31 _ _ (269749 / 12500) (431599 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2355433728 :
    ThetaLowerSegment 2355433728 2355564800 (47107527017999 / 20000)
      (235550706083881 / 100000) := by
  exact
    packedTile65536 2355433728 2355564800 14 6057 48532 31 _ _ (1078999 / 50000) (2158001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2355564800 :
    ThetaLowerSegment 2355564800 2355695872 (235550706083881 / 100000)
      (235563744738007 / 100000) := by
  exact
    packedTile65536 2355564800 2355695872 14 6042 48534 31 _ _ (2158003 / 100000) (1079003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2355695872 :
    ThetaLowerSegment 2355695872 2355826944 (235563744738007 / 100000)
      (29447119238887 / 12500) := by
  exact
    packedTile65536 2355695872 2355826944 14 6121 48535 31 _ _ (2158009 / 100000) (539503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2355826944 :
    ThetaLowerSegment 2355826944 2355958016 (29447119238887 / 12500) (29448770119597 / 12500) := by
  exact
    packedTile65536 2355826944 2355958016 14 6120 48536 31 _ _ (1079007 / 50000) (2158017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2355958016 :
    ThetaLowerSegment 2355958016 2356089088 (29448770119597 / 12500) (58900768097609 / 25000) := by
  exact
    packedTile65536 2355958016 2356089088 14 5983 48538 31 _ _ (107901 / 5000) (2158023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2356089088 :
    ThetaLowerSegment 2356089088 2356220160 (58900768097609 / 25000) (117808025376393 / 50000) := by
  exact
    packedTile65536 2356089088 2356220160 14 6014 48539 31 _ _ (86321 / 4000) (539507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2356220160 :
    ThetaLowerSegment 2356220160 2356351232 (117808025376393 / 50000) (9425170229779 / 4000) := by
  exact
    packedTile65536 2356220160 2356351232 14 6119 48540 31 _ _ (2158031 / 100000) (1079017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2356351232 :
    ThetaLowerSegment 2356351232 2356482304 (9425170229779 / 4000) (117821243334661 / 50000) := by
  exact
    packedTile65536 2356351232 2356482304 14 6131 48542 31 _ _ (2158037 / 100000) (53951 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2356482304 :
    ThetaLowerSegment 2356482304 2356613376 (117821243334661 / 50000) (14728471021831 / 6250) := by
  exact
    packedTile65536 2356482304 2356613376 14 6047 48543 31 _ _ (1079021 / 50000) (431609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2356613376 :
    ThetaLowerSegment 2356613376 2356744448 (14728471021831 / 6250) (14729293238119 / 6250) := by
  exact
    packedTile65536 2356613376 2356744448 14 6096 48544 31 _ _ (67439 / 3125) (2158051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2356744448 :
    ThetaLowerSegment 2356744448 2356875520 (14729293238119 / 6250) (235681810614091 / 100000) := by
  exact
    packedTile65536 2356744448 2356875520 14 6079 48546 31 _ _ (2158053 / 100000) (269757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2356875520 :
    ThetaLowerSegment 2356875520 2357006592 (235681810614091 / 100000)
      (47138997544469 / 20000) := by
  exact
    packedTile65536 2356875520 2357006592 14 6106 48547 31 _ _ (2158059 / 100000) (1079031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2357006592 :
    ThetaLowerSegment 2357006592 2357137664 (47138997544469 / 20000)
      (235707854099913 / 100000) := by
  exact
    packedTile65536 2357006592 2357137664 14 5962 48549 31 _ _ (134879 / 6250) (2158067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2357137664 :
    ThetaLowerSegment 2357137664 2357268736 (235707854099913 / 100000)
      (235721014010773 / 100000) := by
  exact
    packedTile65536 2357137664 2357268736 14 6098 48550 31 _ _ (215807 / 10000) (2158073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2357268736 :
    ThetaLowerSegment 2357268736 2357399808 (235721014010773 / 100000)
      (235734087629123 / 100000) := by
  exact
    packedTile65536 2357268736 2357399808 14 6058 48551 31 _ _ (86323 / 4000) (1079039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2357399808 :
    ThetaLowerSegment 2357399808 2357530880 (235734087629123 / 100000)
      (235747165599983 / 100000) := by
  exact
    packedTile65536 2357399808 2357530880 14 6060 48553 31 _ _ (2158081 / 100000) (539521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2357530880 :
    ThetaLowerSegment 2357530880 2357661952 (235747165599983 / 100000)
      (58940064678453 / 25000) := by
  exact
    packedTile65536 2357530880 2357661952 14 6067 48554 31 _ _ (2158087 / 100000) (215809 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2357661952 :
    ThetaLowerSegment 2357661952 2357793024 (58940064678453 / 25000) (58943366559213 / 25000) := by
  exact
    packedTile65536 2357661952 2357793024 14 6120 48555 31 _ _ (539523 / 25000) (431619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2357793024 :
    ThetaLowerSegment 2357793024 2357924096 (58943366559213 / 25000) (29473317499317 / 12500) := by
  exact
    packedTile65536 2357793024 2357924096 14 6058 48557 31 _ _ (1079049 / 50000) (2158101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2357924096 :
    ThetaLowerSegment 2357924096 2358055168 (29473317499317 / 12500) (943199145723 / 400) := by
  exact
    packedTile65536 2357924096 2358055168 14 6138 48558 31 _ _ (2158103 / 100000) (1079053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2358055168 :
    ThetaLowerSegment 2358055168 2358186240 (943199145723 / 400) (58953230170531 / 25000) := by
  exact
    packedTile65536 2358055168 2358186240 14 6086 48559 31 _ _ (2158109 / 100000) (67441 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2358186240 :
    ThetaLowerSegment 2358186240 2358317312 (58953230170531 / 25000) (117913050142161 / 50000) := by
  exact
    packedTile65536 2358186240 2358317312 14 6107 48561 31 _ _ (1079057 / 50000) (2158117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2358317312 :
    ThetaLowerSegment 2358317312 2358448384 (117913050142161 / 50000)
      (117919571980801 / 50000) := by
  exact
    packedTile65536 2358317312 2358448384 14 6044 48562 31 _ _ (53953 / 2500) (2158123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2358448384 :
    ThetaLowerSegment 2358448384 2358579456 (117919571980801 / 50000)
      (235852487648477 / 100000) := by
  exact
    packedTile65536 2358448384 2358579456 14 6183 48563 31 _ _ (3453 / 160) (134883 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2358579456 :
    ThetaLowerSegment 2358579456 2358710528 (235852487648477 / 100000)
      (235865406220643 / 100000) := by
  exact
    packedTile65536 2358579456 2358710528 14 5986 48565 31 _ _ (2158131 / 100000) (1079067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2358710528 :
    ThetaLowerSegment 2358710528 2358841600 (235865406220643 / 100000)
      (235878523377329 / 100000) := by
  exact
    packedTile65536 2358710528 2358841600 14 6078 48566 31 _ _ (2158137 / 100000) (107907 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2358841600 :
    ThetaLowerSegment 2358841600 2358972672 (235878523377329 / 100000)
      (47178297898893 / 20000) := by
  exact
    packedTile65536 2358841600 2358972672 14 6008 48567 31 _ _ (1079071 / 50000) (431629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2358972672 :
    ThetaLowerSegment 2358972672 2359103744 (47178297898893 / 20000)
      (235904587294677 / 100000) := by
  exact
    packedTile65536 2358972672 2359103744 14 6069 48569 31 _ _ (539537 / 25000) (2158151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2359103744 :
    ThetaLowerSegment 2359103744 2359234816 (235904587294677 / 100000)
      (58979405095161 / 25000) := by
  exact
    packedTile65536 2359103744 2359234816 14 6039 48570 31 _ _ (2158153 / 100000) (539539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2359234816 :
    ThetaLowerSegment 2359234816 2359365888 (58979405095161 / 25000) (117965260927573 / 50000) := by
  exact
    packedTile65536 2359234816 2359365888 14 5978 48571 31 _ _ (2158159 / 100000) (1079081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2359365888 :
    ThetaLowerSegment 2359365888 2359496960 (117965260927573 / 50000)
      (117971911309939 / 50000) := by
  exact
    packedTile65536 2359365888 2359496960 14 6163 48573 31 _ _ (539541 / 25000) (2158167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2359496960 :
    ThetaLowerSegment 2359496960 2359628032 (117971911309939 / 50000)
      (117978454881379 / 50000) := by
  exact
    packedTile65536 2359496960 2359628032 14 6064 48574 31 _ _ (215817 / 10000) (2158173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2359628032 :
    ThetaLowerSegment 2359628032 2359759104 (117978454881379 / 50000)
      (235970115635583 / 100000) := by
  exact
    packedTile65536 2359628032 2359759104 14 6119 48576 31 _ _ (86327 / 4000) (1079089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2359759104 :
    ThetaLowerSegment 2359759104 2359890176 (235970115635583 / 100000)
      (235983289172407 / 100000) := by
  exact
    packedTile65536 2359759104 2359890176 14 6104 48577 31 _ _ (2158181 / 100000) (269773 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2359890176 :
    ThetaLowerSegment 2359890176 2360021248 (235983289172407 / 100000)
      (235996195130667 / 100000) := by
  exact
    packedTile65536 2359890176 2360021248 14 5980 48578 31 _ _ (2158187 / 100000) (215819 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360021248 :
    ThetaLowerSegment 2360021248 2360152320 (235996195130667 / 100000)
      (236009383841979 / 100000) := by
  exact
    packedTile65536 2360021248 2360152320 14 6111 48580 31 _ _ (134887 / 6250) (431639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360152320 :
    ThetaLowerSegment 2360152320 2360283392 (236009383841979 / 100000)
      (47204480418463 / 20000) := by
  exact
    packedTile65536 2360152320 2360283392 14 6032 48581 31 _ _ (1079099 / 50000) (2158201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360283392 :
    ThetaLowerSegment 2360283392 2360414464 (47204480418463 / 20000)
      (236035420372811 / 100000) := by
  exact
    packedTile65536 2360283392 2360414464 14 6032 48582 31 _ _ (2158203 / 100000) (1079103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360414464 :
    ThetaLowerSegment 2360414464 2360545536 (236035420372811 / 100000)
      (236048594080547 / 100000) := by
  exact
    packedTile65536 2360414464 2360545536 14 6104 48584 31 _ _ (2158209 / 100000) (539553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360545536 :
    ThetaLowerSegment 2360545536 2360676608 (236048594080547 / 100000)
      (236061485092769 / 100000) := by
  exact
    packedTile65536 2360545536 2360676608 14 5973 48585 31 _ _ (1079107 / 50000) (2158217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360676608 :
    ThetaLowerSegment 2360676608 2360807680 (236061485092769 / 100000)
      (236074574697069 / 100000) := by
  exact
    packedTile65536 2360676608 2360807680 14 6065 48586 31 _ _ (107911 / 5000) (2158223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360807680 :
    ThetaLowerSegment 2360807680 2360938752 (236074574697069 / 100000)
      (236087485199019 / 100000) := by
  exact
    packedTile65536 2360807680 2360938752 14 5982 48588 31 _ _ (86329 / 4000) (539557 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360938752 :
    ThetaLowerSegment 2360938752 2361069824 (236087485199019 / 100000)
      (118050343549023 / 50000) := by
  exact
    packedTile65536 2360938752 2361069824 14 6117 48589 31 _ _ (2158231 / 100000) (1079117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2361069824 :
    ThetaLowerSegment 2361069824 2361200896 (118050343549023 / 50000)
      (236113746590133 / 100000) := by
  exact
    packedTile65536 2361069824 2361200896 14 6051 48590 31 _ _ (2158237 / 100000) (13489 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2361200896 :
    ThetaLowerSegment 2361200896 2361331968 (236113746590133 / 100000)
      (236126797479507 / 100000) := by
  exact
    packedTile65536 2361200896 2361331968 14 6047 48592 31 _ _ (1079121 / 50000) (431649 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2361331968 :
    ThetaLowerSegment 2361331968 2361463040 (236126797479507 / 100000)
      (47227990831863 / 20000) := by
  exact
    packedTile65536 2361331968 2361463040 14 6096 48593 31 _ _ (269781 / 12500) (2158251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2361463040 :
    ThetaLowerSegment 2361463040 2361594112 (47227990831863 / 20000)
      (236153128135627 / 100000) := by
  exact
    packedTile65536 2361463040 2361594112 14 6104 48594 31 _ _ (2158253 / 100000) (134891 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2361594112 :
    ThetaLowerSegment 2361594112 2361725184 (236153128135627 / 100000)
      (118083070139569 / 50000) := by
  exact
    packedTile65536 2361594112 2361725184 14 6029 48596 31 _ _ (2158259 / 100000) (1079131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2361725184 :
    ThetaLowerSegment 2361725184 2361856256 (118083070139569 / 50000)
      (118089687376993 / 50000) := by
  exact
    packedTile65536 2361725184 2361856256 14 6132 48597 31 _ _ (269783 / 12500) (2158267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2361856256 :
    ThetaLowerSegment 2361856256 2361987328 (118089687376993 / 50000) (29524039737397 / 12500) := by
  exact
    packedTile65536 2361856256 2361987328 14 5997 48598 31 _ _ (215827 / 10000) (2158273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2361987328 :
    ThetaLowerSegment 2361987328 2362118400 (29524039737397 / 12500) (29525688659497 / 12500) := by
  exact
    packedTile65536 2361987328 2362118400 14 6112 48600 31 _ _ (86331 / 4000) (1079139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2362118400 :
    ThetaLowerSegment 2362118400 2362249472 (29525688659497 / 12500) (29527320319933 / 12500) := by
  exact
    packedTile65536 2362118400 2362249472 14 6048 48601 31 _ _ (2158281 / 100000) (539571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2362249472 :
    ThetaLowerSegment 2362249472 2362380544 (29527320319933 / 12500) (5905790396981 / 2500) := by
  exact
    packedTile65536 2362249472 2362380544 14 6048 48602 31 _ _ (2158287 / 100000) (215829 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2362380544 :
    ThetaLowerSegment 2362380544 2362511616 (5905790396981 / 2500) (29530606315723 / 12500) := by
  exact
    packedTile65536 2362380544 2362511616 14 6132 48604 31 _ _ (539573 / 25000) (431659 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2362511616 :
    ThetaLowerSegment 2362511616 2362642688 (29530606315723 / 12500) (14766129246421 / 6250) := by
  exact
    packedTile65536 2362511616 2362642688 14 6124 48605 31 _ _ (1079149 / 50000) (2158301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2362642688 :
    ThetaLowerSegment 2362642688 2362773760 (14766129246421 / 6250) (23627122927443 / 10000) := by
  exact
    packedTile65536 2362642688 2362773760 14 6098 48607 31 _ _ (2158303 / 100000) (1079153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2362773760 :
    ThetaLowerSegment 2362773760 2362904832 (23627122927443 / 10000) (47256872516939 / 20000) := by
  exact
    packedTile65536 2362773760 2362904832 14 6085 48608 31 _ _ (2158309 / 100000) (269789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2362904832 :
    ThetaLowerSegment 2362904832 2363035904 (47256872516939 / 20000) (47259499185077 / 20000) := by
  exact
    packedTile65536 2362904832 2363035904 14 6085 48609 31 _ _ (1079157 / 50000) (2158317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2363035904 :
    ThetaLowerSegment 2363035904 2363166976 (47259499185077 / 20000) (1890483687629 / 800) := by
  exact
    packedTile65536 2363035904 2363166976 14 6007 48611 31 _ _ (26979 / 1250) (2158323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2363166976 :
    ThetaLowerSegment 2363166976 2363298048 (1890483687629 / 800) (1890589013889 / 800) := by
  exact
    packedTile65536 2363166976 2363298048 14 6100 48612 31 _ _ (86333 / 4000) (269791 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2363298048 :
    ThetaLowerSegment 2363298048 2363429120 (1890589013889 / 800) (47267397361003 / 20000) := by
  exact
    packedTile65536 2363298048 2363429120 14 6190 48613 31 _ _ (2158331 / 100000) (1079167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2363429120 :
    ThetaLowerSegment 2363429120 2363560192 (47267397361003 / 20000) (47269961464171 / 20000) := by
  exact
    packedTile65536 2363429120 2363560192 14 5940 48615 31 _ _ (67448 / 3125) (2158339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2363560192 :
    ThetaLowerSegment 2363560192 2363691264 (47269961464171 / 20000)
      (236363012057211 / 100000) := by
  exact
    packedTile65536 2363560192 2363691264 14 6118 48616 31 _ _ (1079171 / 50000) (431669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2363691264 :
    ThetaLowerSegment 2363691264 2363822336 (236363012057211 / 100000)
      (47275234732663 / 20000) := by
  exact
    packedTile65536 2363691264 2363822336 14 6098 48617 31 _ _ (539587 / 25000) (2158351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2363822336 :
    ThetaLowerSegment 2363822336 2363953408 (47275234732663 / 20000) (23638928565779 / 10000) := by
  exact
    packedTile65536 2363822336 2363953408 14 6075 48619 31 _ _ (2158353 / 100000) (539589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2363953408 :
    ThetaLowerSegment 2363953408 2364084480 (23638928565779 / 10000)
      (236402272503893 / 100000) := by
  exact
    packedTile65536 2363953408 2364084480 14 6017 48620 31 _ _ (2158359 / 100000) (1079181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2364084480 :
    ThetaLowerSegment 2364084480 2364215552 (236402272503893 / 100000)
      (47283067416237 / 20000) := by
  exact
    packedTile65536 2364084480 2364215552 14 6053 48621 31 _ _ (539591 / 25000) (2158367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2364215552 :
    ThetaLowerSegment 2364215552 2364346624 (47283067416237 / 20000) (47285648395083 / 20000) := by
  exact
    packedTile65536 2364215552 2364346624 14 5979 48623 31 _ _ (215837 / 10000) (2158373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2364346624 :
    ThetaLowerSegment 2364346624 2364477696 (47285648395083 / 20000) (23644134978679 / 10000) := by
  exact
    packedTile65536 2364346624 2364477696 14 6073 48624 31 _ _ (17267 / 800) (1079189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2364477696 :
    ThetaLowerSegment 2364477696 2364608768 (23644134978679 / 10000) (118227249321921 / 50000) := by
  exact
    packedTile65536 2364477696 2364608768 14 6092 48625 31 _ _ (2158381 / 100000) (134899 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2364608768 :
    ThetaLowerSegment 2364608768 2364739840 (118227249321921 / 50000)
      (118233778439571 / 50000) := by
  exact
    packedTile65536 2364608768 2364739840 14 6050 48627 31 _ _ (1079193 / 50000) (2158389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2364739840 :
    ThetaLowerSegment 2364739840 2364870912 (118233778439571 / 50000) (23648078566371 / 10000) := by
  exact
    packedTile65536 2364739840 2364870912 14 6129 48628 31 _ _ (269799 / 12500) (431679 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2364870912 :
    ThetaLowerSegment 2364870912 2365001984 (23648078566371 / 10000) (59123480416963 / 25000) := by
  exact
    packedTile65536 2364870912 2365001984 14 6086 48629 31 _ _ (2158397 / 100000) (2698 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2365001984 :
    ThetaLowerSegment 2365001984 2365133056 (59123480416963 / 25000) (118253459785359 / 50000) := by
  exact
    packedTile65536 2365001984 2365133056 14 6022 48631 31 _ _ (2158403 / 100000) (1079203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2365133056 :
    ThetaLowerSegment 2365133056 2365264128 (118253459785359 / 50000)
      (236520031905393 / 100000) := by
  exact
    packedTile65536 2365133056 2365264128 14 6075 48632 31 _ _ (2158409 / 100000) (539603 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2365264128 :
    ThetaLowerSegment 2365264128 2365395200 (236520031905393 / 100000)
      (236533314785149 / 100000) := by
  exact
    packedTile65536 2365264128 2365395200 14 6154 48633 31 _ _ (1079207 / 50000) (2158417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2365395200 :
    ThetaLowerSegment 2365395200 2365526272 (236533314785149 / 100000)
      (236546284730929 / 100000) := by
  exact
    packedTile65536 2365395200 2365526272 14 6009 48635 31 _ _ (107921 / 5000) (2158423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2365526272 :
    ThetaLowerSegment 2365526272 2365657344 (236546284730929 / 100000)
      (236559399321229 / 100000) := by
  exact
    packedTile65536 2365526272 2365657344 14 6076 48636 31 _ _ (86337 / 4000) (539607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2365657344 :
    ThetaLowerSegment 2365657344 2365788416 (236559399321229 / 100000)
      (118286156606951 / 50000) := by
  exact
    packedTile65536 2365657344 2365788416 14 5983 48638 31 _ _ (2158431 / 100000) (1079217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2365788416 :
    ThetaLowerSegment 2365788416 2365919488 (118286156606951 / 50000)
      (118292758183457 / 50000) := by
  exact
    packedTile65536 2365788416 2365919488 14 6117 48639 31 _ _ (539609 / 25000) (2158439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2365919488 :
    ThetaLowerSegment 2365919488 2366050560 (118292758183457 / 50000)
      (118299300421159 / 50000) := by
  exact
    packedTile65536 2365919488 2366050560 14 6062 48640 31 _ _ (1079221 / 50000) (431689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2366050560 :
    ThetaLowerSegment 2366050560 2366181632 (118299300421159 / 50000)
      (118305831881781 / 50000) := by
  exact
    packedTile65536 2366050560 2366181632 14 6052 48642 31 _ _ (2158447 / 100000) (43169 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2366181632 :
    ThetaLowerSegment 2366181632 2366312704 (118305831881781 / 50000)
      (236624806583879 / 100000) := by
  exact
    packedTile65536 2366181632 2366312704 14 6089 48643 31 _ _ (2158453 / 100000) (269807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2366312704 :
    ThetaLowerSegment 2366312704 2366443776 (236624806583879 / 100000)
      (236637904107023 / 100000) := by
  exact
    packedTile65536 2366312704 2366443776 14 6068 48644 31 _ _ (1079229 / 50000) (2158461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2366443776 :
    ThetaLowerSegment 2366443776 2366574848 (236637904107023 / 100000)
      (236651094480527 / 100000) := by
  exact
    packedTile65536 2366443776 2366574848 14 6111 48646 31 _ _ (67452 / 3125) (2158467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2366574848 :
    ThetaLowerSegment 2366574848 2366705920 (236651094480527 / 100000)
      (59166029131001 / 25000) := by
  exact
    packedTile65536 2366574848 2366705920 14 6033 48647 31 _ _ (2158469 / 100000) (269809 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2366705920 :
    ThetaLowerSegment 2366705920 2366836992 (59166029131001 / 25000) (118338604916677 / 50000) := by
  exact
    packedTile65536 2366705920 2366836992 14 6066 48648 31 _ _ (86339 / 4000) (1079239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2366836992 :
    ThetaLowerSegment 2366836992 2366968064 (118338604916677 / 50000) (47338075745187 / 20000) := by
  exact
    packedTile65536 2366836992 2366968064 14 6101 48650 31 _ _ (2158481 / 100000) (539621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2366968064 :
    ThetaLowerSegment 2366968064 2367099136 (47338075745187 / 20000)
      (236703709535471 / 100000) := by
  exact
    packedTile65536 2366968064 2367099136 14 6176 48651 31 _ _ (1079243 / 50000) (2158489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2367099136 :
    ThetaLowerSegment 2367099136 2367230208 (236703709535471 / 100000)
      (236716787838499 / 100000) := by
  exact
    packedTile65536 2367099136 2367230208 14 6059 48652 31 _ _ (539623 / 25000) (431699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2367230208 :
    ThetaLowerSegment 2367230208 2367361280 (236716787838499 / 100000)
      (236729920134247 / 100000) := by
  exact
    packedTile65536 2367230208 2367361280 14 6084 48654 31 _ _ (2158497 / 100000) (4317 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2367361280 :
    ThetaLowerSegment 2367361280 2367492352 (236729920134247 / 100000)
      (118371514361483 / 50000) := by
  exact
    packedTile65536 2367361280 2367492352 14 6073 48655 31 _ _ (2158503 / 100000) (1079253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2367492352 :
    ThetaLowerSegment 2367492352 2367623424 (118371514361483 / 50000)
      (118378097810883 / 50000) := by
  exact
    packedTile65536 2367492352 2367623424 14 6100 48656 31 _ _ (539627 / 25000) (2158511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2367623424 :
    ThetaLowerSegment 2367623424 2367754496 (118378097810883 / 50000) (947077502033 / 400) := by
  exact
    packedTile65536 2367623424 2367754496 14 6106 48658 31 _ _ (1079257 / 50000) (2158517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2367754496 :
    ThetaLowerSegment 2367754496 2367885568 (947077502033 / 400) (47356510653349 / 20000) := by
  exact
    packedTile65536 2367754496 2367885568 14 6105 48659 31 _ _ (2158519 / 100000) (1079261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2367885568 :
    ThetaLowerSegment 2367885568 2368016640 (47356510653349 / 20000) (47359144053849 / 20000) := by
  exact
    packedTile65536 2367885568 2368016640 14 6100 48660 31 _ _ (86341 / 4000) (67454 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368016640 :
    ThetaLowerSegment 2368016640 2368147712 (47359144053849 / 20000) (47361776597037 / 20000) := by
  exact
    packedTile65536 2368016640 2368147712 14 6098 48662 31 _ _ (215853 / 10000) (2158533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368147712 :
    ThetaLowerSegment 2368147712 2368278784 (47361776597037 / 20000)
      (236822063006001 / 100000) := by
  exact
    packedTile65536 2368147712 2368278784 14 6106 48663 31 _ _ (269817 / 12500) (2158539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368278784 :
    ThetaLowerSegment 2368278784 2368409856 (236822063006001 / 100000)
      (236835091959477 / 100000) := by
  exact
    packedTile65536 2368278784 2368409856 14 6036 48664 31 _ _ (2158541 / 100000) (134909 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368409856 :
    ThetaLowerSegment 2368409856 2368540928 (236835091959477 / 100000)
      (59212056679493 / 25000) := by
  exact
    packedTile65536 2368409856 2368540928 14 6085 48666 31 _ _ (2158547 / 100000) (43171 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368540928 :
    ThetaLowerSegment 2368540928 2368672000 (59212056679493 / 25000) (11843069586331 / 5000) := by
  exact
    packedTile65536 2368540928 2368672000 14 6099 48667 31 _ _ (269819 / 12500) (431711 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368672000 :
    ThetaLowerSegment 2368672000 2368803072 (11843069586331 / 5000) (59218648366837 / 25000) := by
  exact
    packedTile65536 2368672000 2368803072 14 6116 48669 31 _ _ (1079279 / 50000) (2158561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368803072 :
    ThetaLowerSegment 2368803072 2368934144 (59218648366837 / 25000) (59221927225553 / 25000) := by
  exact
    packedTile65536 2368803072 2368934144 14 6076 48670 31 _ _ (539641 / 25000) (2158567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368934144 :
    ThetaLowerSegment 2368934144 2369065216 (59221927225553 / 25000)
      (236900636571953 / 100000) := by
  exact
    packedTile65536 2368934144 2369065216 14 5989 48671 31 _ _ (2158569 / 100000) (539643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2369065216 :
    ThetaLowerSegment 2369065216 2369196288 (236900636571953 / 100000)
      (59228468778107 / 25000) := by
  exact
    packedTile65536 2369065216 2369196288 14 6133 48673 31 _ _ (86343 / 4000) (1079289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2369196288 :
    ThetaLowerSegment 2369196288 2369327360 (59228468778107 / 25000) (59231728233907 / 25000) := by
  exact
    packedTile65536 2369196288 2369327360 14 6040 48674 31 _ _ (107929 / 5000) (2158583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2369327360 :
    ThetaLowerSegment 2369327360 2369458432 (59231728233907 / 25000) (118470017489961 / 50000) := by
  exact
    packedTile65536 2369327360 2369458432 14 6079 48675 31 _ _ (1079293 / 50000) (2158589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2369458432 :
    ThetaLowerSegment 2369458432 2369589504 (118470017489961 / 50000)
      (236953083662517 / 100000) := by
  exact
    packedTile65536 2369458432 2369589504 14 6045 48677 31 _ _ (2158591 / 100000) (1079297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2369589504 :
    ThetaLowerSegment 2369589504 2369720576 (236953083662517 / 100000)
      (236966272690187 / 100000) := by
  exact
    packedTile65536 2369589504 2369720576 14 6110 48678 31 _ _ (2158597 / 100000) (10793 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2369720576 :
    ThetaLowerSegment 2369720576 2369851648 (236966272690187 / 100000)
      (47395868173339 / 20000) := by
  exact
    packedTile65536 2369720576 2369851648 14 6054 48679 31 _ _ (1079301 / 50000) (431721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2369851648 :
    ThetaLowerSegment 2369851648 2369982720 (47395868173339 / 20000) (47398493040667 / 20000) := by
  exact
    packedTile65536 2369851648 2369982720 14 6080 48681 31 _ _ (134913 / 6250) (2158611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2369982720 :
    ThetaLowerSegment 2369982720 2370113792 (47398493040667 / 20000) (59251402249473 / 25000) := by
  exact
    packedTile65536 2369982720 2370113792 14 6089 48682 31 _ _ (2158613 / 100000) (269827 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2370113792 :
    ThetaLowerSegment 2370113792 2370244864 (59251402249473 / 25000)
      (237018718291079 / 100000) := by
  exact
    packedTile65536 2370113792 2370244864 14 6073 48683 31 _ _ (2158619 / 100000) (1079311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2370244864 :
    ThetaLowerSegment 2370244864 2370375936 (237018718291079 / 100000) (9481275781279 / 4000) := by
  exact
    packedTile65536 2370244864 2370375936 14 6104 48685 31 _ _ (67457 / 3125) (2158627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2370375936 :
    ThetaLowerSegment 2370375936 2370507008 (9481275781279 / 4000) (47409020637789 / 20000) := by
  exact
    packedTile65536 2370375936 2370507008 14 6119 48686 31 _ _ (215863 / 10000) (2158633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2370507008 :
    ThetaLowerSegment 2370507008 2370638080 (47409020637789 / 20000) (2370582989247 / 1000) := by
  exact
    packedTile65536 2370507008 2370638080 14 6113 48687 31 _ _ (431727 / 20000) (1079319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2370638080 :
    ThetaLowerSegment 2370638080 2370769152 (2370582989247 / 1000) (47414209139961 / 20000) := by
  exact
    packedTile65536 2370638080 2370769152 14 5905 48689 31 _ _ (2158641 / 100000) (539661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2370769152 :
    ThetaLowerSegment 2370769152 2370900224 (47414209139961 / 20000)
      (237084252302151 / 100000) := by
  exact
    packedTile65536 2370769152 2370900224 14 6118 48690 31 _ _ (2158647 / 100000) (43173 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2370900224 :
    ThetaLowerSegment 2370900224 2371031296 (237084252302151 / 100000)
      (237097249545843 / 100000) := by
  exact
    packedTile65536 2370900224 2371031296 14 6021 48691 31 _ _ (539663 / 25000) (431731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2371031296 :
    ThetaLowerSegment 2371031296 2371162368 (237097249545843 / 100000)
      (237110428152933 / 100000) := by
  exact
    packedTile65536 2371031296 2371162368 14 6105 48693 31 _ _ (1079329 / 50000) (2158661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2371162368 :
    ThetaLowerSegment 2371162368 2371293440 (237110428152933 / 100000)
      (29640458404139 / 12500) := by
  exact
    packedTile65536 2371162368 2371293440 14 6133 48694 31 _ _ (2158663 / 100000) (1079333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2371293440 :
    ThetaLowerSegment 2371293440 2371424512 (29640458404139 / 12500)
      (237136651627147 / 100000) := by
  exact
    packedTile65536 2371293440 2371424512 14 6015 48695 31 _ _ (2158669 / 100000) (134917 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2371424512 :
    ThetaLowerSegment 2371424512 2371555584 (237136651627147 / 100000)
      (47429949660461 / 20000) := by
  exact
    packedTile65536 2371424512 2371555584 14 6067 48697 31 _ _ (1079337 / 50000) (2158677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2371555584 :
    ThetaLowerSegment 2371555584 2371686656 (47429949660461 / 20000) (9486504906793 / 4000) := by
  exact
    packedTile65536 2371555584 2371686656 14 5964 48698 31 _ _ (53967 / 2500) (2158683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2371686656 :
    ThetaLowerSegment 2371686656 2371817728 (9486504906793 / 4000) (23717570645961 / 10000) := by
  exact
    packedTile65536 2371686656 2371817728 14 6061 48699 31 _ _ (431737 / 20000) (67459 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2371817728 :
    ThetaLowerSegment 2371817728 2371948800 (23717570645961 / 10000) (118594424285209 / 50000) := by
  exact
    packedTile65536 2371817728 2371948800 14 6088 48701 31 _ _ (2158691 / 100000) (1079347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2371948800 :
    ThetaLowerSegment 2371948800 2372079872 (118594424285209 / 50000)
      (118601046085189 / 50000) := by
  exact
    packedTile65536 2371948800 2372079872 14 6135 48702 31 _ _ (269837 / 12500) (2158699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372079872 :
    ThetaLowerSegment 2372079872 2372210944 (118601046085189 / 50000)
      (118607543778209 / 50000) := by
  exact
    packedTile65536 2372079872 2372210944 14 6020 48704 31 _ _ (1079351 / 50000) (431741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372210944 :
    ThetaLowerSegment 2372210944 2372342016 (118607543778209 / 50000) (59307026139907 / 25000) := by
  exact
    packedTile65536 2372210944 2372342016 14 6030 48705 31 _ _ (2158707 / 100000) (215871 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372342016 :
    ThetaLowerSegment 2372342016 2372473088 (59307026139907 / 25000)
      (237241395755569 / 100000) := by
  exact
    packedTile65536 2372342016 2372473088 14 6157 48706 31 _ _ (2158713 / 100000) (539679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372473088 :
    ThetaLowerSegment 2372473088 2372604160 (237241395755569 / 100000)
      (237254391237929 / 100000) := by
  exact
    packedTile65536 2372473088 2372604160 14 6020 48708 31 _ _ (1079359 / 50000) (2158721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372604160 :
    ThetaLowerSegment 2372604160 2372735232 (237254391237929 / 100000)
      (237267626374773 / 100000) := by
  exact
    packedTile65536 2372604160 2372735232 14 6131 48709 31 _ _ (539681 / 25000) (2158727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372735232 :
    ThetaLowerSegment 2372735232 2372866304 (237267626374773 / 100000)
      (237280924145413 / 100000) := by
  exact
    packedTile65536 2372735232 2372866304 14 6160 48710 31 _ _ (2158729 / 100000) (539683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372866304 :
    ThetaLowerSegment 2372866304 2372997376 (237280924145413 / 100000)
      (118646967420629 / 50000) := by
  exact
    packedTile65536 2372866304 2372997376 14 6027 48712 31 _ _ (431747 / 20000) (1079369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372997376 :
    ThetaLowerSegment 2372997376 2373128448 (118646967420629 / 50000)
      (118653515958419 / 50000) := by
  exact
    packedTile65536 2372997376 2373128448 14 6067 48713 31 _ _ (107937 / 5000) (2158743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2373128448 :
    ThetaLowerSegment 2373128448 2373259520 (118653515958419 / 50000)
      (118660054800053 / 50000) := by
  exact
    packedTile65536 2373128448 2373259520 14 6058 48714 31 _ _ (1079373 / 50000) (2158749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2373259520 :
    ThetaLowerSegment 2373259520 2373390592 (118660054800053 / 50000)
      (118666591501109 / 50000) := by
  exact
    packedTile65536 2373259520 2373390592 14 6056 48716 31 _ _ (67461 / 3125) (431751 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2373390592 :
    ThetaLowerSegment 2373390592 2373521664 (118666591501109 / 50000)
      (237346103162863 / 100000) := by
  exact
    packedTile65536 2373390592 2373521664 14 5985 48717 31 _ _ (2158757 / 100000) (53969 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2373521664 :
    ThetaLowerSegment 2373521664 2373652736 (237346103162863 / 100000)
      (118679675745697 / 50000) := by
  exact
    packedTile65536 2373521664 2373652736 14 6137 48718 31 _ _ (2158763 / 100000) (1079383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2373652736 :
    ThetaLowerSegment 2373652736 2373783808 (118679675745697 / 50000)
      (118686203860129 / 50000) := by
  exact
    packedTile65536 2373652736 2373783808 14 6048 48720 31 _ _ (134923 / 6250) (2158771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2373783808 :
    ThetaLowerSegment 2373783808 2373914880 (118686203860129 / 50000) (1186927158019 / 500) := by
  exact
    packedTile65536 2373783808 2373914880 14 6033 48721 31 _ _ (1079387 / 50000) (2158777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2373914880 :
    ThetaLowerSegment 2373914880 2374045952 (1186927158019 / 500) (237398839780169 / 100000) := by
  exact
    packedTile65536 2373914880 2374045952 14 6211 48722 31 _ _ (2158779 / 100000) (1079391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2374045952 :
    ThetaLowerSegment 2374045952 2374177024 (237398839780169 / 100000)
      (118705880054197 / 50000) := by
  exact
    packedTile65536 2374045952 2374177024 14 5985 48724 31 _ _ (431757 / 20000) (539697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2374177024 :
    ThetaLowerSegment 2374177024 2374308096 (118705880054197 / 50000)
      (118712434140637 / 50000) := by
  exact
    packedTile65536 2374177024 2374308096 14 6072 48725 31 _ _ (215879 / 10000) (2158793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2374308096 :
    ThetaLowerSegment 2374308096 2374439168 (118712434140637 / 50000) (23743807147761 / 10000) := by
  exact
    packedTile65536 2374308096 2374439168 14 6116 48726 31 _ _ (539699 / 25000) (2158799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2374439168 :
    ThetaLowerSegment 2374439168 2374570240 (23743807147761 / 10000)
      (237451220734501 / 100000) := by
  exact
    packedTile65536 2374439168 2374570240 14 6091 48728 31 _ _ (2158801 / 100000) (539701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2374570240 :
    ThetaLowerSegment 2374570240 2374701312 (237451220734501 / 100000)
      (29683040316773 / 12500) := by
  exact
    packedTile65536 2374570240 2374701312 14 6069 48729 31 _ _ (2158807 / 100000) (215881 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2374701312 :
    ThetaLowerSegment 2374701312 2374832384 (29683040316773 / 12500) (11873874888191 / 5000) := by
  exact
    packedTile65536 2374701312 2374832384 14 6103 48730 31 _ _ (539703 / 25000) (431763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2374832384 :
    ThetaLowerSegment 2374832384 2374963456 (11873874888191 / 5000) (59372647209043 / 25000) := by
  exact
    packedTile65536 2374832384 2374963456 14 6064 48732 31 _ _ (1079409 / 50000) (2158821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2374963456 :
    ThetaLowerSegment 2374963456 2375094528 (59372647209043 / 25000)
      (237503582791809 / 100000) := by
  exact
    packedTile65536 2374963456 2375094528 14 6019 48733 31 _ _ (2158823 / 100000) (1079413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2375094528 :
    ThetaLowerSegment 2375094528 2375225600 (237503582791809 / 100000) (9500666093703 / 4000) := by
  exact
    packedTile65536 2375094528 2375225600 14 6054 48734 31 _ _ (2158829 / 100000) (134927 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2375225600 :
    ThetaLowerSegment 2375225600 2375356672 (9500666093703 / 4000) (237529834182979 / 100000) := by
  exact
    packedTile65536 2375225600 2375356672 14 6106 48736 31 _ _ (1079417 / 50000) (2158837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2375356672 :
    ThetaLowerSegment 2375356672 2375487744 (237529834182979 / 100000)
      (237543024695379 / 100000) := by
  exact
    packedTile65536 2375356672 2375487744 14 6110 48737 31 _ _ (53971 / 2500) (2158843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2375487744 :
    ThetaLowerSegment 2375487744 2375618816 (237543024695379 / 100000) (14847246586419 / 6250) := by
  exact
    packedTile65536 2375487744 2375618816 14 5985 48738 31 _ _ (431769 / 20000) (67464 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2375618816 :
    ThetaLowerSegment 2375618816 2375749888 (14847246586419 / 6250) (237568935189171 / 100000) := by
  exact
    packedTile65536 2375618816 2375749888 14 6017 48740 31 _ _ (2158851 / 100000) (1079427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2375749888 :
    ThetaLowerSegment 2375749888 2375880960 (237568935189171 / 100000)
      (237582045921659 / 100000) := by
  exact
    packedTile65536 2375749888 2375880960 14 6073 48741 31 _ _ (269857 / 12500) (2158859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2375880960 :
    ThetaLowerSegment 2375880960 2376012032 (237582045921659 / 100000)
      (237595227933031 / 100000) := by
  exact
    packedTile65536 2375880960 2376012032 14 6106 48743 31 _ _ (1079431 / 50000) (431773 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376012032 :
    ThetaLowerSegment 2376012032 2376143104 (237595227933031 / 100000)
      (118804234132171 / 50000) := by
  exact
    packedTile65536 2376012032 2376143104 14 6133 48744 31 _ _ (2158867 / 100000) (215887 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376143104 :
    ThetaLowerSegment 2376143104 2376274176 (118804234132171 / 50000)
      (237621626595277 / 100000) := by
  exact
    packedTile65536 2376143104 2376274176 14 6095 48745 31 _ _ (2158873 / 100000) (539719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376274176 :
    ThetaLowerSegment 2376274176 2376405248 (237621626595277 / 100000)
      (237634724508103 / 100000) := by
  exact
    packedTile65536 2376274176 2376405248 14 6067 48747 31 _ _ (1079439 / 50000) (2158881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376405248 :
    ThetaLowerSegment 2376405248 2376536320 (237634724508103 / 100000)
      (237647686447639 / 100000) := by
  exact
    packedTile65536 2376405248 2376536320 14 6004 48748 31 _ _ (539721 / 25000) (2158887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376536320 :
    ThetaLowerSegment 2376536320 2376667392 (237647686447639 / 100000)
      (118830396531379 / 50000) := by
  exact
    packedTile65536 2376536320 2376667392 14 6071 48749 31 _ _ (2158889 / 100000) (539723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376667392 :
    ThetaLowerSegment 2376667392 2376798464 (118830396531379 / 50000)
      (118836955254389 / 50000) := by
  exact
    packedTile65536 2376667392 2376798464 14 6076 48751 31 _ _ (431779 / 20000) (1079449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376798464 :
    ThetaLowerSegment 2376798464 2376929536 (118836955254389 / 50000) (47537440572447 / 20000) := by
  exact
    packedTile65536 2376798464 2376929536 14 6157 48752 31 _ _ (2158901 / 100000) (269863 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376929536 :
    ThetaLowerSegment 2376929536 2377060608 (47537440572447 / 20000) (47540052848707 / 20000) := by
  exact
    packedTile65536 2376929536 2377060608 14 6050 48753 31 _ _ (1079453 / 50000) (2158909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377060608 :
    ThetaLowerSegment 2377060608 2377191680 (47540052848707 / 20000)
      (237713375316111 / 100000) := by
  exact
    packedTile65536 2377060608 2377191680 14 6073 48755 31 _ _ (67466 / 3125) (431783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377191680 :
    ThetaLowerSegment 2377191680 2377322752 (237713375316111 / 100000) (1485790594092 / 625) := by
  exact
    packedTile65536 2377191680 2377322752 14 6077 48756 31 _ _ (2158917 / 100000) (53973 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377322752 :
    ThetaLowerSegment 2377322752 2377339136 (1485790594092 / 625) (237728094816663 / 100000) := by
  exact
    packedTile65536 2377322752 2377339136 11 741 48757 31 _ _ (2158923 / 100000) (1079463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377339136 :
    ThetaLowerSegment 2377339136 2377341184 (237728094816663 / 100000)
      (237728310708963 / 100000) := by
  exact
    packedTile65536 2377339136 2377341184 8 100 48757 31 _ _ (2158923 / 100000) (1079463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2345341184_2377341184 :
    ThetaLowerSegment 2345341184 2377341184 (11726432528937 / 5000) (237728310708963 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2345341184 cell2345472256)
                  (ThetaLowerSegment.join cell2345603328 cell2345734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2345865472 cell2345996544)
                  (ThetaLowerSegment.join cell2346127616 cell2346258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2346389760 cell2346520832)
                  (ThetaLowerSegment.join cell2346651904 cell2346782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2346914048 cell2347045120)
                  (ThetaLowerSegment.join cell2347176192 cell2347307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2347438336 cell2347569408)
                  (ThetaLowerSegment.join cell2347700480 cell2347831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2347962624 cell2348093696)
                  (ThetaLowerSegment.join cell2348224768 cell2348355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2348486912 cell2348617984)
                  (ThetaLowerSegment.join cell2348749056 cell2348880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2349011200 cell2349142272)
                  (ThetaLowerSegment.join cell2349273344 cell2349404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2349535488 cell2349666560)
                  (ThetaLowerSegment.join cell2349797632 cell2349928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2350059776 cell2350190848)
                  (ThetaLowerSegment.join cell2350321920 cell2350452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2350584064 cell2350715136)
                  (ThetaLowerSegment.join cell2350846208 cell2350977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2351108352 cell2351239424)
                  (ThetaLowerSegment.join cell2351370496 cell2351501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2351632640 cell2351763712)
                  (ThetaLowerSegment.join cell2351894784 cell2352025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2352156928 cell2352288000)
                  (ThetaLowerSegment.join cell2352419072 cell2352550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2352681216 cell2352812288)
                  (ThetaLowerSegment.join cell2352943360 cell2353074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2353205504 cell2353336576)
                  (ThetaLowerSegment.join cell2353467648 cell2353598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2353729792 cell2353860864)
                  (ThetaLowerSegment.join cell2353991936 cell2354123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2354254080 cell2354385152)
                  (ThetaLowerSegment.join cell2354516224 cell2354647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2354778368 cell2354909440)
                  (ThetaLowerSegment.join cell2355040512 cell2355171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2355302656 cell2355433728)
                  (ThetaLowerSegment.join cell2355564800 cell2355695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2355826944 cell2355958016)
                  (ThetaLowerSegment.join cell2356089088 cell2356220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2356351232 cell2356482304)
                  (ThetaLowerSegment.join cell2356613376 cell2356744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2356875520 cell2357006592)
                  (ThetaLowerSegment.join cell2357137664 cell2357268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2357399808 cell2357530880)
                  (ThetaLowerSegment.join cell2357661952 cell2357793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2357924096 cell2358055168)
                  (ThetaLowerSegment.join cell2358186240 cell2358317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2358448384 cell2358579456)
                  (ThetaLowerSegment.join cell2358710528 cell2358841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2358972672 cell2359103744)
                  (ThetaLowerSegment.join cell2359234816 cell2359365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2359496960 cell2359628032)
                  (ThetaLowerSegment.join cell2359759104 cell2359890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2360021248 cell2360152320)
                  (ThetaLowerSegment.join cell2360283392 cell2360414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2360545536 cell2360676608)
                  (ThetaLowerSegment.join cell2360807680 cell2360938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2361069824 cell2361200896)
                  (ThetaLowerSegment.join cell2361331968 cell2361463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2361594112 cell2361725184)
                  (ThetaLowerSegment.join cell2361856256 cell2361987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2362118400 cell2362249472)
                  (ThetaLowerSegment.join cell2362380544 cell2362511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2362642688 cell2362773760)
                  (ThetaLowerSegment.join cell2362904832 cell2363035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2363166976 cell2363298048)
                  (ThetaLowerSegment.join cell2363429120 cell2363560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2363691264 cell2363822336)
                  (ThetaLowerSegment.join cell2363953408 cell2364084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2364215552 cell2364346624)
                  (ThetaLowerSegment.join cell2364477696 cell2364608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2364739840 cell2364870912)
                  (ThetaLowerSegment.join cell2365001984 cell2365133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2365264128 cell2365395200)
                  (ThetaLowerSegment.join cell2365526272 cell2365657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2365788416 cell2365919488)
                  (ThetaLowerSegment.join cell2366050560 cell2366181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2366312704 cell2366443776)
                  (ThetaLowerSegment.join cell2366574848 cell2366705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2366836992 cell2366968064)
                  (ThetaLowerSegment.join cell2367099136 cell2367230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2367361280 cell2367492352)
                  (ThetaLowerSegment.join cell2367623424 cell2367754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2367885568 cell2368016640)
                  (ThetaLowerSegment.join cell2368147712 cell2368278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2368409856 cell2368540928)
                  (ThetaLowerSegment.join cell2368672000 cell2368803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2368934144 cell2369065216)
                  (ThetaLowerSegment.join cell2369196288 cell2369327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2369458432 cell2369589504)
                  (ThetaLowerSegment.join cell2369720576 cell2369851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2369982720 cell2370113792)
                  (ThetaLowerSegment.join cell2370244864 cell2370375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2370507008 cell2370638080)
                  (ThetaLowerSegment.join cell2370769152 cell2370900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2371031296 cell2371162368)
                  (ThetaLowerSegment.join cell2371293440 cell2371424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2371555584 cell2371686656)
                  (ThetaLowerSegment.join cell2371817728 cell2371948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2372079872 cell2372210944)
                  (ThetaLowerSegment.join cell2372342016 cell2372473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2372604160 cell2372735232)
                  (ThetaLowerSegment.join cell2372866304 cell2372997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2373128448 cell2373259520)
                  (ThetaLowerSegment.join cell2373390592 cell2373521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2373652736 cell2373783808)
                  (ThetaLowerSegment.join cell2373914880 cell2374045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2374177024 cell2374308096)
                  (ThetaLowerSegment.join cell2374439168 cell2374570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2374701312 cell2374832384)
                  (ThetaLowerSegment.join cell2374963456 cell2375094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2375225600 cell2375356672)
                  (ThetaLowerSegment.join cell2375487744 cell2375618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2375749888 cell2375880960)
                  (ThetaLowerSegment.join cell2376012032 cell2376143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2376274176 cell2376405248)
                  (ThetaLowerSegment.join cell2376536320 cell2376667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2376798464 cell2376929536)
                (ThetaLowerSegment.join cell2377060608 cell2377191680))
              (ThetaLowerSegment.join cell2377322752 cell2377339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
