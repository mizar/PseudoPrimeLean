/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3209341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3177341184 :
    ThetaLowerSegment 3177341184 3177472256 (31772660514347 / 10000) (31773956644079 / 10000) := by
  exact
    packedTile65536 3177341184 3177472256 14 5924 56367 32 _ _ (218793 / 10000) (2187933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177472256 :
    ThetaLowerSegment 3177472256 3177603328 (31773956644079 / 10000) (158876382029339 / 50000) := by
  exact
    packedTile65536 3177472256 3177603328 14 6032 56369 32 _ _ (1093967 / 50000) (2187937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177603328 :
    ThetaLowerSegment 3177603328 3177734400 (158876382029339 / 50000)
      (158882836446439 / 50000) := by
  exact
    packedTile65536 3177603328 3177734400 14 5900 56370 32 _ _ (1093969 / 50000) (2187941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177734400 :
    ThetaLowerSegment 3177734400 3177865472 (158882836446439 / 50000) (39722351982559 / 12500) := by
  exact
    packedTile65536 3177734400 3177865472 14 6007 56371 32 _ _ (1093971 / 50000) (437589 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177865472 :
    ThetaLowerSegment 3177865472 3177996544 (39722351982559 / 12500) (158895926915343 / 50000) := by
  exact
    packedTile65536 3177865472 3177996544 14 5959 56372 32 _ _ (1093973 / 50000) (2187949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177996544 :
    ThetaLowerSegment 3177996544 3178127616 (158895926915343 / 50000)
      (158902447006343 / 50000) := by
  exact
    packedTile65536 3177996544 3178127616 14 5960 56373 32 _ _ (43759 / 2000) (2187953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3178127616 :
    ThetaLowerSegment 3178127616 3178258688 (158902447006343 / 50000) (9931817623553 / 3125) := by
  exact
    packedTile65536 3178127616 3178258688 14 6065 56374 32 _ _ (1093977 / 50000) (2187957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3178258688 :
    ThetaLowerSegment 3178258688 3178389760 (9931817623553 / 3125) (31783114510851 / 10000) := by
  exact
    packedTile65536 3178258688 3178389760 14 5933 56376 32 _ _ (1093979 / 50000) (2187961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3178389760 :
    ThetaLowerSegment 3178389760 3178520832 (31783114510851 / 10000)
      (317844266322621 / 100000) := by
  exact
    packedTile65536 3178389760 3178520832 14 5997 56377 32 _ _ (2187963 / 100000) (1093983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3178520832 :
    ThetaLowerSegment 3178520832 3178651904 (317844266322621 / 100000)
      (317857459763631 / 100000) := by
  exact
    packedTile65536 3178520832 3178651904 14 6030 56378 32 _ _ (2187967 / 100000) (218797 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3178651904 :
    ThetaLowerSegment 3178651904 3178782976 (317857459763631 / 100000)
      (317870679484413 / 100000) := by
  exact
    packedTile65536 3178651904 3178782976 14 6042 56379 32 _ _ (2187971 / 100000) (1093987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3178782976 :
    ThetaLowerSegment 3178782976 3178914048 (317870679484413 / 100000)
      (158942051355519 / 50000) := by
  exact
    packedTile65536 3178782976 3178914048 14 6135 56380 32 _ _ (87519 / 4000) (1093989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3178914048 :
    ThetaLowerSegment 3178914048 3179045120 (158942051355519 / 50000) (12715889485959 / 4000) := by
  exact
    packedTile65536 3178914048 3179045120 14 6003 56381 32 _ _ (2187979 / 100000) (1093991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179045120 :
    ThetaLowerSegment 3179045120 3179176192 (12715889485959 / 4000) (317910478822091 / 100000) := by
  exact
    packedTile65536 3179045120 3179176192 14 6052 56383 32 _ _ (2187983 / 100000) (1093993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179176192 :
    ThetaLowerSegment 3179176192 3179307264 (317910478822091 / 100000) (6358470253213 / 2000) := by
  exact
    packedTile65536 3179176192 3179307264 14 5957 56384 32 _ _ (2187987 / 100000) (218799 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179307264 :
    ThetaLowerSegment 3179307264 3179438336 (6358470253213 / 2000) (158968259039577 / 50000) := by
  exact
    packedTile65536 3179307264 3179438336 14 5944 56385 32 _ _ (2187991 / 100000) (1093997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179438336 :
    ThetaLowerSegment 3179438336 3179569408 (158968259039577 / 50000)
      (158974789113639 / 50000) := by
  exact
    packedTile65536 3179438336 3179569408 14 5969 56386 32 _ _ (546999 / 25000) (2187999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179569408 :
    ThetaLowerSegment 3179569408 3179700480 (158974789113639 / 50000)
      (158981306071639 / 50000) := by
  exact
    packedTile65536 3179569408 3179700480 14 5957 56387 32 _ _ (547 / 25) (2188003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179700480 :
    ThetaLowerSegment 3179700480 3179831552 (158981306071639 / 50000)
      (158987872271643 / 50000) := by
  exact
    packedTile65536 3179700480 3179831552 14 6002 56388 32 _ _ (547001 / 25000) (2188007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179831552 :
    ThetaLowerSegment 3179831552 3179962624 (158987872271643 / 50000)
      (158994430825623 / 50000) := by
  exact
    packedTile65536 3179831552 3179962624 14 5995 56389 32 _ _ (273501 / 12500) (2188011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179962624 :
    ThetaLowerSegment 3179962624 3180093696 (158994430825623 / 50000)
      (159000994861623 / 50000) := by
  exact
    packedTile65536 3179962624 3180093696 14 6000 56391 32 _ _ (547003 / 25000) (437603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3180093696 :
    ThetaLowerSegment 3180093696 3180224768 (159000994861623 / 50000)
      (159007613610023 / 50000) := by
  exact
    packedTile65536 3180093696 3180224768 14 6050 56392 32 _ _ (136751 / 6250) (2188019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3180224768 :
    ThetaLowerSegment 3180224768 3180355840 (159007613610023 / 50000)
      (159014089055213 / 50000) := by
  exact
    packedTile65536 3180224768 3180355840 14 5919 56393 32 _ _ (109401 / 5000) (2188023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3180355840 :
    ThetaLowerSegment 3180355840 3180486912 (159014089055213 / 50000) (31804140690353 / 10000) := by
  exact
    packedTile65536 3180355840 3180486912 14 6046 56394 32 _ _ (273503 / 12500) (2188027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3180486912 :
    ThetaLowerSegment 3180486912 3180617984 (31804140690353 / 10000) (159027145009141 / 50000) := by
  exact
    packedTile65536 3180486912 3180617984 14 5888 56395 32 _ _ (2188029 / 100000) (68376 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3180617984 :
    ThetaLowerSegment 3180617984 3180749056 (159027145009141 / 50000)
      (318067477293173 / 100000) := by
  exact
    packedTile65536 3180617984 3180749056 14 6027 56396 32 _ _ (2188033 / 100000) (547009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3180749056 :
    ThetaLowerSegment 3180749056 3180880128 (318067477293173 / 100000)
      (79520122387303 / 25000) := by
  exact
    packedTile65536 3180749056 3180880128 14 5947 56398 32 _ _ (2188037 / 100000) (54701 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3180880128 :
    ThetaLowerSegment 3180880128 3181011200 (79520122387303 / 25000)
      (318093589350679 / 100000) := by
  exact
    packedTile65536 3180880128 3181011200 14 5987 56399 32 _ _ (2188041 / 100000) (547011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3181011200 :
    ThetaLowerSegment 3181011200 3181142272 (318093589350679 / 100000)
      (159053353340227 / 50000) := by
  exact
    packedTile65536 3181011200 3181142272 14 5995 56400 32 _ _ (437609 / 20000) (136753 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3181142272 :
    ThetaLowerSegment 3181142272 3181273344 (159053353340227 / 50000) (1272478499687 / 400) := by
  exact
    packedTile65536 3181142272 3181273344 14 5904 56401 32 _ _ (2188049 / 100000) (547013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3181273344 :
    ThetaLowerSegment 3181273344 3181404416 (1272478499687 / 400) (318132702914531 / 100000) := by
  exact
    packedTile65536 3181273344 3181404416 14 5977 56402 32 _ _ (2188053 / 100000) (273507 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3181404416 :
    ThetaLowerSegment 3181404416 3181535488 (318132702914531 / 100000)
      (63629202135441 / 20000) := by
  exact
    packedTile65536 3181404416 3181535488 14 6082 56403 32 _ _ (2188057 / 100000) (109403 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3181535488 :
    ThetaLowerSegment 3181535488 3181666560 (63629202135441 / 20000)
      (318159108410351 / 100000) := by
  exact
    packedTile65536 3181535488 3181666560 14 5986 56405 32 _ _ (2188061 / 100000) (68377 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3181666560 :
    ThetaLowerSegment 3181666560 3181797632 (318159108410351 / 100000)
      (318172129591117 / 100000) := by
  exact
    packedTile65536 3181666560 3181797632 14 5951 56406 32 _ _ (1094033 / 50000) (2188069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3181797632 :
    ThetaLowerSegment 3181797632 3181928704 (318172129591117 / 100000)
      (318185282079887 / 100000) := by
  exact
    packedTile65536 3181797632 3181928704 14 6011 56407 32 _ _ (218807 / 10000) (2188073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3181928704 :
    ThetaLowerSegment 3181928704 3182059776 (318185282079887 / 100000)
      (318198323000927 / 100000) := by
  exact
    packedTile65536 3181928704 3182059776 14 5960 56408 32 _ _ (1094037 / 50000) (2188077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3182059776 :
    ThetaLowerSegment 3182059776 3182190848 (318198323000927 / 100000)
      (63642236029451 / 20000) := by
  exact
    packedTile65536 3182059776 3182190848 14 5876 56409 32 _ _ (1094039 / 50000) (2188081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3182190848 :
    ThetaLowerSegment 3182190848 3182321920 (63642236029451 / 20000)
      (318224389598289 / 100000) := by
  exact
    packedTile65536 3182190848 3182321920 14 6037 56410 32 _ _ (1094041 / 50000) (437617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3182321920 :
    ThetaLowerSegment 3182321920 3182452992 (318224389598289 / 100000)
      (318237469976397 / 100000) := by
  exact
    packedTile65536 3182321920 3182452992 14 5978 56412 32 _ _ (1094043 / 50000) (2188089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3182452992 :
    ThetaLowerSegment 3182452992 3182584064 (318237469976397 / 100000)
      (318250548190327 / 100000) := by
  exact
    packedTile65536 3182452992 3182584064 14 5977 56413 32 _ _ (218809 / 10000) (2188093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3182584064 :
    ThetaLowerSegment 3182584064 3182715136 (318250548190327 / 100000)
      (63652723097539 / 20000) := by
  exact
    packedTile65536 3182584064 3182715136 14 5972 56414 32 _ _ (1094047 / 50000) (2188097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3182715136 :
    ThetaLowerSegment 3182715136 3182846208 (63652723097539 / 20000) (159138390639689 / 50000) := by
  exact
    packedTile65536 3182715136 3182846208 14 6017 56415 32 _ _ (2188099 / 100000) (1094051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3182846208 :
    ThetaLowerSegment 3182846208 3182977280 (159138390639689 / 50000) (79572458875469 / 25000) := by
  exact
    packedTile65536 3182846208 3182977280 14 5966 56416 32 _ _ (2188103 / 100000) (1094053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3182977280 :
    ThetaLowerSegment 3182977280 3183108352 (79572458875469 / 25000) (31830305604437 / 10000) := by
  exact
    packedTile65536 3182977280 3183108352 14 6042 56417 32 _ _ (2188107 / 100000) (218811 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3183108352 :
    ThetaLowerSegment 3183108352 3183239424 (31830305604437 / 10000) (79579053835981 / 25000) := by
  exact
    packedTile65536 3183108352 3183239424 14 6014 56419 32 _ _ (2188111 / 100000) (1094057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3183239424 :
    ThetaLowerSegment 3183239424 3183370496 (79579053835981 / 25000)
      (318329179925299 / 100000) := by
  exact
    packedTile65536 3183239424 3183370496 14 5925 56420 32 _ _ (437623 / 20000) (1094059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3183370496 :
    ThetaLowerSegment 3183370496 3183501568 (318329179925299 / 100000)
      (318342256124443 / 100000) := by
  exact
    packedTile65536 3183370496 3183501568 14 5976 56421 32 _ _ (2188119 / 100000) (1094061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3183501568 :
    ThetaLowerSegment 3183501568 3183632640 (318342256124443 / 100000)
      (159177689149037 / 50000) := by
  exact
    packedTile65536 3183501568 3183632640 14 5997 56422 32 _ _ (2188123 / 100000) (1094063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3183632640 :
    ThetaLowerSegment 3183632640 3183763712 (159177689149037 / 50000)
      (318368539881979 / 100000) := by
  exact
    packedTile65536 3183632640 3183763712 14 6015 56423 32 _ _ (2188127 / 100000) (218813 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3183763712 :
    ThetaLowerSegment 3183763712 3183894784 (318368539881979 / 100000)
      (318381629281621 / 100000) := by
  exact
    packedTile65536 3183763712 3183894784 14 5982 56424 32 _ _ (2188131 / 100000) (1094067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3183894784 :
    ThetaLowerSegment 3183894784 3184025856 (318381629281621 / 100000) (12735787172989 / 4000) := by
  exact
    packedTile65536 3183894784 3184025856 14 5964 56426 32 _ _ (273517 / 12500) (2188139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3184025856 :
    ThetaLowerSegment 3184025856 3184156928 (12735787172989 / 4000) (12736313639473 / 4000) := by
  exact
    packedTile65536 3184025856 3184156928 14 6015 56427 32 _ _ (109407 / 5000) (2188143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3184156928 :
    ThetaLowerSegment 3184156928 3184288000 (12736313639473 / 4000) (318420910770937 / 100000) := by
  exact
    packedTile65536 3184156928 3184288000 14 5973 56428 32 _ _ (136759 / 6250) (2188147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3184288000 :
    ThetaLowerSegment 3184288000 3184419072 (318420910770937 / 100000)
      (318433851478209 / 100000) := by
  exact
    packedTile65536 3184288000 3184419072 14 5914 56429 32 _ _ (547037 / 25000) (2188151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3184419072 :
    ThetaLowerSegment 3184419072 3184550144 (318433851478209 / 100000)
      (318447043846617 / 100000) := by
  exact
    packedTile65536 3184419072 3184550144 14 6029 56430 32 _ _ (273519 / 12500) (437631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3184550144 :
    ThetaLowerSegment 3184550144 3184681216 (318447043846617 / 100000)
      (318460203416801 / 100000) := by
  exact
    packedTile65536 3184550144 3184681216 14 6014 56431 32 _ _ (547039 / 25000) (2188159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3184681216 :
    ThetaLowerSegment 3184681216 3184812288 (318460203416801 / 100000)
      (318473443972961 / 100000) := by
  exact
    packedTile65536 3184681216 3184812288 14 6051 56432 32 _ _ (13676 / 625) (2188163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3184812288 :
    ThetaLowerSegment 3184812288 3184943360 (318473443972961 / 100000)
      (318486588274109 / 100000) := by
  exact
    packedTile65536 3184812288 3184943360 14 6007 56434 32 _ _ (547041 / 25000) (2188167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3184943360 :
    ThetaLowerSegment 3184943360 3185074432 (318486588274109 / 100000)
      (39812461105239 / 12500) := by
  exact
    packedTile65536 3184943360 3185074432 14 5987 56435 32 _ _ (2188169 / 100000) (547043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3185074432 :
    ThetaLowerSegment 3185074432 3185205504 (39812461105239 / 12500)
      (318512850702507 / 100000) := by
  exact
    packedTile65536 3185074432 3185205504 14 6015 56436 32 _ _ (2188173 / 100000) (136761 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3185205504 :
    ThetaLowerSegment 3185205504 3185336576 (318512850702507 / 100000)
      (318525949130029 / 100000) := by
  exact
    packedTile65536 3185205504 3185336576 14 5986 56437 32 _ _ (2188177 / 100000) (109409 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3185336576 :
    ThetaLowerSegment 3185336576 3185467648 (318525949130029 / 100000) (19908697722193 / 6250) := by
  exact
    packedTile65536 3185336576 3185467648 14 6039 56438 32 _ _ (2188181 / 100000) (273523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3185467648 :
    ThetaLowerSegment 3185467648 3185598720 (19908697722193 / 6250) (318552286100533 / 100000) := by
  exact
    packedTile65536 3185467648 3185598720 14 5997 56439 32 _ _ (437637 / 20000) (547047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3185598720 :
    ThetaLowerSegment 3185598720 3185729792 (318552286100533 / 100000) (9955166422462 / 3125) := by
  exact
    packedTile65536 3185598720 3185729792 14 5959 56441 32 _ _ (2188189 / 100000) (68381 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3185729792 :
    ThetaLowerSegment 3185729792 3185860864 (9955166422462 / 3125) (31857854658089 / 10000) := by
  exact
    packedTile65536 3185729792 3185860864 14 6042 56442 32 _ _ (2188193 / 100000) (547049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3185860864 :
    ThetaLowerSegment 3185860864 3185991936 (31857854658089 / 10000)
      (318591778608149 / 100000) := by
  exact
    packedTile65536 3185860864 3185991936 14 6047 56443 32 _ _ (2188197 / 100000) (10941 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3185991936 :
    ThetaLowerSegment 3185991936 3186123008 (318591778608149 / 100000)
      (79651208900879 / 25000) := by
  exact
    packedTile65536 3185991936 3186123008 14 5967 56444 32 _ _ (2188201 / 100000) (547051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3186123008 :
    ThetaLowerSegment 3186123008 3186254080 (79651208900879 / 25000) (159308920055887 / 50000) := by
  exact
    packedTile65536 3186123008 3186254080 14 5943 56445 32 _ _ (1094103 / 50000) (2188209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3186254080 :
    ThetaLowerSegment 3186254080 3186385152 (159308920055887 / 50000)
      (159315513132617 / 50000) := by
  exact
    packedTile65536 3186254080 3186385152 14 6026 56446 32 _ _ (218821 / 10000) (2188213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3186385152 :
    ThetaLowerSegment 3186385152 3186516224 (159315513132617 / 50000) (9957626920501 / 3125) := by
  exact
    packedTile65536 3186385152 3186516224 14 5957 56448 32 _ _ (1094107 / 50000) (2188217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3186516224 :
    ThetaLowerSegment 3186516224 3186647296 (9957626920501 / 3125) (159328546147111 / 50000) := by
  exact
    packedTile65536 3186516224 3186647296 14 5955 56449 32 _ _ (1094109 / 50000) (2188221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3186647296 :
    ThetaLowerSegment 3186647296 3186778368 (159328546147111 / 50000)
      (159334999213789 / 50000) := by
  exact
    packedTile65536 3186647296 3186778368 14 5898 56450 32 _ _ (1094111 / 50000) (87529 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3186778368 :
    ThetaLowerSegment 3186778368 3186909440 (159334999213789 / 50000) (39835388511193 / 12500) := by
  exact
    packedTile65536 3186778368 3186909440 14 5991 56451 32 _ _ (1094113 / 50000) (2188229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3186909440 :
    ThetaLowerSegment 3186909440 3187040512 (39835388511193 / 12500) (39837040624843 / 12500) := by
  exact
    packedTile65536 3186909440 3187040512 14 6040 56452 32 _ _ (218823 / 10000) (2188233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187040512 :
    ThetaLowerSegment 3187040512 3187171584 (39837040624843 / 12500) (9959672911849 / 3125) := by
  exact
    packedTile65536 3187040512 3187171584 14 6036 56453 32 _ _ (1094117 / 50000) (2188237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187171584 :
    ThetaLowerSegment 3187171584 3187302656 (9959672911849 / 3125) (31872266041893 / 10000) := by
  exact
    packedTile65536 3187171584 3187302656 14 5999 56455 32 _ _ (1094119 / 50000) (2188241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187302656 :
    ThetaLowerSegment 3187302656 3187433728 (31872266041893 / 10000) (159367912444409 / 50000) := by
  exact
    packedTile65536 3187302656 3187433728 14 6016 56456 32 _ _ (2188243 / 100000) (1094123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187433728 :
    ThetaLowerSegment 3187433728 3187564800 (159367912444409 / 50000)
      (318748930300101 / 100000) := by
  exact
    packedTile65536 3187433728 3187564800 14 5989 56457 32 _ _ (2188247 / 100000) (8753 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187564800 :
    ThetaLowerSegment 3187564800 3187695872 (318748930300101 / 100000)
      (79690548322353 / 25000) := by
  exact
    packedTile65536 3187564800 3187695872 14 6061 56458 32 _ _ (2188251 / 100000) (1094127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187695872 :
    ThetaLowerSegment 3187695872 3187826944 (79690548322353 / 25000)
      (318775206841897 / 100000) := by
  exact
    packedTile65536 3187695872 3187826944 14 5947 56459 32 _ _ (437651 / 20000) (1094129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187826944 :
    ThetaLowerSegment 3187826944 3187958016 (318775206841897 / 100000)
      (318788257618573 / 100000) := by
  exact
    packedTile65536 3187826944 3187958016 14 5964 56460 32 _ _ (2188259 / 100000) (1094131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187958016 :
    ThetaLowerSegment 3187958016 3188089088 (318788257618573 / 100000) (9962539315283 / 3125) := by
  exact
    packedTile65536 3187958016 3188089088 14 5941 56462 32 _ _ (2188263 / 100000) (1094133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3188089088 :
    ThetaLowerSegment 3188089088 3188220160 (9962539315283 / 3125) (79703607864099 / 25000) := by
  exact
    packedTile65536 3188089088 3188220160 14 6020 56463 32 _ _ (2188267 / 100000) (218827 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3188220160 :
    ThetaLowerSegment 3188220160 3188351232 (79703607864099 / 25000) (159413804612179 / 50000) := by
  exact
    packedTile65536 3188220160 3188351232 14 6022 56464 32 _ _ (2188271 / 100000) (1094137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3188351232 :
    ThetaLowerSegment 3188351232 3188482304 (159413804612179 / 50000) (19927545906113 / 6250) := by
  exact
    packedTile65536 3188351232 3188482304 14 5998 56465 32 _ _ (87531 / 4000) (1094139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3188482304 :
    ThetaLowerSegment 3188482304 3188613376 (19927545906113 / 6250) (19928355569713 / 6250) := by
  exact
    packedTile65536 3188482304 3188613376 14 5920 56466 32 _ _ (54707 / 2500) (2188283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3188613376 :
    ThetaLowerSegment 3188613376 3188744448 (19928355569713 / 6250) (39858361652633 / 12500) := by
  exact
    packedTile65536 3188613376 3188744448 14 6034 56467 32 _ _ (547071 / 25000) (2188287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3188744448 :
    ThetaLowerSegment 3188744448 3188875520 (39858361652633 / 12500) (7972002871429 / 2500) := by
  exact
    packedTile65536 3188744448 3188875520 14 6042 56468 32 _ _ (68384 / 3125) (2188291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3188875520 :
    ThetaLowerSegment 3188875520 3189006592 (7972002871429 / 2500) (3986166925297 / 1250) := by
  exact
    packedTile65536 3188875520 3189006592 14 6050 56470 32 _ _ (547073 / 25000) (437659 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3189006592 :
    ThetaLowerSegment 3189006592 3189137664 (3986166925297 / 1250) (7972666745123 / 2500) := by
  exact
    packedTile65536 3189006592 3189137664 14 6085 56471 32 _ _ (273537 / 12500) (2188299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3189137664 :
    ThetaLowerSegment 3189137664 3189268736 (7972666745123 / 2500) (15945990308491 / 5000) := by
  exact
    packedTile65536 3189137664 3189268736 14 6003 56472 32 _ _ (21883 / 1000) (2188303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3189268736 :
    ThetaLowerSegment 3189268736 3189399808 (15945990308491 / 5000) (79733201720971 / 25000) := by
  exact
    packedTile65536 3189268736 3189399808 14 5941 56473 32 _ _ (136769 / 6250) (2188307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3189399808 :
    ThetaLowerSegment 3189399808 3189530880 (79733201720971 / 25000) (39868225405637 / 12500) := by
  exact
    packedTile65536 3189399808 3189530880 14 5939 56474 32 _ _ (547077 / 25000) (2188311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3189530880 :
    ThetaLowerSegment 3189530880 3189661952 (39868225405637 / 12500) (39869860621779 / 12500) := by
  exact
    packedTile65536 3189530880 3189661952 14 5978 56475 32 _ _ (273539 / 12500) (437663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3189661952 :
    ThetaLowerSegment 3189661952 3189793024 (39869860621779 / 12500)
      (318971798232849 / 100000) := by
  exact
    packedTile65536 3189661952 3189793024 14 5901 56477 32 _ _ (2188317 / 100000) (13677 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3189793024 :
    ThetaLowerSegment 3189793024 3189924096 (318971798232849 / 100000)
      (318984792482947 / 100000) := by
  exact
    packedTile65536 3189793024 3189924096 14 5938 56478 32 _ _ (2188321 / 100000) (547081 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3189924096 :
    ThetaLowerSegment 3189924096 3190055168 (318984792482947 / 100000)
      (318998088745647 / 100000) := by
  exact
    packedTile65536 3189924096 3190055168 14 6076 56479 32 _ _ (87533 / 4000) (273541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3190055168 :
    ThetaLowerSegment 3190055168 3190186240 (318998088745647 / 100000)
      (79752829298613 / 25000) := by
  exact
    packedTile65536 3190055168 3190186240 14 6045 56480 32 _ _ (2188329 / 100000) (547083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3190186240 :
    ThetaLowerSegment 3190186240 3190317312 (79752829298613 / 25000)
      (319024466887449 / 100000) := by
  exact
    packedTile65536 3190186240 3190317312 14 6009 56481 32 _ _ (2188333 / 100000) (136771 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3190317312 :
    ThetaLowerSegment 3190317312 3190448384 (319024466887449 / 100000)
      (79759387738593 / 25000) := by
  exact
    packedTile65536 3190317312 3190448384 14 5979 56482 32 _ _ (2188337 / 100000) (109417 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3190448384 :
    ThetaLowerSegment 3190448384 3190579456 (79759387738593 / 25000) (79762626483273 / 25000) := by
  exact
    packedTile65536 3190448384 3190579456 14 5920 56484 32 _ _ (2188341 / 100000) (273543 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3190579456 :
    ThetaLowerSegment 3190579456 3190710528 (79762626483273 / 25000)
      (319063476253907 / 100000) := by
  exact
    packedTile65536 3190579456 3190710528 14 5927 56485 32 _ _ (437669 / 20000) (547087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3190710528 :
    ThetaLowerSegment 3190710528 3190841600 (319063476253907 / 100000)
      (319076667621679 / 100000) := by
  exact
    packedTile65536 3190710528 3190841600 14 6028 56486 32 _ _ (2188349 / 100000) (68386 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3190841600 :
    ThetaLowerSegment 3190841600 3190972672 (319076667621679 / 100000)
      (319089885279839 / 100000) := by
  exact
    packedTile65536 3190841600 3190972672 14 6040 56487 32 _ _ (1094177 / 50000) (2188357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3190972672 :
    ThetaLowerSegment 3190972672 3191103744 (319089885279839 / 100000)
      (319103124845739 / 100000) := by
  exact
    packedTile65536 3190972672 3191103744 14 6050 56488 32 _ _ (1094179 / 50000) (2188361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3191103744 :
    ThetaLowerSegment 3191103744 3191234816 (319103124845739 / 100000)
      (319116112774209 / 100000) := by
  exact
    packedTile65536 3191103744 3191234816 14 5935 56489 32 _ _ (1094181 / 50000) (437673 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3191234816 :
    ThetaLowerSegment 3191234816 3191365888 (319116112774209 / 100000)
      (319129304244457 / 100000) := by
  exact
    packedTile65536 3191234816 3191365888 14 6028 56491 32 _ _ (1094183 / 50000) (2188369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3191365888 :
    ThetaLowerSegment 3191365888 3191496960 (319129304244457 / 100000)
      (319142349118027 / 100000) := by
  exact
    packedTile65536 3191365888 3191496960 14 5961 56492 32 _ _ (218837 / 10000) (2188373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3191496960 :
    ThetaLowerSegment 3191496960 3191628032 (319142349118027 / 100000)
      (319155383073571 / 100000) := by
  exact
    packedTile65536 3191496960 3191628032 14 5956 56493 32 _ _ (1094187 / 50000) (2188377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3191628032 :
    ThetaLowerSegment 3191628032 3191759104 (319155383073571 / 100000)
      (319168565862643 / 100000) := by
  exact
    packedTile65536 3191628032 3191759104 14 6024 56494 32 _ _ (1094189 / 50000) (2188381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3191759104 :
    ThetaLowerSegment 3191759104 3191890176 (319168565862643 / 100000)
      (319181766182867 / 100000) := by
  exact
    packedTile65536 3191759104 3191890176 14 6032 56495 32 _ _ (1094191 / 50000) (437677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3191890176 :
    ThetaLowerSegment 3191890176 3192021248 (319181766182867 / 100000)
      (319194905252411 / 100000) := by
  exact
    packedTile65536 3191890176 3192021248 14 6004 56496 32 _ _ (1094193 / 50000) (2188389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3192021248 :
    ThetaLowerSegment 3192021248 3192152320 (319194905252411 / 100000)
      (319207921802079 / 100000) := by
  exact
    packedTile65536 3192021248 3192152320 14 5948 56497 32 _ _ (2188391 / 100000) (1094197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3192152320 :
    ThetaLowerSegment 3192152320 3192283392 (319207921802079 / 100000)
      (159610500919497 / 50000) := by
  exact
    packedTile65536 3192152320 3192283392 14 5977 56499 32 _ _ (437679 / 20000) (1094199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3192283392 :
    ThetaLowerSegment 3192283392 3192414464 (159610500919497 / 50000)
      (319234138798191 / 100000) := by
  exact
    packedTile65536 3192283392 3192414464 14 6003 56500 32 _ _ (2188399 / 100000) (1094201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3192414464 :
    ThetaLowerSegment 3192414464 3192545536 (319234138798191 / 100000)
      (159623486890893 / 50000) := by
  exact
    packedTile65536 3192414464 3192545536 14 5865 56501 32 _ _ (2188403 / 100000) (1094203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3192545536 :
    ThetaLowerSegment 3192545536 3192676608 (159623486890893 / 50000)
      (319260123919449 / 100000) := by
  exact
    packedTile65536 3192545536 3192676608 14 6009 56502 32 _ _ (2188407 / 100000) (218841 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3192676608 :
    ThetaLowerSegment 3192676608 3192807680 (319260123919449 / 100000)
      (159636534185257 / 50000) := by
  exact
    packedTile65536 3192676608 3192807680 14 5915 56503 32 _ _ (2188411 / 100000) (1094207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3192807680 :
    ThetaLowerSegment 3192807680 3192938752 (159636534185257 / 50000)
      (319286288585529 / 100000) := by
  exact
    packedTile65536 3192807680 3192938752 14 6041 56504 32 _ _ (437683 / 20000) (1094209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3192938752 :
    ThetaLowerSegment 3192938752 3193069824 (319286288585529 / 100000)
      (319299397215339 / 100000) := by
  exact
    packedTile65536 3192938752 3193069824 14 5990 56506 32 _ _ (2188419 / 100000) (1094211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3193069824 :
    ThetaLowerSegment 3193069824 3193200896 (319299397215339 / 100000)
      (79828109506999 / 25000) := by
  exact
    packedTile65536 3193069824 3193200896 14 5959 56507 32 _ _ (2188423 / 100000) (1094213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3193200896 :
    ThetaLowerSegment 3193200896 3193331968 (79828109506999 / 25000)
      (319325566401569 / 100000) := by
  exact
    packedTile65536 3193200896 3193331968 14 5999 56508 32 _ _ (2188427 / 100000) (218843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3193331968 :
    ThetaLowerSegment 3193331968 3193463040 (319325566401569 / 100000)
      (63867736334909 / 20000) := by
  exact
    packedTile65536 3193331968 3193463040 14 5993 56509 32 _ _ (136777 / 6250) (437687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3193463040 :
    ThetaLowerSegment 3193463040 3193594112 (63867736334909 / 20000)
      (319351794783057 / 100000) := by
  exact
    packedTile65536 3193463040 3193594112 14 5992 56510 32 _ _ (547109 / 25000) (2188439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3193594112 :
    ThetaLowerSegment 3193594112 3193725184 (319351794783057 / 100000)
      (319364958249657 / 100000) := by
  exact
    packedTile65536 3193594112 3193725184 14 6015 56511 32 _ _ (54711 / 2500) (2188443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3193725184 :
    ThetaLowerSegment 3193725184 3193856256 (319364958249657 / 100000)
      (319377894142141 / 100000) := by
  exact
    packedTile65536 3193725184 3193856256 14 5911 56513 32 _ _ (547111 / 25000) (2188447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3193856256 :
    ThetaLowerSegment 3193856256 3193987328 (319377894142141 / 100000)
      (319391044526173 / 100000) := by
  exact
    packedTile65536 3193856256 3193987328 14 6009 56514 32 _ _ (68389 / 3125) (2188451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3193987328 :
    ThetaLowerSegment 3193987328 3194118400 (319391044526173 / 100000)
      (63880809223901 / 20000) := by
  exact
    packedTile65536 3193987328 3194118400 14 5941 56515 32 _ _ (547113 / 25000) (437691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3194118400 :
    ThetaLowerSegment 3194118400 3194249472 (63880809223901 / 20000) (63883428805733 / 20000) := by
  exact
    packedTile65536 3194118400 3194249472 14 5985 56516 32 _ _ (273557 / 12500) (2188459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3194249472 :
    ThetaLowerSegment 3194249472 3194380544 (63883428805733 / 20000) (12777209766009 / 4000) := by
  exact
    packedTile65536 3194249472 3194380544 14 5986 56517 32 _ _ (109423 / 5000) (2188463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3194380544 :
    ThetaLowerSegment 3194380544 3194511616 (12777209766009 / 4000) (319443280830273 / 100000) := by
  exact
    packedTile65536 3194380544 3194511616 14 5957 56518 32 _ _ (136779 / 6250) (2188467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3194511616 :
    ThetaLowerSegment 3194511616 3194642688 (319443280830273 / 100000)
      (159728163146991 / 50000) := by
  exact
    packedTile65536 3194511616 3194642688 14 5961 56520 32 _ _ (2188469 / 100000) (273559 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3194642688 :
    ThetaLowerSegment 3194642688 3194773760 (159728163146991 / 50000)
      (159734798597127 / 50000) := by
  exact
    packedTile65536 3194642688 3194773760 14 6064 56521 32 _ _ (2188473 / 100000) (547119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3194773760 :
    ThetaLowerSegment 3194773760 3194904832 (159734798597127 / 50000)
      (159741346520311 / 50000) := by
  exact
    packedTile65536 3194773760 3194904832 14 5984 56522 32 _ _ (2188477 / 100000) (13678 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3194904832 :
    ThetaLowerSegment 3194904832 3195035904 (159741346520311 / 50000) (79873950510453 / 25000) := by
  exact
    packedTile65536 3194904832 3195035904 14 5990 56523 32 _ _ (2188481 / 100000) (547121 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3195035904 :
    ThetaLowerSegment 3195035904 3195166976 (79873950510453 / 25000) (79877255122803 / 25000) := by
  exact
    packedTile65536 3195035904 3195166976 14 6040 56524 32 _ _ (437697 / 20000) (273561 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3195166976 :
    ThetaLowerSegment 3195166976 3195298048 (79877255122803 / 25000)
      (319522171121613 / 100000) := by
  exact
    packedTile65536 3195166976 3195298048 14 6009 56525 32 _ _ (2188489 / 100000) (547123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3195298048 :
    ThetaLowerSegment 3195298048 3195429120 (319522171121613 / 100000)
      (159767674018983 / 50000) := by
  exact
    packedTile65536 3195298048 3195429120 14 6021 56526 32 _ _ (2188493 / 100000) (136781 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3195429120 :
    ThetaLowerSegment 3195429120 3195560192 (159767674018983 / 50000)
      (319548433061529 / 100000) := by
  exact
    packedTile65536 3195429120 3195560192 14 5979 56528 32 _ _ (2188497 / 100000) (4377 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3195560192 :
    ThetaLowerSegment 3195560192 3195691264 (319548433061529 / 100000) (9986298535157 / 3125) := by
  exact
    packedTile65536 3195560192 3195691264 14 5995 56529 32 _ _ (2188501 / 100000) (273563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3195691264 :
    ThetaLowerSegment 3195691264 3195822336 (9986298535157 / 3125) (39946833330873 / 12500) := by
  exact
    packedTile65536 3195691264 3195822336 14 5992 56530 32 _ _ (437701 / 20000) (547127 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3195822336 :
    ThetaLowerSegment 3195822336 3195953408 (39946833330873 / 12500) (79896939578451 / 25000) := by
  exact
    packedTile65536 3195822336 3195953408 14 5982 56531 32 _ _ (218851 / 10000) (2188513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3195953408 :
    ThetaLowerSegment 3195953408 3196084480 (79896939578451 / 25000) (79900185144713 / 25000) := by
  exact
    packedTile65536 3195953408 3196084480 14 5932 56532 32 _ _ (1094257 / 50000) (2188517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3196084480 :
    ThetaLowerSegment 3196084480 3196215552 (79900185144713 / 25000) (19975862876957 / 6250) := by
  exact
    packedTile65536 3196084480 3196215552 14 5970 56533 32 _ _ (1094259 / 50000) (2188521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3196215552 :
    ThetaLowerSegment 3196215552 3196346624 (19975862876957 / 6250) (159813526577489 / 50000) := by
  exact
    packedTile65536 3196215552 3196346624 14 6053 56535 32 _ _ (1094261 / 50000) (87541 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3196346624 :
    ThetaLowerSegment 3196346624 3196477696 (159813526577489 / 50000) (79910030210931 / 25000) := by
  exact
    packedTile65536 3196346624 3196477696 14 5971 56536 32 _ _ (1094263 / 50000) (2188529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3196477696 :
    ThetaLowerSegment 3196477696 3196608768 (79910030210931 / 25000) (79913319571521 / 25000) := by
  exact
    packedTile65536 3196477696 3196608768 14 6012 56537 32 _ _ (218853 / 10000) (2188533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3196608768 :
    ThetaLowerSegment 3196608768 3196739840 (79913319571521 / 25000) (159833201462241 / 50000) := by
  exact
    packedTile65536 3196608768 3196739840 14 5997 56538 32 _ _ (1094267 / 50000) (2188537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3196739840 :
    ThetaLowerSegment 3196739840 3196870912 (159833201462241 / 50000) (79919868765489 / 25000) := by
  exact
    packedTile65536 3196739840 3196870912 14 5973 56539 32 _ _ (1094269 / 50000) (2188541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3196870912 :
    ThetaLowerSegment 3196870912 3197001984 (79919868765489 / 25000) (19980787073919 / 6250) := by
  exact
    packedTile65536 3196870912 3197001984 14 5994 56540 32 _ _ (1094271 / 50000) (437709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3197001984 :
    ThetaLowerSegment 3197001984 3197133056 (19980787073919 / 6250) (159852887397631 / 50000) := by
  exact
    packedTile65536 3197001984 3197133056 14 6023 56542 32 _ _ (1094273 / 50000) (2188549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3197133056 :
    ThetaLowerSegment 3197133056 3197264128 (159852887397631 / 50000)
      (319718860141691 / 100000) := by
  exact
    packedTile65536 3197133056 3197264128 14 5979 56543 32 _ _ (2188551 / 100000) (1094277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3197264128 :
    ThetaLowerSegment 3197264128 3197395200 (319718860141691 / 100000)
      (79932999509339 / 25000) := by
  exact
    packedTile65536 3197264128 3197395200 14 6003 56544 32 _ _ (437711 / 20000) (1094279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3197395200 :
    ThetaLowerSegment 3197395200 3197526272 (79932999509339 / 25000)
      (319745004643493 / 100000) := by
  exact
    packedTile65536 3197395200 3197526272 14 5943 56545 32 _ _ (2188559 / 100000) (1094281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3197526272 :
    ThetaLowerSegment 3197526272 3197657344 (319745004643493 / 100000)
      (319758009084839 / 100000) := by
  exact
    packedTile65536 3197526272 3197657344 14 5942 56546 32 _ _ (2188563 / 100000) (1094283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3197657344 :
    ThetaLowerSegment 3197657344 3197788416 (319758009084839 / 100000)
      (319771258669457 / 100000) := by
  exact
    packedTile65536 3197657344 3197788416 14 6054 56547 32 _ _ (2188567 / 100000) (218857 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3197788416 :
    ThetaLowerSegment 3197788416 3197919488 (319771258669457 / 100000)
      (159892172067733 / 50000) := by
  exact
    packedTile65536 3197788416 3197919488 14 5979 56548 32 _ _ (2188571 / 100000) (1094287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3197919488 :
    ThetaLowerSegment 3197919488 3198050560 (159892172067733 / 50000)
      (159898689644083 / 50000) := by
  exact
    packedTile65536 3197919488 3198050560 14 5956 56550 32 _ _ (87543 / 4000) (1094289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3198050560 :
    ThetaLowerSegment 3198050560 3198181632 (159898689644083 / 50000) (79952646293463 / 25000) := by
  exact
    packedTile65536 3198050560 3198181632 14 6034 56551 32 _ _ (2188579 / 100000) (1094291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3198181632 :
    ThetaLowerSegment 3198181632 3198312704 (79952646293463 / 25000)
      (319823613808451 / 100000) := by
  exact
    packedTile65536 3198181632 3198312704 14 5953 56552 32 _ _ (2188583 / 100000) (1094293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3198312704 :
    ThetaLowerSegment 3198312704 3198443776 (319823613808451 / 100000) (7995916827677 / 2500) := by
  exact
    packedTile65536 3198312704 3198443776 14 5967 56553 32 _ _ (2188587 / 100000) (218859 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3198443776 :
    ThetaLowerSegment 3198443776 3198574848 (7995916827677 / 2500) (39981201507873 / 12500) := by
  exact
    packedTile65536 3198443776 3198574848 14 5912 56554 32 _ _ (136787 / 6250) (437719 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3198574848 :
    ThetaLowerSegment 3198574848 3198705920 (39981201507873 / 12500) (7996570560711 / 2500) := by
  exact
    packedTile65536 3198574848 3198705920 14 6036 56555 32 _ _ (547149 / 25000) (2188599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3198705920 :
    ThetaLowerSegment 3198705920 3198836992 (7996570560711 / 2500) (7996901914751 / 2500) := by
  exact
    packedTile65536 3198705920 3198836992 14 6056 56557 32 _ _ (10943 / 500) (2188603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3198836992 :
    ThetaLowerSegment 3198836992 3198968064 (7996901914751 / 2500) (39986149932453 / 12500) := by
  exact
    packedTile65536 3198836992 3198968064 14 5996 56558 32 _ _ (547151 / 25000) (2188607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3198968064 :
    ThetaLowerSegment 3198968064 3199099136 (39986149932453 / 12500) (39987754729269 / 12500) := by
  exact
    packedTile65536 3198968064 3199099136 14 5866 56559 32 _ _ (68394 / 3125) (2188611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3199099136 :
    ThetaLowerSegment 3199099136 3199230208 (39987754729269 / 12500) (19994689613263 / 6250) := by
  exact
    packedTile65536 3199099136 3199230208 14 5938 56560 32 _ _ (547153 / 25000) (437723 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3199230208 :
    ThetaLowerSegment 3199230208 3199361280 (19994689613263 / 6250) (19995513627187 / 6250) := by
  exact
    packedTile65536 3199230208 3199361280 14 6024 56561 32 _ _ (273577 / 12500) (2188619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3199361280 :
    ThetaLowerSegment 3199361280 3199492352 (19995513627187 / 6250) (79985332514353 / 25000) := by
  exact
    packedTile65536 3199361280 3199492352 14 5991 56562 32 _ _ (109431 / 5000) (2188623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3199492352 :
    ThetaLowerSegment 3199492352 3199623424 (79985332514353 / 25000) (3199544333493 / 1000) := by
  exact
    packedTile65536 3199492352 3199623424 14 5987 56564 32 _ _ (136789 / 6250) (2188627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3199623424 :
    ThetaLowerSegment 3199623424 3199754496 (3199544333493 / 1000) (15998379350179 / 5000) := by
  exact
    packedTile65536 3199623424 3199754496 14 6010 56565 32 _ _ (547157 / 25000) (2188631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3199754496 :
    ThetaLowerSegment 3199754496 3199885568 (15998379350179 / 5000) (79995170397209 / 25000) := by
  exact
    packedTile65536 3199754496 3199885568 14 5983 56566 32 _ _ (273579 / 12500) (437727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3199885568 :
    ThetaLowerSegment 3199885568 3200016640 (79995170397209 / 25000)
      (319993964426789 / 100000) := by
  exact
    packedTile65536 3199885568 3200016640 14 6069 56567 32 _ _ (2188637 / 100000) (13679 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200016640 :
    ThetaLowerSegment 3200016640 3200147712 (319993964426789 / 100000)
      (64001421880927 / 20000) := by
  exact
    packedTile65536 3200016640 3200147712 14 6006 56568 32 _ _ (2188641 / 100000) (547161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200147712 :
    ThetaLowerSegment 3200147712 3200278784 (64001421880927 / 20000) (64004059635881 / 20000) := by
  exact
    packedTile65536 3200147712 3200278784 14 6026 56569 32 _ _ (437729 / 20000) (273581 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200278784 :
    ThetaLowerSegment 3200278784 3200409856 (64004059635881 / 20000)
      (320033311886359 / 100000) := by
  exact
    packedTile65536 3200278784 3200409856 14 5946 56571 32 _ _ (2188649 / 100000) (547163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200409856 :
    ThetaLowerSegment 3200409856 3200540928 (320033311886359 / 100000)
      (320046435049747 / 100000) := by
  exact
    packedTile65536 3200409856 3200540928 14 5996 56572 32 _ _ (2188653 / 100000) (136791 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200540928 :
    ThetaLowerSegment 3200540928 3200672000 (320046435049747 / 100000)
      (40007425355309 / 12500) := by
  exact
    packedTile65536 3200540928 3200672000 14 5925 56573 32 _ _ (2188657 / 100000) (109433 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200672000 :
    ThetaLowerSegment 3200672000 3200803072 (40007425355309 / 12500) (16003625427227 / 5000) := by
  exact
    packedTile65536 3200672000 3200803072 14 5988 56574 32 _ _ (2188661 / 100000) (273583 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200803072 :
    ThetaLowerSegment 3200803072 3200934144 (16003625427227 / 5000) (8002141669963 / 2500) := by
  exact
    packedTile65536 3200803072 3200934144 14 6012 56575 32 _ _ (437733 / 20000) (547167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200934144 :
    ThetaLowerSegment 3200934144 3201065216 (8002141669963 / 2500) (20006162888103 / 6250) := by
  exact
    packedTile65536 3200934144 3201065216 14 5912 56576 32 _ _ (2188669 / 100000) (68396 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3201065216 :
    ThetaLowerSegment 3201065216 3201196288 (20006162888103 / 6250) (64022364721179 / 20000) := by
  exact
    packedTile65536 3201065216 3201196288 14 6039 56577 32 _ _ (2188673 / 100000) (547169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3201196288 :
    ThetaLowerSegment 3201196288 3201327360 (64022364721179 / 20000)
      (320125135145491 / 100000) := by
  exact
    packedTile65536 3201196288 3201327360 14 6082 56579 32 _ _ (1094339 / 50000) (2188681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3201327360 :
    ThetaLowerSegment 3201327360 3201458432 (320125135145491 / 100000)
      (64027663077699 / 20000) := by
  exact
    packedTile65536 3201327360 3201458432 14 6022 56580 32 _ _ (1094341 / 50000) (437737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3201458432 :
    ThetaLowerSegment 3201458432 3201589504 (64027663077699 / 20000)
      (320151303051219 / 100000) := by
  exact
    packedTile65536 3201458432 3201589504 14 5934 56581 32 _ _ (1094343 / 50000) (2188689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3201589504 :
    ThetaLowerSegment 3201589504 3201720576 (320151303051219 / 100000)
      (320164417681699 / 100000) := by
  exact
    packedTile65536 3201589504 3201720576 14 5992 56582 32 _ _ (218869 / 10000) (2188693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3201720576 :
    ThetaLowerSegment 3201720576 3201851648 (320164417681699 / 100000)
      (320177418524059 / 100000) := by
  exact
    packedTile65536 3201720576 3201851648 14 5940 56583 32 _ _ (1094347 / 50000) (2188697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3201851648 :
    ThetaLowerSegment 3201851648 3201982720 (320177418524059 / 100000)
      (320190561655549 / 100000) := by
  exact
    packedTile65536 3201851648 3201982720 14 6005 56584 32 _ _ (1094349 / 50000) (2188701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3201982720 :
    ThetaLowerSegment 3201982720 3202113792 (320190561655549 / 100000)
      (320203597564661 / 100000) := by
  exact
    packedTile65536 3201982720 3202113792 14 5956 56586 32 _ _ (1094351 / 50000) (437741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3202113792 :
    ThetaLowerSegment 3202113792 3202244864 (320203597564661 / 100000)
      (64043338956273 / 20000) := by
  exact
    packedTile65536 3202113792 3202244864 14 5984 56587 32 _ _ (1094353 / 50000) (2188709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3202244864 :
    ThetaLowerSegment 3202244864 3202375936 (64043338956273 / 20000) (64045995612471 / 20000) := by
  exact
    packedTile65536 3202244864 3202375936 14 6069 56588 32 _ _ (218871 / 10000) (2188713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3202375936 :
    ThetaLowerSegment 3202375936 3202507008 (64045995612471 / 20000)
      (320243221970769 / 100000) := by
  exact
    packedTile65536 3202375936 3202507008 14 6051 56589 32 _ _ (1094357 / 50000) (2188717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3202507008 :
    ThetaLowerSegment 3202507008 3202638080 (320243221970769 / 100000)
      (320256487790567 / 100000) := by
  exact
    packedTile65536 3202507008 3202638080 14 6061 56590 32 _ _ (1094359 / 50000) (2188721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3202638080 :
    ThetaLowerSegment 3202638080 3202769152 (320256487790567 / 100000)
      (320269445030727 / 100000) := by
  exact
    packedTile65536 3202638080 3202769152 14 5920 56591 32 _ _ (2188723 / 100000) (1094363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3202769152 :
    ThetaLowerSegment 3202769152 3202900224 (320269445030727 / 100000)
      (160141202241647 / 50000) := by
  exact
    packedTile65536 3202769152 3202900224 14 5921 56593 32 _ _ (2188727 / 100000) (218873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3202900224 :
    ThetaLowerSegment 3202900224 3203031296 (160141202241647 / 50000)
      (320295565322797 / 100000) := by
  exact
    packedTile65536 3202900224 3203031296 14 6013 56594 32 _ _ (2188731 / 100000) (1094367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3203031296 :
    ThetaLowerSegment 3203031296 3203162368 (320295565322797 / 100000)
      (160154378414321 / 50000) := by
  exact
    packedTile65536 3203031296 3203162368 14 6027 56595 32 _ _ (437747 / 20000) (1094369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3203162368 :
    ThetaLowerSegment 3203162368 3203293440 (160154378414321 / 50000) (12812870930379 / 4000) := by
  exact
    packedTile65536 3203162368 3203293440 14 5947 56596 32 _ _ (2188739 / 100000) (1094371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3203293440 :
    ThetaLowerSegment 3203293440 3203424512 (12812870930379 / 4000) (320334721863063 / 100000) := by
  exact
    packedTile65536 3203293440 3203424512 14 5916 56597 32 _ _ (2188743 / 100000) (1094373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3203424512 :
    ThetaLowerSegment 3203424512 3203555584 (320334721863063 / 100000)
      (320347849967569 / 100000) := by
  exact
    packedTile65536 3203424512 3203555584 14 5998 56598 32 _ _ (2188747 / 100000) (1751 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3203555584 :
    ThetaLowerSegment 3203555584 3203686656 (320347849967569 / 100000)
      (160180529539927 / 50000) := by
  exact
    packedTile65536 3203555584 3203686656 14 6035 56599 32 _ _ (2188751 / 100000) (1094377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3203686656 :
    ThetaLowerSegment 3203686656 3203817728 (160180529539927 / 50000)
      (320374250706239 / 100000) := by
  exact
    packedTile65536 3203686656 3203817728 14 6027 56601 32 _ _ (437751 / 20000) (1094379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3203817728 :
    ThetaLowerSegment 3203817728 3203948800 (320374250706239 / 100000)
      (160193775897341 / 50000) := by
  exact
    packedTile65536 3203817728 3203948800 14 6077 56602 32 _ _ (2188759 / 100000) (1094381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3203948800 :
    ThetaLowerSegment 3203948800 3204079872 (160193775897341 / 50000)
      (160200324676237 / 50000) := by
  exact
    packedTile65536 3203948800 3204079872 14 5984 56603 32 _ _ (2188763 / 100000) (1094383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204079872 :
    ThetaLowerSegment 3204079872 3204210944 (160200324676237 / 50000) (32041389577641 / 10000) := by
  exact
    packedTile65536 3204079872 3204210944 14 6052 56604 32 _ _ (68399 / 3125) (2188771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204210944 :
    ThetaLowerSegment 3204210944 3204342016 (32041389577641 / 10000) (160213495599643 / 50000) := by
  exact
    packedTile65536 3204210944 3204342016 14 5983 56605 32 _ _ (547193 / 25000) (87551 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204342016 :
    ThetaLowerSegment 3204342016 3204473088 (160213495599643 / 50000)
      (160220103514387 / 50000) := by
  exact
    packedTile65536 3204342016 3204473088 14 6038 56606 32 _ _ (273597 / 12500) (2188779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204473088 :
    ThetaLowerSegment 3204473088 3204604160 (160220103514387 / 50000)
      (160226611851717 / 50000) := by
  exact
    packedTile65536 3204473088 3204604160 14 5947 56608 32 _ _ (109439 / 5000) (2188783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204604160 :
    ThetaLowerSegment 3204604160 3204735232 (160226611851717 / 50000)
      (160233192430813 / 50000) := by
  exact
    packedTile65536 3204604160 3204735232 14 6013 56609 32 _ _ (136799 / 6250) (2188787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204735232 :
    ThetaLowerSegment 3204735232 3204866304 (160233192430813 / 50000)
      (160239829930423 / 50000) := by
  exact
    packedTile65536 3204735232 3204866304 14 6065 56610 32 _ _ (547197 / 25000) (2188791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204866304 :
    ThetaLowerSegment 3204866304 3204997376 (160239829930423 / 50000)
      (160246318604307 / 50000) := by
  exact
    packedTile65536 3204866304 3204997376 14 5929 56611 32 _ _ (273599 / 12500) (437759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204997376 :
    ThetaLowerSegment 3204997376 3205128448 (160246318604307 / 50000)
      (160252846688377 / 50000) := by
  exact
    packedTile65536 3204997376 3205128448 14 5965 56612 32 _ _ (547199 / 25000) (2188799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3205128448 :
    ThetaLowerSegment 3205128448 3205259520 (160252846688377 / 50000)
      (160259338669177 / 50000) := by
  exact
    packedTile65536 3205128448 3205259520 14 5932 56613 32 _ _ (2736 / 125) (2188803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3205259520 :
    ThetaLowerSegment 3205259520 3205390592 (160259338669177 / 50000)
      (160265952140463 / 50000) := by
  exact
    packedTile65536 3205259520 3205390592 14 6043 56615 32 _ _ (547201 / 25000) (2188807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3205390592 :
    ThetaLowerSegment 3205390592 3205521664 (160265952140463 / 50000) (6410899779503 / 2000) := by
  exact
    packedTile65536 3205390592 3205521664 14 5978 56616 32 _ _ (273601 / 12500) (2188811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3205521664 :
    ThetaLowerSegment 3205521664 3205652736 (6410899779503 / 2000) (80139520613629 / 25000) := by
  exact
    packedTile65536 3205521664 3205652736 14 5982 56617 32 _ _ (2188813 / 100000) (136801 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3205652736 :
    ThetaLowerSegment 3205652736 3205783808 (80139520613629 / 25000)
      (320571221922967 / 100000) := by
  exact
    packedTile65536 3205652736 3205783808 14 6003 56618 32 _ _ (2188817 / 100000) (109441 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3205783808 :
    ThetaLowerSegment 3205783808 3205914880 (320571221922967 / 100000)
      (320584188498571 / 100000) := by
  exact
    packedTile65536 3205783808 3205914880 14 5924 56619 32 _ _ (2188821 / 100000) (273603 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3205914880 :
    ThetaLowerSegment 3205914880 3206045952 (320584188498571 / 100000) (20037340935431 / 6250) := by
  exact
    packedTile65536 3205914880 3206045952 14 6061 56620 32 _ _ (87553 / 4000) (547207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3206045952 :
    ThetaLowerSegment 3206045952 3206177024 (20037340935431 / 6250) (320610533220171 / 100000) := by
  exact
    packedTile65536 3206045952 3206177024 14 5975 56621 32 _ _ (2188829 / 100000) (68401 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3206177024 :
    ThetaLowerSegment 3206177024 3206308096 (320610533220171 / 100000)
      (320623736260827 / 100000) := by
  exact
    packedTile65536 3206177024 3206308096 14 6032 56623 32 _ _ (2188833 / 100000) (547209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3206308096 :
    ThetaLowerSegment 3206308096 3206439168 (320623736260827 / 100000)
      (80159198168383 / 25000) := by
  exact
    packedTile65536 3206308096 3206439168 14 5965 56624 32 _ _ (2188837 / 100000) (54721 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3206439168 :
    ThetaLowerSegment 3206439168 3206570240 (80159198168383 / 25000)
      (320649958552147 / 100000) := by
  exact
    packedTile65536 3206439168 3206570240 14 6015 56625 32 _ _ (2188841 / 100000) (547211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3206570240 :
    ThetaLowerSegment 3206570240 3206701312 (320649958552147 / 100000)
      (320663144154427 / 100000) := by
  exact
    packedTile65536 3206570240 3206701312 14 6024 56626 32 _ _ (437769 / 20000) (136803 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3206701312 :
    ThetaLowerSegment 3206701312 3206832384 (320663144154427 / 100000)
      (320676246604541 / 100000) := by
  exact
    packedTile65536 3206701312 3206832384 14 5986 56627 32 _ _ (2188849 / 100000) (547213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3206832384 :
    ThetaLowerSegment 3206832384 3206963456 (320676246604541 / 100000)
      (160344634045519 / 50000) := by
  exact
    packedTile65536 3206832384 3206963456 14 5949 56628 32 _ _ (2188853 / 100000) (273607 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3206963456 :
    ThetaLowerSegment 3206963456 3207094528 (160344634045519 / 50000) (80175591007113 / 25000) := by
  exact
    packedTile65536 3206963456 3207094528 14 5983 56630 32 _ _ (1094429 / 50000) (2188861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3207094528 :
    ThetaLowerSegment 3207094528 3207225600 (80175591007113 / 25000) (160357754072381 / 50000) := by
  exact
    packedTile65536 3207094528 3207225600 14 6005 56631 32 _ _ (1094431 / 50000) (437773 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3207225600 :
    ThetaLowerSegment 3207225600 3207356672 (160357754072381 / 50000) (40091099593781 / 12500) := by
  exact
    packedTile65536 3207225600 3207356672 14 6071 56632 32 _ _ (1094433 / 50000) (2188869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3207356672 :
    ThetaLowerSegment 3207356672 3207487744 (40091099593781 / 12500) (160370917924419 / 50000) := by
  exact
    packedTile65536 3207356672 3207487744 14 5957 56633 32 _ _ (218887 / 10000) (2188873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3207487744 :
    ThetaLowerSegment 3207487744 3207618816 (160370917924419 / 50000) (20047181327359 / 6250) := by
  exact
    packedTile65536 3207487744 3207618816 14 5969 56634 32 _ _ (1094437 / 50000) (2188877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3207618816 :
    ThetaLowerSegment 3207618816 3207749888 (20047181327359 / 6250) (8019201519307 / 2500) := by
  exact
    packedTile65536 3207618816 3207749888 14 6012 56635 32 _ _ (1094439 / 50000) (2188881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3207749888 :
    ThetaLowerSegment 3207749888 3207880960 (8019201519307 / 2500) (16039056419891 / 5000) := by
  exact
    packedTile65536 3207749888 3207880960 14 5970 56637 32 _ _ (1094441 / 50000) (437777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3207880960 :
    ThetaLowerSegment 3207880960 3208012032 (16039056419891 / 5000) (80198604828403 / 25000) := by
  exact
    packedTile65536 3207880960 3208012032 14 6072 56638 32 _ _ (1094443 / 50000) (2188889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3208012032 :
    ThetaLowerSegment 3208012032 3208143104 (80198604828403 / 25000) (160403744587901 / 50000) := by
  exact
    packedTile65536 3208012032 3208143104 14 5971 56639 32 _ _ (218889 / 10000) (2188893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3208143104 :
    ThetaLowerSegment 3208143104 3208274176 (160403744587901 / 50000) (401025551077 / 125) := by
  exact
    packedTile65536 3208143104 3208274176 14 5917 56640 32 _ _ (1094447 / 50000) (2188897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3208274176 :
    ThetaLowerSegment 3208274176 3208405248 (401025551077 / 125) (160416867019577 / 50000) := by
  exact
    packedTile65536 3208274176 3208405248 14 6073 56641 32 _ _ (1094449 / 50000) (2188901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3208405248 :
    ThetaLowerSegment 3208405248 3208536320 (160416867019577 / 50000)
      (160423446858989 / 50000) := by
  exact
    packedTile65536 3208405248 3208536320 14 6012 56642 32 _ _ (1094451 / 50000) (437781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3208536320 :
    ThetaLowerSegment 3208536320 3208667392 (160423446858989 / 50000)
      (320860121282979 / 100000) := by
  exact
    packedTile65536 3208536320 3208667392 14 6043 56643 32 _ _ (2188907 / 100000) (218891 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3208667392 :
    ThetaLowerSegment 3208667392 3208798464 (320860121282979 / 100000)
      (320873206592937 / 100000) := by
  exact
    packedTile65536 3208667392 3208798464 14 5978 56645 32 _ _ (2188911 / 100000) (1094457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3208798464 :
    ThetaLowerSegment 3208798464 3208929536 (320873206592937 / 100000)
      (80221611834943 / 25000) := by
  exact
    packedTile65536 3208798464 3208929536 14 6049 56646 32 _ _ (437783 / 20000) (1094459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3208929536 :
    ThetaLowerSegment 3208929536 3209060608 (80221611834943 / 25000) (32089954145323 / 10000) := by
  exact
    packedTile65536 3208929536 3209060608 14 5982 56647 32 _ _ (2188919 / 100000) (1094461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209060608 :
    ThetaLowerSegment 3209060608 3209191680 (32089954145323 / 10000) (160456298095001 / 50000) := by
  exact
    packedTile65536 3209060608 3209191680 14 5964 56648 32 _ _ (2188923 / 100000) (1094463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209191680 :
    ThetaLowerSegment 3209191680 3209322752 (160456298095001 / 50000)
      (160462755429651 / 50000) := by
  exact
    packedTile65536 3209191680 3209322752 14 5900 56649 32 _ _ (2188927 / 100000) (218893 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209322752 :
    ThetaLowerSegment 3209322752 3209339136 (160462755429651 / 50000)
      (320927154746483 / 100000) := by
  exact
    packedTile65536 3209322752 3209339136 11 751 56650 32 _ _ (2188931 / 100000) (1094467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209339136 :
    ThetaLowerSegment 3209339136 3209341184 (320927154746483 / 100000)
      (320927380206479 / 100000) := by
  exact
    packedTile65536 3209339136 3209341184 8 103 56651 32 _ _ (547233 / 25000) (437787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3177341184_3209341184 :
    ThetaLowerSegment 3177341184 3209341184 (31772660514347 / 10000)
      (320927380206479 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3177341184 cell3177472256)
                  (ThetaLowerSegment.join cell3177603328 cell3177734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3177865472 cell3177996544)
                  (ThetaLowerSegment.join cell3178127616 cell3178258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3178389760 cell3178520832)
                  (ThetaLowerSegment.join cell3178651904 cell3178782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3178914048 cell3179045120)
                  (ThetaLowerSegment.join cell3179176192 cell3179307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3179438336 cell3179569408)
                  (ThetaLowerSegment.join cell3179700480 cell3179831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3179962624 cell3180093696)
                  (ThetaLowerSegment.join cell3180224768 cell3180355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3180486912 cell3180617984)
                  (ThetaLowerSegment.join cell3180749056 cell3180880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3181011200 cell3181142272)
                  (ThetaLowerSegment.join cell3181273344 cell3181404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3181535488 cell3181666560)
                  (ThetaLowerSegment.join cell3181797632 cell3181928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3182059776 cell3182190848)
                  (ThetaLowerSegment.join cell3182321920 cell3182452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3182584064 cell3182715136)
                  (ThetaLowerSegment.join cell3182846208 cell3182977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3183108352 cell3183239424)
                  (ThetaLowerSegment.join cell3183370496 cell3183501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3183632640 cell3183763712)
                  (ThetaLowerSegment.join cell3183894784 cell3184025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3184156928 cell3184288000)
                  (ThetaLowerSegment.join cell3184419072 cell3184550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3184681216 cell3184812288)
                  (ThetaLowerSegment.join cell3184943360 cell3185074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3185205504 cell3185336576)
                  (ThetaLowerSegment.join cell3185467648 cell3185598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3185729792 cell3185860864)
                  (ThetaLowerSegment.join cell3185991936 cell3186123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3186254080 cell3186385152)
                  (ThetaLowerSegment.join cell3186516224 cell3186647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3186778368 cell3186909440)
                  (ThetaLowerSegment.join cell3187040512 cell3187171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3187302656 cell3187433728)
                  (ThetaLowerSegment.join cell3187564800 cell3187695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3187826944 cell3187958016)
                  (ThetaLowerSegment.join cell3188089088 cell3188220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3188351232 cell3188482304)
                  (ThetaLowerSegment.join cell3188613376 cell3188744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3188875520 cell3189006592)
                  (ThetaLowerSegment.join cell3189137664 cell3189268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3189399808 cell3189530880)
                  (ThetaLowerSegment.join cell3189661952 cell3189793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3189924096 cell3190055168)
                  (ThetaLowerSegment.join cell3190186240 cell3190317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3190448384 cell3190579456)
                  (ThetaLowerSegment.join cell3190710528 cell3190841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3190972672 cell3191103744)
                  (ThetaLowerSegment.join cell3191234816 cell3191365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3191496960 cell3191628032)
                  (ThetaLowerSegment.join cell3191759104 cell3191890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3192021248 cell3192152320)
                  (ThetaLowerSegment.join cell3192283392 cell3192414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3192545536 cell3192676608)
                  (ThetaLowerSegment.join cell3192807680 cell3192938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3193069824 cell3193200896)
                  (ThetaLowerSegment.join cell3193331968 cell3193463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3193594112 cell3193725184)
                  (ThetaLowerSegment.join cell3193856256 cell3193987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3194118400 cell3194249472)
                  (ThetaLowerSegment.join cell3194380544 cell3194511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3194642688 cell3194773760)
                  (ThetaLowerSegment.join cell3194904832 cell3195035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3195166976 cell3195298048)
                  (ThetaLowerSegment.join cell3195429120 cell3195560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3195691264 cell3195822336)
                  (ThetaLowerSegment.join cell3195953408 cell3196084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3196215552 cell3196346624)
                  (ThetaLowerSegment.join cell3196477696 cell3196608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3196739840 cell3196870912)
                  (ThetaLowerSegment.join cell3197001984 cell3197133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3197264128 cell3197395200)
                  (ThetaLowerSegment.join cell3197526272 cell3197657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3197788416 cell3197919488)
                  (ThetaLowerSegment.join cell3198050560 cell3198181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3198312704 cell3198443776)
                  (ThetaLowerSegment.join cell3198574848 cell3198705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3198836992 cell3198968064)
                  (ThetaLowerSegment.join cell3199099136 cell3199230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3199361280 cell3199492352)
                  (ThetaLowerSegment.join cell3199623424 cell3199754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3199885568 cell3200016640)
                  (ThetaLowerSegment.join cell3200147712 cell3200278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3200409856 cell3200540928)
                  (ThetaLowerSegment.join cell3200672000 cell3200803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3200934144 cell3201065216)
                  (ThetaLowerSegment.join cell3201196288 cell3201327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3201458432 cell3201589504)
                  (ThetaLowerSegment.join cell3201720576 cell3201851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3201982720 cell3202113792)
                  (ThetaLowerSegment.join cell3202244864 cell3202375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3202507008 cell3202638080)
                  (ThetaLowerSegment.join cell3202769152 cell3202900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3203031296 cell3203162368)
                  (ThetaLowerSegment.join cell3203293440 cell3203424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3203555584 cell3203686656)
                  (ThetaLowerSegment.join cell3203817728 cell3203948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3204079872 cell3204210944)
                  (ThetaLowerSegment.join cell3204342016 cell3204473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3204604160 cell3204735232)
                  (ThetaLowerSegment.join cell3204866304 cell3204997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3205128448 cell3205259520)
                  (ThetaLowerSegment.join cell3205390592 cell3205521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3205652736 cell3205783808)
                  (ThetaLowerSegment.join cell3205914880 cell3206045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3206177024 cell3206308096)
                  (ThetaLowerSegment.join cell3206439168 cell3206570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3206701312 cell3206832384)
                  (ThetaLowerSegment.join cell3206963456 cell3207094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3207225600 cell3207356672)
                  (ThetaLowerSegment.join cell3207487744 cell3207618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3207749888 cell3207880960)
                  (ThetaLowerSegment.join cell3208012032 cell3208143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3208274176 cell3208405248)
                  (ThetaLowerSegment.join cell3208536320 cell3208667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3208798464 cell3208929536)
                (ThetaLowerSegment.join cell3209060608 cell3209191680))
              (ThetaLowerSegment.join cell3209322752 cell3209339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
