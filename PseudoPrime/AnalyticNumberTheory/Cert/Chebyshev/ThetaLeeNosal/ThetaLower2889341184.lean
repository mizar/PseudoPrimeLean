/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2889341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2857341184 :
    ThetaLowerSegment 2857341184 2857472256 (71432156080959 / 25000) (35717721368221 / 12500) := by
  exact
    packedTile65536 2857341184 2857472256 14 6038 53454 31 _ _ (1088657 / 50000) (2177317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857472256 :
    ThetaLowerSegment 2857472256 2857603328 (35717721368221 / 12500)
      (285754902356657 / 100000) := by
  exact
    packedTile65536 2857472256 2857603328 14 6031 53455 31 _ _ (2177319 / 100000) (1088661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857603328 :
    ThetaLowerSegment 2857603328 2857734400 (285754902356657 / 100000)
      (285767857428507 / 100000) := by
  exact
    packedTile65536 2857603328 2857734400 14 5950 53456 31 _ _ (2177323 / 100000) (1088663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857734400 :
    ThetaLowerSegment 2857734400 2857865472 (285767857428507 / 100000)
      (285781049858859 / 100000) := by
  exact
    packedTile65536 2857734400 2857865472 14 6059 53457 31 _ _ (136083 / 6250) (2177331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857865472 :
    ThetaLowerSegment 2857865472 2857996544 (285781049858859 / 100000)
      (285794105147527 / 100000) := by
  exact
    packedTile65536 2857865472 2857996544 14 5996 53459 31 _ _ (2177333 / 100000) (272167 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857996544 :
    ThetaLowerSegment 2857996544 2858127616 (285794105147527 / 100000)
      (142903531240007 / 50000) := by
  exact
    packedTile65536 2857996544 2858127616 14 5951 53460 31 _ _ (2177337 / 100000) (108867 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2858127616 :
    ThetaLowerSegment 2858127616 2858258688 (142903531240007 / 50000)
      (142910045847271 / 50000) := by
  exact
    packedTile65536 2858127616 2858258688 14 5984 53461 31 _ _ (1088671 / 50000) (435469 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2858258688 :
    ThetaLowerSegment 2858258688 2858389760 (142910045847271 / 50000) (357291643396 / 125) := by
  exact
    packedTile65536 2858258688 2858389760 14 6073 53462 31 _ _ (1088673 / 50000) (2177349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2858389760 :
    ThetaLowerSegment 2858389760 2858520832 (357291643396 / 125) (71461623011263 / 25000) := by
  exact
    packedTile65536 2858389760 2858520832 14 6052 53463 31 _ _ (2177351 / 100000) (1088677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2858520832 :
    ThetaLowerSegment 2858520832 2858651904 (71461623011263 / 25000) (8933112423463 / 3125) := by
  exact
    packedTile65536 2858520832 2858651904 14 6019 53465 31 _ _ (544339 / 25000) (2177359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2858651904 :
    ThetaLowerSegment 2858651904 2858782976 (8933112423463 / 3125) (17867043670371 / 6250) := by
  exact
    packedTile65536 2858651904 2858782976 14 6017 53466 31 _ _ (27217 / 1250) (2177363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2858782976 :
    ThetaLowerSegment 2858782976 2858914048 (17867043670371 / 6250) (285885778157491 / 100000) := by
  exact
    packedTile65536 2858782976 2858914048 14 6007 53467 31 _ _ (435473 / 20000) (272171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2858914048 :
    ThetaLowerSegment 2858914048 2859045120 (285885778157491 / 100000)
      (71474706782477 / 25000) := by
  exact
    packedTile65536 2858914048 2859045120 14 5993 53468 31 _ _ (2177369 / 100000) (544343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2859045120 :
    ThetaLowerSegment 2859045120 2859176192 (71474706782477 / 25000) (35738977167899 / 12500) := by
  exact
    packedTile65536 2859045120 2859176192 14 5966 53470 31 _ _ (1088687 / 50000) (2177377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2859176192 :
    ThetaLowerSegment 2859176192 2859307264 (35738977167899 / 12500) (142962457135931 / 50000) := by
  exact
    packedTile65536 2859176192 2859307264 14 6015 53471 31 _ _ (1088689 / 50000) (2177381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2859307264 :
    ThetaLowerSegment 2859307264 2859438336 (142962457135931 / 50000)
      (142968950092037 / 50000) := by
  exact
    packedTile65536 2859307264 2859438336 14 5964 53472 31 _ _ (2177383 / 100000) (1088693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2859438336 :
    ThetaLowerSegment 2859438336 2859569408 (142968950092037 / 50000) (5719017199949 / 2000) := by
  exact
    packedTile65536 2859438336 2859569408 14 5952 53473 31 _ _ (544347 / 25000) (2177391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2859569408 :
    ThetaLowerSegment 2859569408 2859700480 (5719017199949 / 2000) (142982080842589 / 50000) := by
  exact
    packedTile65536 2859569408 2859700480 14 6109 53474 31 _ _ (136087 / 6250) (435479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2859700480 :
    ThetaLowerSegment 2859700480 2859831552 (142982080842589 / 50000)
      (285977154213077 / 100000) := by
  exact
    packedTile65536 2859700480 2859831552 14 5967 53476 31 _ _ (2177397 / 100000) (10887 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2859831552 :
    ThetaLowerSegment 2859831552 2859962624 (285977154213077 / 100000)
      (285990336198731 / 100000) := by
  exact
    packedTile65536 2859831552 2859962624 14 6054 53477 31 _ _ (2177401 / 100000) (544351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2859962624 :
    ThetaLowerSegment 2859962624 2860093696 (285990336198731 / 100000)
      (286003522569467 / 100000) := by
  exact
    packedTile65536 2859962624 2860093696 14 6056 53478 31 _ _ (1088703 / 50000) (2177409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2860093696 :
    ThetaLowerSegment 2860093696 2860224768 (286003522569467 / 100000)
      (143008259767863 / 50000) := by
  exact
    packedTile65536 2860093696 2860224768 14 5969 53479 31 _ _ (2177411 / 100000) (1088707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2860224768 :
    ThetaLowerSegment 2860224768 2860355840 (143008259767863 / 50000)
      (143014809432183 / 50000) := by
  exact
    packedTile65536 2860224768 2860355840 14 6016 53481 31 _ _ (435483 / 20000) (1088709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2860355840 :
    ThetaLowerSegment 2860355840 2860486912 (143014809432183 / 50000)
      (143021366732513 / 50000) := by
  exact
    packedTile65536 2860355840 2860486912 14 6023 53482 31 _ _ (108871 / 5000) (2177423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2860486912 :
    ThetaLowerSegment 2860486912 2860617984 (143021366732513 / 50000) (28605584373493 / 10000) := by
  exact
    packedTile65536 2860486912 2860617984 14 6021 53483 31 _ _ (136089 / 6250) (2177427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2860617984 :
    ThetaLowerSegment 2860617984 2860749056 (28605584373493 / 10000)
      (286068927905791 / 100000) := by
  exact
    packedTile65536 2860617984 2860749056 14 6009 53484 31 _ _ (2177429 / 100000) (272179 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2860749056 :
    ThetaLowerSegment 2860749056 2860880128 (286068927905791 / 100000)
      (143041016937509 / 50000) := by
  exact
    packedTile65536 2860749056 2860880128 14 6019 53485 31 _ _ (2177433 / 100000) (544359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2860880128 :
    ThetaLowerSegment 2860880128 2861011200 (143041016937509 / 50000) (14304761348593 / 5000) := by
  exact
    packedTile65536 2860880128 2861011200 14 6059 53487 31 _ _ (1088719 / 50000) (2177441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2861011200 :
    ThetaLowerSegment 2861011200 2861142272 (14304761348593 / 5000) (286108511551603 / 100000) := by
  exact
    packedTile65536 2861011200 2861142272 14 6101 53488 31 _ _ (2177443 / 100000) (1088723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2861142272 :
    ThetaLowerSegment 2861142272 2861273344 (286108511551603 / 100000) (1430608436417 / 500) := by
  exact
    packedTile65536 2861142272 2861273344 14 6051 53489 31 _ _ (2177447 / 100000) (43549 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2861273344 :
    ThetaLowerSegment 2861273344 2861404416 (1430608436417 / 500) (71533774552567 / 25000) := by
  exact
    packedTile65536 2861273344 2861404416 14 6159 53490 31 _ _ (544363 / 25000) (435491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2861404416 :
    ThetaLowerSegment 2861404416 2861535488 (71533774552567 / 25000) (71537000453631 / 25000) := by
  exact
    packedTile65536 2861404416 2861535488 14 5926 53492 31 _ _ (136091 / 6250) (2177459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2861535488 :
    ThetaLowerSegment 2861535488 2861666560 (71537000453631 / 25000) (17885086802797 / 6250) := by
  exact
    packedTile65536 2861535488 2861666560 14 6148 53493 31 _ _ (2177461 / 100000) (272183 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2861666560 :
    ThetaLowerSegment 2861666560 2861797632 (17885086802797 / 6250) (71543573127067 / 25000) := by
  exact
    packedTile65536 2861666560 2861797632 14 5926 53494 31 _ _ (1088733 / 50000) (2177469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2861797632 :
    ThetaLowerSegment 2861797632 2861928704 (71543573127067 / 25000) (71546880703997 / 25000) := by
  exact
    packedTile65536 2861797632 2861928704 14 6076 53495 31 _ _ (217747 / 10000) (2177473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2861928704 :
    ThetaLowerSegment 2861928704 2862059776 (71546880703997 / 25000) (35775054949711 / 12500) := by
  exact
    packedTile65536 2861928704 2862059776 14 5932 53496 31 _ _ (87099 / 4000) (1088739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2862059776 :
    ThetaLowerSegment 2862059776 2862190848 (35775054949711 / 12500) (35776714188709 / 12500) := by
  exact
    packedTile65536 2862059776 2862190848 14 6096 53498 31 _ _ (2177479 / 100000) (1088741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2862190848 :
    ThetaLowerSegment 2862190848 2862321920 (35776714188709 / 12500) (1431134893711 / 500) := by
  exact
    packedTile65536 2862190848 2862321920 14 6092 53499 31 _ _ (544371 / 25000) (2177487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2862321920 :
    ThetaLowerSegment 2862321920 2862452992 (1431134893711 / 500) (35780010358123 / 12500) := by
  exact
    packedTile65536 2862321920 2862452992 14 6018 53500 31 _ _ (136093 / 6250) (2177491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2862452992 :
    ThetaLowerSegment 2862452992 2862584064 (35780010358123 / 12500)
      (286253058545771 / 100000) := by
  exact
    packedTile65536 2862452992 2862584064 14 5959 53501 31 _ _ (2177493 / 100000) (272187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2862584064 :
    ThetaLowerSegment 2862584064 2862715136 (286253058545771 / 100000)
      (286266373946041 / 100000) := by
  exact
    packedTile65536 2862584064 2862715136 14 6115 53503 31 _ _ (1088749 / 50000) (2177501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2862715136 :
    ThetaLowerSegment 2862715136 2862846208 (286266373946041 / 100000)
      (286279397585503 / 100000) := by
  exact
    packedTile65536 2862715136 2862846208 14 5981 53504 31 _ _ (1088751 / 50000) (435501 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2862846208 :
    ThetaLowerSegment 2862846208 2862977280 (286279397585503 / 100000)
      (286292331977083 / 100000) := by
  exact
    packedTile65536 2862846208 2862977280 14 5940 53505 31 _ _ (2177507 / 100000) (217751 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2862977280 :
    ThetaLowerSegment 2862977280 2863108352 (286292331977083 / 100000)
      (143152703965319 / 50000) := by
  exact
    packedTile65536 2862977280 2863108352 14 6005 53506 31 _ _ (2177511 / 100000) (1088757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2863108352 :
    ThetaLowerSegment 2863108352 2863239424 (143152703965319 / 50000)
      (143159308371347 / 50000) := by
  exact
    packedTile65536 2863108352 2863239424 14 6066 53508 31 _ _ (544379 / 25000) (2177519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2863239424 :
    ThetaLowerSegment 2863239424 2863370496 (143159308371347 / 50000)
      (143165889925547 / 50000) := by
  exact
    packedTile65536 2863239424 2863370496 14 6045 53509 31 _ _ (27219 / 1250) (2177523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2863370496 :
    ThetaLowerSegment 2863370496 2863501568 (143165889925547 / 50000)
      (286344733947319 / 100000) := by
  exact
    packedTile65536 2863370496 2863501568 14 5949 53510 31 _ _ (87101 / 4000) (272191 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2863501568 :
    ThetaLowerSegment 2863501568 2863632640 (286344733947319 / 100000)
      (286357840500389 / 100000) := by
  exact
    packedTile65536 2863501568 2863632640 14 6019 53511 31 _ _ (217753 / 10000) (2177533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2863632640 :
    ThetaLowerSegment 2863632640 2863763712 (286357840500389 / 100000)
      (57274198125643 / 20000) := by
  exact
    packedTile65536 2863632640 2863763712 14 6039 53512 31 _ _ (1088767 / 50000) (2177537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2863763712 :
    ThetaLowerSegment 2863763712 2863894784 (57274198125643 / 20000) (143191959338629 / 50000) := by
  exact
    packedTile65536 2863763712 2863894784 14 5937 53514 31 _ _ (2177539 / 100000) (1088771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2863894784 :
    ThetaLowerSegment 2863894784 2864025856 (143191959338629 / 50000) (35799614826121 / 12500) := by
  exact
    packedTile65536 2863894784 2864025856 14 5970 53515 31 _ _ (2177543 / 100000) (1088773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864025856 :
    ThetaLowerSegment 2864025856 2864156928 (35799614826121 / 12500) (71602498696177 / 25000) := by
  exact
    packedTile65536 2864025856 2864156928 14 6005 53516 31 _ _ (544387 / 25000) (2177551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864156928 :
    ThetaLowerSegment 2864156928 2864288000 (71602498696177 / 25000) (71605772101221 / 25000) := by
  exact
    packedTile65536 2864156928 2864288000 14 6013 53517 31 _ _ (136097 / 6250) (435511 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864288000 :
    ThetaLowerSegment 2864288000 2864419072 (71605772101221 / 25000) (143218166153279 / 50000) := by
  exact
    packedTile65536 2864288000 2864419072 14 6082 53519 31 _ _ (2177557 / 100000) (54439 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864419072 :
    ThetaLowerSegment 2864419072 2864550144 (143218166153279 / 50000) (35806194580073 / 12500) := by
  exact
    packedTile65536 2864419072 2864550144 14 6073 53520 31 _ _ (1088781 / 50000) (435513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864550144 :
    ThetaLowerSegment 2864550144 2864681216 (35806194580073 / 12500) (28646249356019 / 10000) := by
  exact
    packedTile65536 2864550144 2864681216 14 5941 53521 31 _ _ (1088783 / 50000) (2177569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864681216 :
    ThetaLowerSegment 2864681216 2864812288 (28646249356019 / 10000) (8952368159326 / 3125) := by
  exact
    packedTile65536 2864681216 2864812288 14 6102 53522 31 _ _ (2177571 / 100000) (1088787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864812288 :
    ThetaLowerSegment 2864812288 2864943360 (8952368159326 / 3125) (286488896632657 / 100000) := by
  exact
    packedTile65536 2864812288 2864943360 14 6023 53523 31 _ _ (87103 / 4000) (1088789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864943360 :
    ThetaLowerSegment 2864943360 2865074432 (286488896632657 / 100000)
      (286501935981697 / 100000) := by
  exact
    packedTile65536 2864943360 2865074432 14 5988 53525 31 _ _ (108879 / 5000) (2177583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2865074432 :
    ThetaLowerSegment 2865074432 2865205504 (286501935981697 / 100000)
      (71628760716453 / 25000) := by
  exact
    packedTile65536 2865074432 2865205504 14 6019 53526 31 _ _ (435517 / 20000) (544397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2865205504 :
    ThetaLowerSegment 2865205504 2865336576 (71628760716453 / 25000)
      (286528219456851 / 100000) := by
  exact
    packedTile65536 2865205504 2865336576 14 6051 53527 31 _ _ (2177589 / 100000) (272199 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2865336576 :
    ThetaLowerSegment 2865336576 2865467648 (286528219456851 / 100000)
      (286541324217543 / 100000) := by
  exact
    packedTile65536 2865336576 2865467648 14 6018 53528 31 _ _ (1088797 / 50000) (2177597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2865467648 :
    ThetaLowerSegment 2865467648 2865598720 (286541324217543 / 100000)
      (57310908011961 / 20000) := by
  exact
    packedTile65536 2865467648 2865598720 14 6069 53530 31 _ _ (1088799 / 50000) (2177601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2865598720 :
    ThetaLowerSegment 2865598720 2865729792 (57310908011961 / 20000) (57313534201179 / 20000) := by
  exact
    packedTile65536 2865598720 2865729792 14 6030 53531 31 _ _ (2177603 / 100000) (1088803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2865729792 :
    ThetaLowerSegment 2865729792 2865860864 (57313534201179 / 20000) (71645207571249 / 25000) := by
  exact
    packedTile65536 2865729792 2865860864 14 6043 53532 31 _ _ (2177607 / 100000) (217761 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2865860864 :
    ThetaLowerSegment 2865860864 2865991936 (71645207571249 / 25000) (35824261764961 / 12500) := by
  exact
    packedTile65536 2865860864 2865991936 14 6091 53533 31 _ _ (544403 / 25000) (435523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2865991936 :
    ThetaLowerSegment 2865991936 2866123008 (35824261764961 / 12500) (17912942044813 / 6250) := by
  exact
    packedTile65536 2865991936 2866123008 14 5960 53534 31 _ _ (2177617 / 100000) (108881 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2866123008 :
    ThetaLowerSegment 2866123008 2866254080 (17912942044813 / 6250) (286620271277889 / 100000) := by
  exact
    packedTile65536 2866123008 2866254080 14 6061 53536 31 _ _ (2177621 / 100000) (272203 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2866254080 :
    ThetaLowerSegment 2866254080 2866385152 (286620271277889 / 100000)
      (286633358810149 / 100000) := by
  exact
    packedTile65536 2866254080 2866385152 14 6010 53537 31 _ _ (1088813 / 50000) (2177629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2866385152 :
    ThetaLowerSegment 2866385152 2866516224 (286633358810149 / 100000)
      (286646326596799 / 100000) := by
  exact
    packedTile65536 2866385152 2866516224 14 5955 53538 31 _ _ (217763 / 10000) (2177633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2866516224 :
    ThetaLowerSegment 2866516224 2866647296 (286646326596799 / 100000)
      (71664873688911 / 25000) := by
  exact
    packedTile65536 2866516224 2866647296 14 6047 53539 31 _ _ (435527 / 20000) (1088819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2866647296 :
    ThetaLowerSegment 2866647296 2866778368 (71664873688911 / 25000)
      (286672527925059 / 100000) := by
  exact
    packedTile65536 2866647296 2866778368 14 5985 53541 31 _ _ (2177639 / 100000) (1088821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2866778368 :
    ThetaLowerSegment 2866778368 2866909440 (286672527925059 / 100000)
      (57337096545843 / 20000) := by
  exact
    packedTile65536 2866778368 2866909440 14 5949 53542 31 _ _ (544411 / 25000) (2177647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2866909440 :
    ThetaLowerSegment 2866909440 2867040512 (57337096545843 / 20000) (35837329738353 / 12500) := by
  exact
    packedTile65536 2866909440 2867040512 14 6041 53543 31 _ _ (2177649 / 100000) (544413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2867040512 :
    ThetaLowerSegment 2867040512 2867171584 (35837329738353 / 12500) (8959739111286 / 3125) := by
  exact
    packedTile65536 2867040512 2867171584 14 5976 53544 31 _ _ (2177653 / 100000) (272207 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2867171584 :
    ThetaLowerSegment 2867171584 2867302656 (8959739111286 / 3125) (17920295933151 / 6250) := by
  exact
    packedTile65536 2867171584 2867302656 14 6008 53545 31 _ _ (1088829 / 50000) (2177661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2867302656 :
    ThetaLowerSegment 2867302656 2867433728 (17920295933151 / 6250) (573475523409 / 200) := by
  exact
    packedTile65536 2867302656 2867433728 14 5982 53547 31 _ _ (1088831 / 50000) (435533 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2867433728 :
    ThetaLowerSegment 2867433728 2867564800 (573475523409 / 200) (286750856016171 / 100000) := by
  exact
    packedTile65536 2867433728 2867564800 14 6013 53548 31 _ _ (2177667 / 100000) (217767 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2867564800 :
    ThetaLowerSegment 2867564800 2867695872 (286750856016171 / 100000)
      (286763961240249 / 100000) := by
  exact
    packedTile65536 2867564800 2867695872 14 6018 53549 31 _ _ (2177671 / 100000) (1088837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2867695872 :
    ThetaLowerSegment 2867695872 2867826944 (286763961240249 / 100000)
      (286777308216453 / 100000) := by
  exact
    packedTile65536 2867695872 2867826944 14 6129 53550 31 _ _ (544419 / 25000) (2177679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2867826944 :
    ThetaLowerSegment 2867826944 2867958016 (286777308216453 / 100000)
      (286790500607951 / 100000) := by
  exact
    packedTile65536 2867826944 2867958016 14 6058 53552 31 _ _ (2177681 / 100000) (544421 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2867958016 :
    ThetaLowerSegment 2867958016 2868089088 (286790500607951 / 100000)
      (286803662536091 / 100000) := by
  exact
    packedTile65536 2867958016 2868089088 14 6044 53553 31 _ _ (435537 / 20000) (272211 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2868089088 :
    ThetaLowerSegment 2868089088 2868220160 (286803662536091 / 100000)
      (286816706899191 / 100000) := by
  exact
    packedTile65536 2868089088 2868220160 14 5990 53554 31 _ _ (217769 / 10000) (2177693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2868220160 :
    ThetaLowerSegment 2868220160 2868351232 (286816706899191 / 100000)
      (286829696843901 / 100000) := by
  exact
    packedTile65536 2868220160 2868351232 14 5965 53555 31 _ _ (1088847 / 50000) (2177697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2868351232 :
    ThetaLowerSegment 2868351232 2868482304 (286829696843901 / 100000) (17927681536771 / 6250) := by
  exact
    packedTile65536 2868351232 2868482304 14 6065 53556 31 _ _ (2177699 / 100000) (1088851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2868482304 :
    ThetaLowerSegment 2868482304 2868613376 (17927681536771 / 6250) (143427970159247 / 50000) := by
  exact
    packedTile65536 2868482304 2868613376 14 5986 53558 31 _ _ (2177703 / 100000) (1088853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2868613376 :
    ThetaLowerSegment 2868613376 2868744448 (143427970159247 / 50000) (28686893470213 / 10000) := by
  exact
    packedTile65536 2868613376 2868744448 14 5967 53559 31 _ _ (544427 / 25000) (2177711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2868744448 :
    ThetaLowerSegment 2868744448 2868875520 (28686893470213 / 10000) (143441052755177 / 50000) := by
  exact
    packedTile65536 2868744448 2868875520 14 6048 53560 31 _ _ (2177713 / 100000) (544429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2868875520 :
    ThetaLowerSegment 2868875520 2869006592 (143441052755177 / 50000) (35861908998417 / 12500) := by
  exact
    packedTile65536 2868875520 2869006592 14 6046 53561 31 _ _ (2177717 / 100000) (54443 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2869006592 :
    ThetaLowerSegment 2869006592 2869137664 (35861908998417 / 12500) (35863557533971 / 12500) := by
  exact
    packedTile65536 2869006592 2869137664 14 6056 53563 31 _ _ (1088861 / 50000) (87109 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2869137664 :
    ThetaLowerSegment 2869137664 2869268736 (35863557533971 / 12500) (143460773113651 / 50000) := by
  exact
    packedTile65536 2869137664 2869268736 14 6009 53564 31 _ _ (1088863 / 50000) (2177729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2869268736 :
    ThetaLowerSegment 2869268736 2869399808 (143460773113651 / 50000) (71733697796811 / 25000) := by
  exact
    packedTile65536 2869268736 2869399808 14 6082 53565 31 _ _ (2177731 / 100000) (1088867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2869399808 :
    ThetaLowerSegment 2869399808 2869530880 (71733697796811 / 25000) (143473878710717 / 50000) := by
  exact
    packedTile65536 2869399808 2869530880 14 5954 53566 31 _ _ (435547 / 20000) (1088869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2869530880 :
    ThetaLowerSegment 2869530880 2869661952 (143473878710717 / 50000)
      (143480489240487 / 50000) := by
  exact
    packedTile65536 2869530880 2869661952 14 6071 53568 31 _ _ (108887 / 5000) (2177743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2869661952 :
    ThetaLowerSegment 2869661952 2869793024 (143480489240487 / 50000)
      (286974034062249 / 100000) := by
  exact
    packedTile65536 2869661952 2869793024 14 5995 53569 31 _ _ (435549 / 20000) (544437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2869793024 :
    ThetaLowerSegment 2869793024 2869924096 (286974034062249 / 100000)
      (35873375319693 / 12500) := by
  exact
    packedTile65536 2869793024 2869924096 14 5955 53570 31 _ _ (2177749 / 100000) (272219 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2869924096 :
    ThetaLowerSegment 2869924096 2870055168 (35873375319693 / 12500) (28700011045887 / 10000) := by
  exact
    packedTile65536 2869924096 2870055168 14 6019 53571 31 _ _ (1088877 / 50000) (2177757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2870055168 :
    ThetaLowerSegment 2870055168 2870186240 (28700011045887 / 10000) (14350665928057 / 5000) := by
  exact
    packedTile65536 2870055168 2870186240 14 6065 53572 31 _ _ (1088879 / 50000) (2177761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2870186240 :
    ThetaLowerSegment 2870186240 2870317312 (14350665928057 / 5000) (287026443938741 / 100000) := by
  exact
    packedTile65536 2870186240 2870317312 14 6027 53574 31 _ _ (2177763 / 100000) (1088883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2870317312 :
    ThetaLowerSegment 2870317312 2870448384 (287026443938741 / 100000)
      (71759904312831 / 25000) := by
  exact
    packedTile65536 2870317312 2870448384 14 6049 53575 31 _ _ (2177767 / 100000) (217777 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2870448384 :
    ThetaLowerSegment 2870448384 2870579456 (71759904312831 / 25000) (71763196015209 / 25000) := by
  exact
    packedTile65536 2870448384 2870579456 14 6046 53576 31 _ _ (544443 / 25000) (87111 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2870579456 :
    ThetaLowerSegment 2870579456 2870710528 (71763196015209 / 25000) (71766435457009 / 25000) := by
  exact
    packedTile65536 2870579456 2870710528 14 5950 53577 31 _ _ (136111 / 6250) (2177779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2870710528 :
    ThetaLowerSegment 2870710528 2870841600 (71766435457009 / 25000)
      (287078880380809 / 100000) := by
  exact
    packedTile65536 2870710528 2870841600 14 6033 53579 31 _ _ (2177781 / 100000) (272223 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2870841600 :
    ThetaLowerSegment 2870841600 2870972672 (287078880380809 / 100000)
      (287091936207879 / 100000) := by
  exact
    packedTile65536 2870841600 2870972672 14 5995 53580 31 _ _ (1088893 / 50000) (2177789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2870972672 :
    ThetaLowerSegment 2870972672 2871103744 (287091936207879 / 100000)
      (287105092237269 / 100000) := by
  exact
    packedTile65536 2870972672 2871103744 14 6041 53581 31 _ _ (217779 / 10000) (2177793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2871103744 :
    ThetaLowerSegment 2871103744 2871234816 (287105092237269 / 100000)
      (287118193851989 / 100000) := by
  exact
    packedTile65536 2871103744 2871234816 14 6016 53582 31 _ _ (435559 / 20000) (1088899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2871234816 :
    ThetaLowerSegment 2871234816 2871365888 (287118193851989 / 100000)
      (28713117135623 / 10000) := by
  exact
    packedTile65536 2871234816 2871365888 14 5959 53583 31 _ _ (2177799 / 100000) (1088901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2871365888 :
    ThetaLowerSegment 2871365888 2871496960 (28713117135623 / 10000) (143572131068037 / 50000) := by
  exact
    packedTile65536 2871365888 2871496960 14 6011 53585 31 _ _ (544451 / 25000) (2177807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2871496960 :
    ThetaLowerSegment 2871496960 2871628032 (143572131068037 / 50000)
      (143578700425869 / 50000) := by
  exact
    packedTile65536 2871496960 2871628032 14 6033 53586 31 _ _ (136113 / 6250) (2177811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2871628032 :
    ThetaLowerSegment 2871628032 2871759104 (143578700425869 / 50000)
      (287170635421339 / 100000) := by
  exact
    packedTile65536 2871628032 2871759104 14 6077 53587 31 _ _ (2177813 / 100000) (272227 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2871759104 :
    ThetaLowerSegment 2871759104 2871890176 (287170635421339 / 100000)
      (287183846065327 / 100000) := by
  exact
    packedTile65536 2871759104 2871890176 14 6066 53588 31 _ _ (1088909 / 50000) (2177821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2871890176 :
    ThetaLowerSegment 2871890176 2872021248 (287183846065327 / 100000)
      (287197026244071 / 100000) := by
  exact
    packedTile65536 2871890176 2872021248 14 6052 53590 31 _ _ (1088911 / 50000) (87113 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872021248 :
    ThetaLowerSegment 2872021248 2872152320 (287197026244071 / 100000)
      (287210106273033 / 100000) := by
  exact
    packedTile65536 2872021248 2872152320 14 6006 53591 31 _ _ (2177827 / 100000) (217783 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872152320 :
    ThetaLowerSegment 2872152320 2872283392 (287210106273033 / 100000)
      (287223277794921 / 100000) := by
  exact
    packedTile65536 2872152320 2872283392 14 6048 53592 31 _ _ (2177831 / 100000) (1088917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872283392 :
    ThetaLowerSegment 2872283392 2872414464 (287223277794921 / 100000)
      (287236305609873 / 100000) := by
  exact
    packedTile65536 2872283392 2872414464 14 5982 53593 31 _ _ (544459 / 25000) (2177839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872414464 :
    ThetaLowerSegment 2872414464 2872545536 (287236305609873 / 100000)
      (287249337804433 / 100000) := by
  exact
    packedTile65536 2872414464 2872545536 14 5984 53594 31 _ _ (27223 / 1250) (2177843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872545536 :
    ThetaLowerSegment 2872545536 2872676608 (287249337804433 / 100000)
      (287262444075643 / 100000) := by
  exact
    packedTile65536 2872545536 2872676608 14 6018 53596 31 _ _ (435569 / 20000) (272231 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872676608 :
    ThetaLowerSegment 2872676608 2872807680 (287262444075643 / 100000)
      (287275615712443 / 100000) := by
  exact
    packedTile65536 2872676608 2872807680 14 6048 53597 31 _ _ (43557 / 2000) (2177853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872807680 :
    ThetaLowerSegment 2872807680 2872938752 (287275615712443 / 100000) (11491548010371 / 4000) := by
  exact
    packedTile65536 2872807680 2872938752 14 6008 53598 31 _ _ (1088927 / 50000) (2177857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872938752 :
    ThetaLowerSegment 2872938752 2873069824 (11491548010371 / 4000) (28730173474539 / 10000) := by
  exact
    packedTile65536 2872938752 2873069824 14 5985 53599 31 _ _ (2177859 / 100000) (1088931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2873069824 :
    ThetaLowerSegment 2873069824 2873200896 (28730173474539 / 10000) (35914343162369 / 12500) := by
  exact
    packedTile65536 2873069824 2873200896 14 5974 53601 31 _ _ (2177863 / 100000) (1088933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2873200896 :
    ThetaLowerSegment 2873200896 2873331968 (35914343162369 / 12500) (71831922092119 / 25000) := by
  exact
    packedTile65536 2873200896 2873331968 14 5943 53602 31 _ _ (544467 / 25000) (2177871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2873331968 :
    ThetaLowerSegment 2873331968 2873463040 (71831922092119 / 25000) (71835166576931 / 25000) := by
  exact
    packedTile65536 2873331968 2873463040 14 5959 53603 31 _ _ (136117 / 6250) (17423 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2873463040 :
    ThetaLowerSegment 2873463040 2873594112 (71835166576931 / 25000) (35919237386047 / 12500) := by
  exact
    packedTile65536 2873463040 2873594112 14 6076 53604 31 _ _ (2177877 / 100000) (54447 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2873594112 :
    ThetaLowerSegment 2873594112 2873725184 (35919237386047 / 12500) (143683424384401 / 50000) := by
  exact
    packedTile65536 2873594112 2873725184 14 5946 53605 31 _ _ (2177881 / 100000) (544471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2873725184 :
    ThetaLowerSegment 2873725184 2873856256 (143683424384401 / 50000)
      (143690101782877 / 50000) := by
  exact
    packedTile65536 2873725184 2873856256 14 6132 53607 31 _ _ (1088943 / 50000) (2177889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2873856256 :
    ThetaLowerSegment 2873856256 2873987328 (143690101782877 / 50000) (14369672910519 / 5000) := by
  exact
    packedTile65536 2873856256 2873987328 14 6086 53608 31 _ _ (2177891 / 100000) (1088947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2873987328 :
    ThetaLowerSegment 2873987328 2874118400 (14369672910519 / 5000) (57481367403873 / 20000) := by
  exact
    packedTile65536 2873987328 2874118400 14 6143 53609 31 _ _ (435579 / 20000) (1088949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2874118400 :
    ThetaLowerSegment 2874118400 2874249472 (57481367403873 / 20000) (57484000484973 / 20000) := by
  exact
    packedTile65536 2874118400 2874249472 14 6045 53610 31 _ _ (21779 / 1000) (2177903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2874249472 :
    ThetaLowerSegment 2874249472 2874380544 (57484000484973 / 20000)
      (287433043714017 / 100000) := by
  exact
    packedTile65536 2874249472 2874380544 14 5988 53612 31 _ _ (136119 / 6250) (2177907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2874380544 :
    ThetaLowerSegment 2874380544 2874511616 (287433043714017 / 100000)
      (287446111168017 / 100000) := by
  exact
    packedTile65536 2874380544 2874511616 14 6000 53613 31 _ _ (2177909 / 100000) (272239 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2874511616 :
    ThetaLowerSegment 2874511616 2874642688 (287446111168017 / 100000)
      (143729555565357 / 50000) := by
  exact
    packedTile65536 2874511616 2874642688 14 5969 53614 31 _ _ (2177913 / 100000) (544479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2874642688 :
    ThetaLowerSegment 2874642688 2874773760 (143729555565357 / 50000)
      (143736176436077 / 50000) := by
  exact
    packedTile65536 2874642688 2874773760 14 6080 53615 31 _ _ (1088959 / 50000) (2177921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2874773760 :
    ThetaLowerSegment 2874773760 2874904832 (143736176436077 / 50000) (28748532893143 / 10000) := by
  exact
    packedTile65536 2874773760 2874904832 14 5958 53616 31 _ _ (1088961 / 50000) (87117 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2874904832 :
    ThetaLowerSegment 2874904832 2875035904 (28748532893143 / 10000) (28749826581781 / 10000) := by
  exact
    packedTile65536 2874904832 2875035904 14 5940 53618 31 _ _ (2177927 / 100000) (217793 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2875035904 :
    ThetaLowerSegment 2875035904 2875166976 (28749826581781 / 10000) (143755706996647 / 50000) := by
  exact
    packedTile65536 2875035904 2875166976 14 6037 53619 31 _ _ (544483 / 25000) (435587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2875166976 :
    ThetaLowerSegment 2875166976 2875298048 (143755706996647 / 50000)
      (143762363858031 / 50000) := by
  exact
    packedTile65536 2875166976 2875298048 14 6113 53620 31 _ _ (136121 / 6250) (2177939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2875298048 :
    ThetaLowerSegment 2875298048 2875429120 (143762363858031 / 50000)
      (143768888969267 / 50000) := by
  exact
    packedTile65536 2875298048 2875429120 14 5992 53621 31 _ _ (2177941 / 100000) (272243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2875429120 :
    ThetaLowerSegment 2875429120 2875560192 (143768888969267 / 50000)
      (287550651771429 / 100000) := by
  exact
    packedTile65536 2875429120 2875560192 14 5911 53623 31 _ _ (435589 / 20000) (544487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2875560192 :
    ThetaLowerSegment 2875560192 2875691264 (287550651771429 / 100000)
      (287563789165829 / 100000) := by
  exact
    packedTile65536 2875560192 2875691264 14 6032 53624 31 _ _ (43559 / 2000) (2177953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2875691264 :
    ThetaLowerSegment 2875691264 2875822336 (287563789165829 / 100000)
      (287576948363897 / 100000) := by
  exact
    packedTile65536 2875691264 2875822336 14 6042 53625 31 _ _ (1088977 / 50000) (2177957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2875822336 :
    ThetaLowerSegment 2875822336 2875953408 (287576948363897 / 100000)
      (287590168575027 / 100000) := by
  exact
    packedTile65536 2875822336 2875953408 14 6070 53626 31 _ _ (2177959 / 100000) (1088981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2875953408 :
    ThetaLowerSegment 2875953408 2876084480 (287590168575027 / 100000)
      (287603105681187 / 100000) := by
  exact
    packedTile65536 2875953408 2876084480 14 5940 53627 31 _ _ (544491 / 25000) (2177967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2876084480 :
    ThetaLowerSegment 2876084480 2876215552 (287603105681187 / 100000)
      (287616095082339 / 100000) := by
  exact
    packedTile65536 2876084480 2876215552 14 5964 53629 31 _ _ (136123 / 6250) (2177971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2876215552 :
    ThetaLowerSegment 2876215552 2876346624 (287616095082339 / 100000) (2301034732113 / 800) := by
  exact
    packedTile65536 2876215552 2876346624 14 6082 53630 31 _ _ (2177973 / 100000) (272247 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2876346624 :
    ThetaLowerSegment 2876346624 2876477696 (2301034732113 / 800) (5752849276511 / 2000) := by
  exact
    packedTile65536 2876346624 2876477696 14 6025 53631 31 _ _ (2177977 / 100000) (108899 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2876477696 :
    ThetaLowerSegment 2876477696 2876608768 (5752849276511 / 2000) (143827813774379 / 50000) := by
  exact
    packedTile65536 2876477696 2876608768 14 6044 53632 31 _ _ (1088991 / 50000) (435597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2876608768 :
    ThetaLowerSegment 2876608768 2876739840 (143827813774379 / 50000) (1797928761321 / 625) := by
  exact
    packedTile65536 2876608768 2876739840 14 5957 53634 31 _ _ (1088993 / 50000) (2177989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2876739840 :
    ThetaLowerSegment 2876739840 2876870912 (1797928761321 / 625) (287681698071243 / 100000) := by
  exact
    packedTile65536 2876739840 2876870912 14 6013 53635 31 _ _ (2177991 / 100000) (1088997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2876870912 :
    ThetaLowerSegment 2876870912 2877001984 (287681698071243 / 100000)
      (287694857517033 / 100000) := by
  exact
    packedTile65536 2876870912 2877001984 14 6042 53636 31 _ _ (435599 / 20000) (1088999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2877001984 :
    ThetaLowerSegment 2877001984 2877133056 (287694857517033 / 100000)
      (287708136783033 / 100000) := by
  exact
    packedTile65536 2877001984 2877133056 14 6097 53637 31 _ _ (1089 / 50) (2178003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2877133056 :
    ThetaLowerSegment 2877133056 2877264128 (287708136783033 / 100000)
      (287721047996673 / 100000) := by
  exact
    packedTile65536 2877133056 2877264128 14 5928 53638 31 _ _ (435601 / 20000) (272251 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2877264128 :
    ThetaLowerSegment 2877264128 2877395200 (287721047996673 / 100000)
      (57546822338931 / 20000) := by
  exact
    packedTile65536 2877264128 2877395200 14 5998 53640 31 _ _ (2178009 / 100000) (544503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2877395200 :
    ThetaLowerSegment 2877395200 2877526272 (57546822338931 / 20000)
      (287747031673703 / 100000) := by
  exact
    packedTile65536 2877395200 2877526272 14 5932 53641 31 _ _ (1089007 / 50000) (2178017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2877526272 :
    ThetaLowerSegment 2877526272 2877657344 (287747031673703 / 100000)
      (57552008630647 / 20000) := by
  exact
    packedTile65536 2877526272 2877657344 14 5974 53642 31 _ _ (1089009 / 50000) (2178021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2877657344 :
    ThetaLowerSegment 2877657344 2877788416 (57552008630647 / 20000)
      (287773215836339 / 100000) := by
  exact
    packedTile65536 2877657344 2877788416 14 6048 53643 31 _ _ (2178023 / 100000) (1089013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2877788416 :
    ThetaLowerSegment 2877788416 2877919488 (287773215836339 / 100000)
      (71946607481537 / 25000) := by
  exact
    packedTile65536 2877788416 2877919488 14 6067 53645 31 _ _ (2178027 / 100000) (217803 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2877919488 :
    ThetaLowerSegment 2877919488 2878050560 (71946607481537 / 25000) (71949865272901 / 25000) := by
  exact
    packedTile65536 2877919488 2878050560 14 5983 53646 31 _ _ (136127 / 6250) (435607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2878050560 :
    ThetaLowerSegment 2878050560 2878181632 (71949865272901 / 25000) (7195317643213 / 2500) := by
  exact
    packedTile65536 2878050560 2878181632 14 6081 53647 31 _ _ (544509 / 25000) (2178039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2878181632 :
    ThetaLowerSegment 2878181632 2878312704 (7195317643213 / 2500) (57565161329027 / 20000) := by
  exact
    packedTile65536 2878181632 2878312704 14 6015 53648 31 _ _ (2178041 / 100000) (544511 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2878312704 :
    ThetaLowerSegment 2878312704 2878443776 (57565161329027 / 20000)
      (287838905413779 / 100000) := by
  exact
    packedTile65536 2878312704 2878443776 14 6014 53649 31 _ _ (1089023 / 50000) (2178049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2878443776 :
    ThetaLowerSegment 2878443776 2878574848 (287838905413779 / 100000)
      (287851901838129 / 100000) := by
  exact
    packedTile65536 2878443776 2878574848 14 5967 53651 31 _ _ (43561 / 2000) (2178053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2878574848 :
    ThetaLowerSegment 2878574848 2878705920 (287851901838129 / 100000)
      (287865214110289 / 100000) := by
  exact
    packedTile65536 2878574848 2878705920 14 6112 53652 31 _ _ (435611 / 20000) (1089029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2878705920 :
    ThetaLowerSegment 2878705920 2878836992 (287865214110289 / 100000) (17992398779809 / 6250) := by
  exact
    packedTile65536 2878705920 2878836992 14 6045 53653 31 _ _ (2178059 / 100000) (1089031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2878836992 :
    ThetaLowerSegment 2878836992 2878968064 (17992398779809 / 6250) (8996610975936 / 3125) := by
  exact
    packedTile65536 2878836992 2878968064 14 6047 53654 31 _ _ (136129 / 6250) (2178067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2878968064 :
    ThetaLowerSegment 2878968064 2879099136 (8996610975936 / 3125) (71976124961053 / 25000) := by
  exact
    packedTile65536 2878968064 2879099136 14 5945 53656 31 _ _ (544517 / 25000) (2178071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2879099136 :
    ThetaLowerSegment 2879099136 2879230208 (71976124961053 / 25000) (143958795031471 / 50000) := by
  exact
    packedTile65536 2879099136 2879230208 14 6010 53657 31 _ _ (2178073 / 100000) (544519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2879230208 :
    ThetaLowerSegment 2879230208 2879361280 (143958795031471 / 50000)
      (143965316194009 / 50000) := by
  exact
    packedTile65536 2879230208 2879361280 14 5988 53658 31 _ _ (2178077 / 100000) (13613 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2879361280 :
    ThetaLowerSegment 2879361280 2879492352 (143965316194009 / 50000)
      (143971891823567 / 50000) := by
  exact
    packedTile65536 2879361280 2879492352 14 6038 53659 31 _ _ (1089041 / 50000) (435617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2879492352 :
    ThetaLowerSegment 2879492352 2879623424 (143971891823567 / 50000) (35994612782389 / 12500) := by
  exact
    packedTile65536 2879492352 2879623424 14 6023 53660 31 _ _ (1089043 / 50000) (2178089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2879623424 :
    ThetaLowerSegment 2879623424 2879754496 (35994612782389 / 12500) (143985039854831 / 50000) := by
  exact
    packedTile65536 2879623424 2879754496 14 6050 53662 31 _ _ (2178091 / 100000) (1089047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2879754496 :
    ThetaLowerSegment 2879754496 2879885568 (143985039854831 / 50000) (28798324194379 / 10000) := by
  exact
    packedTile65536 2879754496 2879885568 14 6043 53663 31 _ _ (136131 / 6250) (2178099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2879885568 :
    ThetaLowerSegment 2879885568 2880016640 (28798324194379 / 10000) (28799625173509 / 10000) := by
  exact
    packedTile65536 2879885568 2880016640 14 5973 53664 31 _ _ (21781 / 1000) (2178103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880016640 :
    ThetaLowerSegment 2880016640 2880147712 (28799625173509 / 10000) (57601834015169 / 20000) := by
  exact
    packedTile65536 2880016640 2880147712 14 5931 53665 31 _ _ (435621 / 20000) (544527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880147712 :
    ThetaLowerSegment 2880147712 2880278784 (57601834015169 / 20000)
      (288022417334783 / 100000) := by
  exact
    packedTile65536 2880147712 2880278784 14 6082 53667 31 _ _ (2178109 / 100000) (68066 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880278784 :
    ThetaLowerSegment 2880278784 2880409856 (288022417334783 / 100000)
      (57607102866853 / 20000) := by
  exact
    packedTile65536 2880278784 2880409856 14 6013 53668 31 _ _ (1089057 / 50000) (2178117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880409856 :
    ThetaLowerSegment 2880409856 2880540928 (57607102866853 / 20000)
      (288048480670719 / 100000) := by
  exact
    packedTile65536 2880409856 2880540928 14 5953 53669 31 _ _ (1089059 / 50000) (2178121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880540928 :
    ThetaLowerSegment 2880540928 2880672000 (288048480670719 / 100000)
      (144030758368437 / 50000) := by
  exact
    packedTile65536 2880540928 2880672000 14 5985 53670 31 _ _ (2178123 / 100000) (1089063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880672000 :
    ThetaLowerSegment 2880672000 2880803072 (144030758368437 / 50000) (28807460292389 / 10000) := by
  exact
    packedTile65536 2880672000 2880803072 14 6008 53671 31 _ _ (2178127 / 100000) (217813 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880803072 :
    ThetaLowerSegment 2880803072 2880934144 (28807460292389 / 10000) (28808788952909 / 10000) := by
  exact
    packedTile65536 2880803072 2880934144 14 6100 53673 31 _ _ (544533 / 25000) (435627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880934144 :
    ThetaLowerSegment 2880934144 2881065216 (28808788952909 / 10000) (14405053362897 / 5000) := by
  exact
    packedTile65536 2880934144 2881065216 14 6050 53674 31 _ _ (2178137 / 100000) (108907 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2881065216 :
    ThetaLowerSegment 2881065216 2881196288 (14405053362897 / 5000) (288114199270029 / 100000) := by
  exact
    packedTile65536 2881065216 2881196288 14 6029 53675 31 _ _ (2178141 / 100000) (68067 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2881196288 :
    ThetaLowerSegment 2881196288 2881327360 (288114199270029 / 100000)
      (57625471490003 / 20000) := by
  exact
    packedTile65536 2881196288 2881327360 14 6041 53676 31 _ _ (1089073 / 50000) (2178149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2881327360 :
    ThetaLowerSegment 2881327360 2881458432 (57625471490003 / 20000) (57628109229653 / 20000) := by
  exact
    packedTile65536 2881327360 2881458432 14 6055 53677 31 _ _ (43563 / 2000) (2178153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2881458432 :
    ThetaLowerSegment 2881458432 2881589504 (57628109229653 / 20000) (5763077834079 / 2000) := by
  exact
    packedTile65536 2881458432 2881589504 14 6127 53679 31 _ _ (435631 / 20000) (1089079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2881589504 :
    ThetaLowerSegment 2881589504 2881720576 (5763077834079 / 2000) (7204173471909 / 2500) := by
  exact
    packedTile65536 2881589504 2881720576 14 5990 53680 31 _ _ (2178159 / 100000) (1089081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2881720576 :
    ThetaLowerSegment 2881720576 2881851648 (7204173471909 / 2500) (14409006382969 / 5000) := by
  exact
    packedTile65536 2881720576 2881851648 14 6055 53681 31 _ _ (544541 / 25000) (2178167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2881851648 :
    ThetaLowerSegment 2881851648 2881982720 (14409006382969 / 5000) (72048257237111 / 25000) := by
  exact
    packedTile65536 2881851648 2881982720 14 5923 53682 31 _ _ (272271 / 12500) (2178171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2881982720 :
    ThetaLowerSegment 2881982720 2882113792 (72048257237111 / 25000) (144102950975437 / 50000) := by
  exact
    packedTile65536 2881982720 2882113792 14 5910 53684 31 _ _ (2178173 / 100000) (68068 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2882113792 :
    ThetaLowerSegment 2882113792 2882244864 (144102950975437 / 50000) (72054769980431 / 25000) := by
  exact
    packedTile65536 2882113792 2882244864 14 6050 53685 31 _ _ (2178177 / 100000) (108909 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2882244864 :
    ThetaLowerSegment 2882244864 2882375936 (72054769980431 / 25000) (2882322971301 / 1000) := by
  exact
    packedTile65536 2882244864 2882375936 14 6068 53686 31 _ _ (1089091 / 50000) (435637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2882375936 :
    ThetaLowerSegment 2882375936 2882507008 (2882322971301 / 1000) (288245307441051 / 100000) := by
  exact
    packedTile65536 2882375936 2882507008 14 5973 53687 31 _ _ (2178187 / 100000) (217819 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2882507008 :
    ThetaLowerSegment 2882507008 2882638080 (288245307441051 / 100000)
      (288258106491367 / 100000) := by
  exact
    packedTile65536 2882507008 2882638080 14 5876 53688 31 _ _ (2178191 / 100000) (1089097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2882638080 :
    ThetaLowerSegment 2882638080 2882769152 (288258106491367 / 100000)
      (57654297429879 / 20000) := by
  exact
    packedTile65536 2882638080 2882769152 14 6143 53690 31 _ _ (544549 / 25000) (2178199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2882769152 :
    ThetaLowerSegment 2882769152 2882900224 (57654297429879 / 20000) (57656884695839 / 20000) := by
  exact
    packedTile65536 2882769152 2882900224 14 5939 53691 31 _ _ (10891 / 500) (2178203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2882900224 :
    ThetaLowerSegment 2882900224 2883031296 (57656884695839 / 20000) (1801859669777 / 625) := by
  exact
    packedTile65536 2882900224 2883031296 14 6025 53692 31 _ _ (435641 / 20000) (68069 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2883031296 :
    ThetaLowerSegment 2883031296 2883162368 (1801859669777 / 625) (288310710081307 / 100000) := by
  exact
    packedTile65536 2883031296 2883162368 14 6043 53693 31 _ _ (2178209 / 100000) (544553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2883162368 :
    ThetaLowerSegment 2883162368 2883293440 (288310710081307 / 100000)
      (288323796791019 / 100000) := by
  exact
    packedTile65536 2883162368 2883293440 14 6008 53695 31 _ _ (1089107 / 50000) (2178217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2883293440 :
    ThetaLowerSegment 2883293440 2883424512 (288323796791019 / 100000)
      (288337149267359 / 100000) := by
  exact
    packedTile65536 2883293440 2883424512 14 6130 53696 31 _ _ (1089109 / 50000) (2178221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2883424512 :
    ThetaLowerSegment 2883424512 2883555584 (288337149267359 / 100000)
      (288350414645429 / 100000) := by
  exact
    packedTile65536 2883424512 2883555584 14 6090 53697 31 _ _ (2178223 / 100000) (1089113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2883555584 :
    ThetaLowerSegment 2883555584 2883686656 (288350414645429 / 100000)
      (144181719132331 / 50000) := by
  exact
    packedTile65536 2883555584 2883686656 14 5979 53698 31 _ _ (2178227 / 100000) (217823 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2883686656 :
    ThetaLowerSegment 2883686656 2883817728 (144181719132331 / 50000)
      (144188188481371 / 50000) := by
  exact
    packedTile65536 2883686656 2883817728 14 5940 53699 31 _ _ (272279 / 12500) (435647 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2883817728 :
    ThetaLowerSegment 2883817728 2883948800 (144188188481371 / 50000)
      (288389461632401 / 100000) := by
  exact
    packedTile65536 2883817728 2883948800 14 6007 53701 31 _ _ (2178237 / 100000) (13614 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2883948800 :
    ThetaLowerSegment 2883948800 2884079872 (288389461632401 / 100000)
      (57680503601791 / 20000) := by
  exact
    packedTile65536 2883948800 2884079872 14 5994 53702 31 _ _ (2178241 / 100000) (544561 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884079872 :
    ThetaLowerSegment 2884079872 2884210944 (57680503601791 / 20000)
      (288415692040763 / 100000) := by
  exact
    packedTile65536 2884079872 2884210944 14 6048 53703 31 _ _ (1089123 / 50000) (2178249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884210944 :
    ThetaLowerSegment 2884210944 2884342016 (288415692040763 / 100000)
      (288428709262763 / 100000) := by
  exact
    packedTile65536 2884210944 2884342016 14 5976 53704 31 _ _ (8713 / 400) (2178253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884342016 :
    ThetaLowerSegment 2884342016 2884473088 (288428709262763 / 100000) (18027614850353 / 6250) := by
  exact
    packedTile65536 2884342016 2884473088 14 6027 53706 31 _ _ (435651 / 20000) (1089129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884473088 :
    ThetaLowerSegment 2884473088 2884604160 (18027614850353 / 6250) (288455096668181 / 100000) := by
  exact
    packedTile65536 2884473088 2884604160 14 6087 53707 31 _ _ (2178259 / 100000) (1089131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884604160 :
    ThetaLowerSegment 2884604160 2884735232 (288455096668181 / 100000)
      (288468153182597 / 100000) := by
  exact
    packedTile65536 2884604160 2884735232 14 5994 53708 31 _ _ (272283 / 12500) (2178267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884735232 :
    ThetaLowerSegment 2884735232 2884866304 (288468153182597 / 100000)
      (288481264177689 / 100000) := by
  exact
    packedTile65536 2884735232 2884866304 14 6019 53709 31 _ _ (544567 / 25000) (2178271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884866304 :
    ThetaLowerSegment 2884866304 2884997376 (288481264177689 / 100000)
      (144247150570797 / 50000) := by
  exact
    packedTile65536 2884866304 2884997376 14 5985 53710 31 _ _ (2178273 / 100000) (544569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884997376 :
    ThetaLowerSegment 2884997376 2885128448 (144247150570797 / 50000) (3606339902311 / 1250) := by
  exact
    packedTile65536 2884997376 2885128448 14 5918 53712 31 _ _ (2178277 / 100000) (54457 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2885128448 :
    ThetaLowerSegment 2885128448 2885259520 (3606339902311 / 1250) (72130112302283 / 25000) := by
  exact
    packedTile65536 2885128448 2885259520 14 6086 53713 31 _ _ (1089141 / 50000) (435657 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2885259520 :
    ThetaLowerSegment 2885259520 2885390592 (72130112302283 / 25000) (11541339798799 / 4000) := by
  exact
    packedTile65536 2885259520 2885390592 14 5989 53714 31 _ _ (2178287 / 100000) (217829 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2885390592 :
    ThetaLowerSegment 2885390592 2885521664 (11541339798799 / 4000) (57709330369523 / 20000) := by
  exact
    packedTile65536 2885390592 2885521664 14 6040 53715 31 _ _ (2178291 / 100000) (1089147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2885521664 :
    ThetaLowerSegment 2885521664 2885652736 (57709330369523 / 20000)
      (288559969949359 / 100000) := by
  exact
    packedTile65536 2885521664 2885652736 14 6114 53717 31 _ _ (272287 / 12500) (2178299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2885652736 :
    ThetaLowerSegment 2885652736 2885783808 (288559969949359 / 100000)
      (288573078958759 / 100000) := by
  exact
    packedTile65536 2885652736 2885783808 14 6018 53718 31 _ _ (21783 / 1000) (2178303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2885783808 :
    ThetaLowerSegment 2885783808 2885914880 (288573078958759 / 100000)
      (288586148788759 / 100000) := by
  exact
    packedTile65536 2885783808 2885914880 14 6000 53719 31 _ _ (435661 / 20000) (544577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2885914880 :
    ThetaLowerSegment 2885914880 2886045952 (288586148788759 / 100000) (7214982045343 / 2500) := by
  exact
    packedTile65536 2885914880 2886045952 14 6029 53720 31 _ _ (2178309 / 100000) (272289 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2886045952 :
    ThetaLowerSegment 2886045952 2886177024 (7214982045343 / 2500) (144306172581389 / 50000) := by
  exact
    packedTile65536 2886045952 2886177024 14 5997 53721 31 _ _ (1089157 / 50000) (2178317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2886177024 :
    ThetaLowerSegment 2886177024 2886308096 (144306172581389 / 50000) (72156370649659 / 25000) := by
  exact
    packedTile65536 2886177024 2886308096 14 6031 53723 31 _ _ (1089159 / 50000) (2178321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2886308096 :
    ThetaLowerSegment 2886308096 2886439168 (72156370649659 / 25000)
      (288638445798809 / 100000) := by
  exact
    packedTile65536 2886308096 2886439168 14 5951 53724 31 _ _ (2178323 / 100000) (1089163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2886439168 :
    ThetaLowerSegment 2886439168 2886570240 (288638445798809 / 100000)
      (57730315350793 / 20000) := by
  exact
    packedTile65536 2886439168 2886570240 14 6028 53725 31 _ _ (2178327 / 100000) (217833 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2886570240 :
    ThetaLowerSegment 2886570240 2886701312 (57730315350793 / 20000) (57732944597517 / 20000) := by
  exact
    packedTile65536 2886570240 2886701312 14 6035 53726 31 _ _ (544583 / 25000) (435667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2886701312 :
    ThetaLowerSegment 2886701312 2886832384 (57732944597517 / 20000)
      (288677871429717 / 100000) := by
  exact
    packedTile65536 2886701312 2886832384 14 6036 53728 31 _ _ (2178337 / 100000) (108917 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2886832384 :
    ThetaLowerSegment 2886832384 2886963456 (288677871429717 / 100000) (9021591853043 / 3125) := by
  exact
    packedTile65536 2886832384 2886963456 14 5999 53729 31 _ _ (2178341 / 100000) (272293 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2886963456 :
    ThetaLowerSegment 2886963456 2887094528 (9021591853043 / 3125) (7217604808861 / 2500) := by
  exact
    packedTile65536 2886963456 2887094528 14 6084 53730 31 _ _ (1089173 / 50000) (2178349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2887094528 :
    ThetaLowerSegment 2887094528 2887225600 (7217604808861 / 2500) (1804482509129 / 625) := by
  exact
    packedTile65536 2887094528 2887225600 14 5972 53731 31 _ _ (43567 / 2000) (2178353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2887225600 :
    ThetaLowerSegment 2887225600 2887356672 (1804482509129 / 625) (11549206245513 / 4000) := by
  exact
    packedTile65536 2887225600 2887356672 14 5947 53732 31 _ _ (435671 / 20000) (1089179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2887356672 :
    ThetaLowerSegment 2887356672 2887487744 (11549206245513 / 4000) (144371633840323 / 50000) := by
  exact
    packedTile65536 2887356672 2887487744 14 6019 53734 31 _ _ (2178359 / 100000) (1089181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2887487744 :
    ThetaLowerSegment 2887487744 2887618816 (144371633840323 / 50000)
      (144378204875329 / 50000) := by
  exact
    packedTile65536 2887487744 2887618816 14 6033 53735 31 _ _ (544591 / 25000) (2178367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2887618816 :
    ThetaLowerSegment 2887618816 2887749888 (144378204875329 / 50000) (28876942332109 / 10000) := by
  exact
    packedTile65536 2887618816 2887749888 14 5974 53736 31 _ _ (68074 / 3125) (2178371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2887749888 :
    ThetaLowerSegment 2887749888 2887880960 (28876942332109 / 10000)
      (288782447813257 / 100000) := by
  exact
    packedTile65536 2887749888 2887880960 14 5979 53737 31 _ _ (2178373 / 100000) (272297 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2887880960 :
    ThetaLowerSegment 2887880960 2888012032 (288782447813257 / 100000)
      (144397781910587 / 50000) := by
  exact
    packedTile65536 2887880960 2888012032 14 6021 53739 31 _ _ (2178377 / 100000) (108919 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888012032 :
    ThetaLowerSegment 2888012032 2888143104 (144397781910587 / 50000) (36101076813467 / 12500) := by
  exact
    packedTile65536 2888012032 2888143104 14 5991 53740 31 _ _ (1089191 / 50000) (435677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888143104 :
    ThetaLowerSegment 2888143104 2888274176 (36101076813467 / 12500) (9025675744654 / 3125) := by
  exact
    packedTile65536 2888143104 2888274176 14 5972 53741 31 _ _ (1089193 / 50000) (2178389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888274176 :
    ThetaLowerSegment 2888274176 2888405248 (9025675744654 / 3125) (288834792202523 / 100000) := by
  exact
    packedTile65536 2888274176 2888405248 14 6045 53742 31 _ _ (2178391 / 100000) (1089197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888405248 :
    ThetaLowerSegment 2888405248 2888536320 (288834792202523 / 100000)
      (288847871292107 / 100000) := by
  exact
    packedTile65536 2888405248 2888536320 14 6004 53743 31 _ _ (544599 / 25000) (2178399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888536320 :
    ThetaLowerSegment 2888536320 2888667392 (288847871292107 / 100000)
      (288861017936107 / 100000) := by
  exact
    packedTile65536 2888536320 2888667392 14 6035 53745 31 _ _ (2723 / 125) (2178403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888667392 :
    ThetaLowerSegment 2888667392 2888798464 (288861017936107 / 100000)
      (144437043093851 / 50000) := by
  exact
    packedTile65536 2888667392 2888798464 14 5999 53746 31 _ _ (435681 / 20000) (272301 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888798464 :
    ThetaLowerSegment 2888798464 2888929536 (144437043093851 / 50000)
      (288887036829207 / 100000) := by
  exact
    packedTile65536 2888798464 2888929536 14 5945 53747 31 _ _ (2178409 / 100000) (544603 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888929536 :
    ThetaLowerSegment 2888929536 2889060608 (288887036829207 / 100000)
      (57780039761319 / 20000) := by
  exact
    packedTile65536 2888929536 2889060608 14 6042 53748 31 _ _ (1089207 / 50000) (2178417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889060608 :
    ThetaLowerSegment 2889060608 2889191680 (57780039761319 / 20000)
      (288913543795263 / 100000) := by
  exact
    packedTile65536 2889060608 2889191680 14 6126 53749 31 _ _ (1089209 / 50000) (2178421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889191680 :
    ThetaLowerSegment 2889191680 2889322752 (288913543795263 / 100000)
      (144463373608533 / 50000) := by
  exact
    packedTile65536 2889191680 2889322752 14 6061 53751 31 _ _ (2178423 / 100000) (1089213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889322752 :
    ThetaLowerSegment 2889322752 2889339136 (144463373608533 / 50000) (11557132365969 / 4000) := by
  exact
    packedTile65536 2889322752 2889339136 11 717 53752 31 _ _ (2178427 / 100000) (217843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889339136 :
    ThetaLowerSegment 2889339136 2889341184 (11557132365969 / 4000) (288928546597877 / 100000) := by
  exact
    packedTile65536 2889339136 2889341184 8 109 53752 31 _ _ (544607 / 25000) (2178431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2857341184_2889341184 :
    ThetaLowerSegment 2857341184 2889341184 (71432156080959 / 25000)
      (288928546597877 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2857341184 cell2857472256)
                  (ThetaLowerSegment.join cell2857603328 cell2857734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2857865472 cell2857996544)
                  (ThetaLowerSegment.join cell2858127616 cell2858258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2858389760 cell2858520832)
                  (ThetaLowerSegment.join cell2858651904 cell2858782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2858914048 cell2859045120)
                  (ThetaLowerSegment.join cell2859176192 cell2859307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2859438336 cell2859569408)
                  (ThetaLowerSegment.join cell2859700480 cell2859831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2859962624 cell2860093696)
                  (ThetaLowerSegment.join cell2860224768 cell2860355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2860486912 cell2860617984)
                  (ThetaLowerSegment.join cell2860749056 cell2860880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2861011200 cell2861142272)
                  (ThetaLowerSegment.join cell2861273344 cell2861404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2861535488 cell2861666560)
                  (ThetaLowerSegment.join cell2861797632 cell2861928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2862059776 cell2862190848)
                  (ThetaLowerSegment.join cell2862321920 cell2862452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2862584064 cell2862715136)
                  (ThetaLowerSegment.join cell2862846208 cell2862977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2863108352 cell2863239424)
                  (ThetaLowerSegment.join cell2863370496 cell2863501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2863632640 cell2863763712)
                  (ThetaLowerSegment.join cell2863894784 cell2864025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2864156928 cell2864288000)
                  (ThetaLowerSegment.join cell2864419072 cell2864550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2864681216 cell2864812288)
                  (ThetaLowerSegment.join cell2864943360 cell2865074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2865205504 cell2865336576)
                  (ThetaLowerSegment.join cell2865467648 cell2865598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2865729792 cell2865860864)
                  (ThetaLowerSegment.join cell2865991936 cell2866123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2866254080 cell2866385152)
                  (ThetaLowerSegment.join cell2866516224 cell2866647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2866778368 cell2866909440)
                  (ThetaLowerSegment.join cell2867040512 cell2867171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2867302656 cell2867433728)
                  (ThetaLowerSegment.join cell2867564800 cell2867695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2867826944 cell2867958016)
                  (ThetaLowerSegment.join cell2868089088 cell2868220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2868351232 cell2868482304)
                  (ThetaLowerSegment.join cell2868613376 cell2868744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2868875520 cell2869006592)
                  (ThetaLowerSegment.join cell2869137664 cell2869268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2869399808 cell2869530880)
                  (ThetaLowerSegment.join cell2869661952 cell2869793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2869924096 cell2870055168)
                  (ThetaLowerSegment.join cell2870186240 cell2870317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2870448384 cell2870579456)
                  (ThetaLowerSegment.join cell2870710528 cell2870841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2870972672 cell2871103744)
                  (ThetaLowerSegment.join cell2871234816 cell2871365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2871496960 cell2871628032)
                  (ThetaLowerSegment.join cell2871759104 cell2871890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2872021248 cell2872152320)
                  (ThetaLowerSegment.join cell2872283392 cell2872414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2872545536 cell2872676608)
                  (ThetaLowerSegment.join cell2872807680 cell2872938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2873069824 cell2873200896)
                  (ThetaLowerSegment.join cell2873331968 cell2873463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2873594112 cell2873725184)
                  (ThetaLowerSegment.join cell2873856256 cell2873987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2874118400 cell2874249472)
                  (ThetaLowerSegment.join cell2874380544 cell2874511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2874642688 cell2874773760)
                  (ThetaLowerSegment.join cell2874904832 cell2875035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2875166976 cell2875298048)
                  (ThetaLowerSegment.join cell2875429120 cell2875560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2875691264 cell2875822336)
                  (ThetaLowerSegment.join cell2875953408 cell2876084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2876215552 cell2876346624)
                  (ThetaLowerSegment.join cell2876477696 cell2876608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2876739840 cell2876870912)
                  (ThetaLowerSegment.join cell2877001984 cell2877133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2877264128 cell2877395200)
                  (ThetaLowerSegment.join cell2877526272 cell2877657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2877788416 cell2877919488)
                  (ThetaLowerSegment.join cell2878050560 cell2878181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2878312704 cell2878443776)
                  (ThetaLowerSegment.join cell2878574848 cell2878705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2878836992 cell2878968064)
                  (ThetaLowerSegment.join cell2879099136 cell2879230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2879361280 cell2879492352)
                  (ThetaLowerSegment.join cell2879623424 cell2879754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2879885568 cell2880016640)
                  (ThetaLowerSegment.join cell2880147712 cell2880278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2880409856 cell2880540928)
                  (ThetaLowerSegment.join cell2880672000 cell2880803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2880934144 cell2881065216)
                  (ThetaLowerSegment.join cell2881196288 cell2881327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2881458432 cell2881589504)
                  (ThetaLowerSegment.join cell2881720576 cell2881851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2881982720 cell2882113792)
                  (ThetaLowerSegment.join cell2882244864 cell2882375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2882507008 cell2882638080)
                  (ThetaLowerSegment.join cell2882769152 cell2882900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2883031296 cell2883162368)
                  (ThetaLowerSegment.join cell2883293440 cell2883424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2883555584 cell2883686656)
                  (ThetaLowerSegment.join cell2883817728 cell2883948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2884079872 cell2884210944)
                  (ThetaLowerSegment.join cell2884342016 cell2884473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2884604160 cell2884735232)
                  (ThetaLowerSegment.join cell2884866304 cell2884997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2885128448 cell2885259520)
                  (ThetaLowerSegment.join cell2885390592 cell2885521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2885652736 cell2885783808)
                  (ThetaLowerSegment.join cell2885914880 cell2886045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2886177024 cell2886308096)
                  (ThetaLowerSegment.join cell2886439168 cell2886570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2886701312 cell2886832384)
                  (ThetaLowerSegment.join cell2886963456 cell2887094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2887225600 cell2887356672)
                  (ThetaLowerSegment.join cell2887487744 cell2887618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2887749888 cell2887880960)
                  (ThetaLowerSegment.join cell2888012032 cell2888143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2888274176 cell2888405248)
                  (ThetaLowerSegment.join cell2888536320 cell2888667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2888798464 cell2888929536)
                (ThetaLowerSegment.join cell2889060608 cell2889191680))
              (ThetaLowerSegment.join cell2889322752 cell2889339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
