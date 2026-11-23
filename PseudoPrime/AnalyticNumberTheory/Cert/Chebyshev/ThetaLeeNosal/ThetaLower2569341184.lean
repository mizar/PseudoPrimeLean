/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2569341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2537341184 :
    ThetaLowerSegment 2537341184 2537472256 (253728455215421 / 100000)
      (50748268779289 / 20000) := by
  exact
    packedTile65536 2537341184 2537472256 14 5952 50372 31 _ _ (2165437 / 100000) (13534 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537472256 :
    ThetaLowerSegment 2537472256 2537603328 (50748268779289 / 20000)
      (253754546596319 / 100000) := by
  exact
    packedTile65536 2537472256 2537603328 14 6097 50373 31 _ _ (1082721 / 50000) (433089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537603328 :
    ThetaLowerSegment 2537603328 2537734400 (253754546596319 / 100000)
      (25376782728277 / 10000) := by
  exact
    packedTile65536 2537603328 2537734400 14 6133 50374 31 _ _ (2165447 / 100000) (43309 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537734400 :
    ThetaLowerSegment 2537734400 2537865472 (25376782728277 / 10000) (126890448975521 / 50000) := by
  exact
    packedTile65536 2537734400 2537865472 14 6036 50375 31 _ _ (541363 / 25000) (433091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537865472 :
    ThetaLowerSegment 2537865472 2537996544 (126890448975521 / 50000) (12689698215929 / 5000) := by
  exact
    packedTile65536 2537865472 2537996544 14 6034 50377 31 _ _ (2165457 / 100000) (108273 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2537996544 :
    ThetaLowerSegment 2537996544 2538127616 (12689698215929 / 5000) (253807171477417 / 100000) := by
  exact
    packedTile65536 2537996544 2538127616 14 6099 50378 31 _ _ (2165463 / 100000) (1082733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2538127616 :
    ThetaLowerSegment 2538127616 2538258688 (253807171477417 / 100000)
      (253820363508473 / 100000) := by
  exact
    packedTile65536 2538127616 2538258688 14 6092 50379 31 _ _ (541367 / 25000) (2165471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2538258688 :
    ThetaLowerSegment 2538258688 2538389760 (253820363508473 / 100000)
      (50766668670727 / 20000) := by
  exact
    packedTile65536 2538258688 2538389760 14 5994 50381 31 _ _ (2165473 / 100000) (541369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2538389760 :
    ThetaLowerSegment 2538389760 2538520832 (50766668670727 / 20000)
      (253846511625353 / 100000) := by
  exact
    packedTile65536 2538389760 2538520832 14 6081 50382 31 _ _ (1082739 / 50000) (2165481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2538520832 :
    ThetaLowerSegment 2538520832 2538651904 (253846511625353 / 100000)
      (253859738395517 / 100000) := by
  exact
    packedTile65536 2538520832 2538651904 14 6108 50383 31 _ _ (2165483 / 100000) (1082743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2538651904 :
    ThetaLowerSegment 2538651904 2538782976 (253859738395517 / 100000)
      (253872774633277 / 100000) := by
  exact
    packedTile65536 2538651904 2538782976 14 6020 50385 31 _ _ (135343 / 6250) (2165491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2538782976 :
    ThetaLowerSegment 2538782976 2538914048 (253872774633277 / 100000)
      (253885930009327 / 100000) := by
  exact
    packedTile65536 2538782976 2538914048 14 6075 50386 31 _ _ (1082747 / 50000) (2165497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2538914048 :
    ThetaLowerSegment 2538914048 2539045120 (253885930009327 / 100000)
      (31737377014973 / 12500) := by
  exact
    packedTile65536 2538914048 2539045120 14 6043 50387 31 _ _ (2165499 / 100000) (1082751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2539045120 :
    ThetaLowerSegment 2539045120 2539176192 (31737377014973 / 12500) (31739017925629 / 12500) := by
  exact
    packedTile65536 2539045120 2539176192 14 6062 50388 31 _ _ (67672 / 3125) (2165507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2539176192 :
    ThetaLowerSegment 2539176192 2539307264 (31739017925629 / 12500) (5078502815801 / 2000) := by
  exact
    packedTile65536 2539176192 2539307264 14 6002 50390 31 _ _ (2165509 / 100000) (270689 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2539307264 :
    ThetaLowerSegment 2539307264 2539438336 (5078502815801 / 2000) (126969097254221 / 50000) := by
  exact
    packedTile65536 2539307264 2539438336 14 6028 50391 31 _ _ (1082757 / 50000) (2165517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2539438336 :
    ThetaLowerSegment 2539438336 2539569408 (126969097254221 / 50000)
      (253951358698443 / 100000) := by
  exact
    packedTile65536 2539438336 2539569408 14 6079 50392 31 _ _ (2165519 / 100000) (1082761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2539569408 :
    ThetaLowerSegment 2539569408 2539700480 (253951358698443 / 100000)
      (126982148855159 / 50000) := by
  exact
    packedTile65536 2539569408 2539700480 14 5975 50394 31 _ _ (86621 / 4000) (270691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2539700480 :
    ThetaLowerSegment 2539700480 2539831552 (126982148855159 / 50000)
      (126988729900829 / 50000) := by
  exact
    packedTile65536 2539700480 2539831552 14 6078 50395 31 _ _ (216553 / 10000) (2165533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2539831552 :
    ThetaLowerSegment 2539831552 2539962624 (126988729900829 / 50000)
      (253990663068553 / 100000) := by
  exact
    packedTile65536 2539831552 2539962624 14 6097 50396 31 _ _ (433107 / 20000) (1082769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2539962624 :
    ThetaLowerSegment 2539962624 2540093696 (253990663068553 / 100000)
      (254003645480853 / 100000) := by
  exact
    packedTile65536 2539962624 2540093696 14 5995 50398 31 _ _ (108277 / 5000) (2165543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2540093696 :
    ThetaLowerSegment 2540093696 2540224768 (254003645480853 / 100000)
      (127008372431279 / 50000) := by
  exact
    packedTile65536 2540093696 2540224768 14 6049 50399 31 _ _ (433109 / 20000) (541387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2540224768 :
    ThetaLowerSegment 2540224768 2540355840 (127008372431279 / 50000) (63507467565277 / 25000) := by
  exact
    packedTile65536 2540224768 2540355840 14 6061 50400 31 _ _ (43311 / 2000) (2165553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2540355840 :
    ThetaLowerSegment 2540355840 2540486912 (63507467565277 / 25000) (6351075758623 / 2500) := by
  exact
    packedTile65536 2540355840 2540486912 14 6077 50401 31 _ _ (541389 / 25000) (2165559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2540486912 :
    ThetaLowerSegment 2540486912 2540617984 (6351075758623 / 2500) (31757020288353 / 12500) := by
  exact
    packedTile65536 2540486912 2540617984 14 6064 50403 31 _ _ (2165561 / 100000) (541391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2540617984 :
    ThetaLowerSegment 2540617984 2540749056 (31757020288353 / 12500) (127034609252119 / 50000) := by
  exact
    packedTile65536 2540617984 2540749056 14 6029 50404 31 _ _ (1082783 / 50000) (2165569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2540749056 :
    ThetaLowerSegment 2540749056 2540880128 (127034609252119 / 50000)
      (254082231420377 / 100000) := by
  exact
    packedTile65536 2540749056 2540880128 14 6009 50405 31 _ _ (2165571 / 100000) (1082787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2540880128 :
    ThetaLowerSegment 2540880128 2541011200 (254082231420377 / 100000)
      (254095486911073 / 100000) := by
  exact
    packedTile65536 2540880128 2541011200 14 6121 50407 31 _ _ (270697 / 12500) (2165579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2541011200 :
    ThetaLowerSegment 2541011200 2541142272 (254095486911073 / 100000)
      (254108800903061 / 100000) := by
  exact
    packedTile65536 2541011200 2541142272 14 6148 50408 31 _ _ (2165581 / 100000) (135349 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2541142272 :
    ThetaLowerSegment 2541142272 2541273344 (254108800903061 / 100000)
      (254121887539259 / 100000) := by
  exact
    packedTile65536 2541142272 2541273344 14 6043 50409 31 _ _ (1082793 / 50000) (2165589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2541273344 :
    ThetaLowerSegment 2541273344 2541404416 (254121887539259 / 100000)
      (254135260069859 / 100000) := by
  exact
    packedTile65536 2541273344 2541404416 14 6175 50411 31 _ _ (270699 / 12500) (433119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2541404416 :
    ThetaLowerSegment 2541404416 2541535488 (254135260069859 / 100000)
      (254148266645441 / 100000) := by
  exact
    packedTile65536 2541404416 2541535488 14 6006 50412 31 _ _ (2165597 / 100000) (2707 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2541535488 :
    ThetaLowerSegment 2541535488 2541666560 (254148266645441 / 100000)
      (254161294907073 / 100000) := by
  exact
    packedTile65536 2541535488 2541666560 14 6016 50413 31 _ _ (1082801 / 50000) (433121 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2541666560 :
    ThetaLowerSegment 2541666560 2541797632 (254161294907073 / 100000)
      (31771803664191 / 12500) := by
  exact
    packedTile65536 2541666560 2541797632 14 6065 50414 31 _ _ (2165607 / 100000) (216561 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2541797632 :
    ThetaLowerSegment 2541797632 2541928704 (31771803664191 / 12500) (7943361164171 / 3125) := by
  exact
    packedTile65536 2541797632 2541928704 14 6062 50416 31 _ _ (541403 / 25000) (433123 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2541928704 :
    ThetaLowerSegment 2541928704 2542059776 (7943361164171 / 3125) (254200709045513 / 100000) := by
  exact
    packedTile65536 2541928704 2542059776 14 6073 50417 31 _ _ (2165617 / 100000) (108281 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2542059776 :
    ThetaLowerSegment 2542059776 2542190848 (254200709045513 / 100000) (1588836305619 / 625) := by
  exact
    packedTile65536 2542059776 2542190848 14 6049 50418 31 _ _ (2165623 / 100000) (1082813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2542190848 :
    ThetaLowerSegment 2542190848 2542321920 (1588836305619 / 625) (7944591373194 / 3125) := by
  exact
    packedTile65536 2542190848 2542321920 14 6056 50420 31 _ _ (541407 / 25000) (2165631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2542321920 :
    ThetaLowerSegment 2542321920 2542452992 (7944591373194 / 3125) (127120021673461 / 50000) := by
  exact
    packedTile65536 2542321920 2542452992 14 6058 50421 31 _ _ (2165633 / 100000) (541409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2542452992 :
    ThetaLowerSegment 2542452992 2542584064 (127120021673461 / 50000)
      (127126598716067 / 50000) := by
  exact
    packedTile65536 2542452992 2542584064 14 6074 50422 31 _ _ (1082819 / 50000) (2165641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2542584064 :
    ThetaLowerSegment 2542584064 2542715136 (127126598716067 / 50000) (50853249952499 / 20000) := by
  exact
    packedTile65536 2542584064 2542715136 14 6027 50424 31 _ _ (2165643 / 100000) (1082823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2542715136 :
    ThetaLowerSegment 2542715136 2542846208 (50853249952499 / 20000)
      (254279334607711 / 100000) := by
  exact
    packedTile65536 2542715136 2542846208 14 6042 50425 31 _ _ (135353 / 6250) (2165651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2542846208 :
    ThetaLowerSegment 2542846208 2542977280 (254279334607711 / 100000)
      (63573108660677 / 25000) := by
  exact
    packedTile65536 2542846208 2542977280 14 6049 50426 31 _ _ (2165653 / 100000) (270707 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2542977280 :
    ThetaLowerSegment 2542977280 2543108352 (63573108660677 / 25000) (127152699138741 / 50000) := by
  exact
    packedTile65536 2542977280 2543108352 14 5986 50427 31 _ _ (2165659 / 100000) (1082831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2543108352 :
    ThetaLowerSegment 2543108352 2543239424 (127152699138741 / 50000)
      (127159158231621 / 50000) := by
  exact
    packedTile65536 2543108352 2543239424 14 5965 50429 31 _ _ (67677 / 3125) (2165667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2543239424 :
    ThetaLowerSegment 2543239424 2543370496 (127159158231621 / 50000) (2543314880621 / 1000) := by
  exact
    packedTile65536 2543239424 2543370496 14 6082 50430 31 _ _ (2165669 / 100000) (270709 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2543370496 :
    ThetaLowerSegment 2543370496 2543501568 (2543314880621 / 1000) (15896541772129 / 6250) := by
  exact
    packedTile65536 2543370496 2543501568 14 6086 50431 31 _ _ (1082837 / 50000) (2165677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2543501568 :
    ThetaLowerSegment 2543501568 2543632640 (15896541772129 / 6250) (63589426435411 / 25000) := by
  exact
    packedTile65536 2543501568 2543632640 14 6020 50433 31 _ _ (2165679 / 100000) (1082841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2543632640 :
    ThetaLowerSegment 2543632640 2543763712 (63589426435411 / 25000) (63592694452567 / 25000) := by
  exact
    packedTile65536 2543632640 2543763712 14 6036 50434 31 _ _ (541421 / 25000) (2165687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2543763712 :
    ThetaLowerSegment 2543763712 2543894784 (63592694452567 / 25000) (63595951650327 / 25000) := by
  exact
    packedTile65536 2543763712 2543894784 14 6016 50435 31 _ _ (216569 / 10000) (2165693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2543894784 :
    ThetaLowerSegment 2543894784 2544025856 (63595951650327 / 25000)
      (254396911221753 / 100000) := by
  exact
    packedTile65536 2543894784 2544025856 14 6051 50437 31 _ _ (433139 / 20000) (1082849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544025856 :
    ThetaLowerSegment 2544025856 2544156928 (254396911221753 / 100000)
      (254410039695153 / 100000) := by
  exact
    packedTile65536 2544025856 2544156928 14 6062 50438 31 _ _ (21657 / 1000) (2165703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544156928 :
    ThetaLowerSegment 2544156928 2544288000 (254410039695153 / 100000)
      (254423107559123 / 100000) := by
  exact
    packedTile65536 2544156928 2544288000 14 6034 50439 31 _ _ (433141 / 20000) (541427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544288000 :
    ThetaLowerSegment 2544288000 2544419072 (254423107559123 / 100000)
      (254436160293293 / 100000) := by
  exact
    packedTile65536 2544288000 2544419072 14 6027 50440 31 _ _ (216571 / 10000) (2165713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544419072 :
    ThetaLowerSegment 2544419072 2544550144 (254436160293293 / 100000) (7951532899834 / 3125) := by
  exact
    packedTile65536 2544419072 2544550144 14 5953 50442 31 _ _ (433143 / 20000) (1082859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544550144 :
    ThetaLowerSegment 2544550144 2544681216 (7951532899834 / 3125) (31807766988651 / 12500) := by
  exact
    packedTile65536 2544550144 2544681216 14 6041 50443 31 _ _ (54143 / 2500) (2165723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544681216 :
    ThetaLowerSegment 2544681216 2544812288 (31807766988651 / 12500) (63618824797959 / 25000) := by
  exact
    packedTile65536 2544681216 2544812288 14 6078 50444 31 _ _ (1082863 / 50000) (2165729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544812288 :
    ThetaLowerSegment 2544812288 2544943360 (63618824797959 / 25000)
      (254488456007661 / 100000) := by
  exact
    packedTile65536 2544812288 2544943360 14 6075 50446 31 _ _ (2165731 / 100000) (1082867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544943360 :
    ThetaLowerSegment 2544943360 2545074432 (254488456007661 / 100000)
      (254501391948789 / 100000) := by
  exact
    packedTile65536 2544943360 2545074432 14 5973 50447 31 _ _ (270717 / 12500) (2165739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2545074432 :
    ThetaLowerSegment 2545074432 2545205504 (254501391948789 / 100000)
      (254514347411451 / 100000) := by
  exact
    packedTile65536 2545074432 2545205504 14 5982 50448 31 _ _ (2165741 / 100000) (135359 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2545205504 :
    ThetaLowerSegment 2545205504 2545336576 (254514347411451 / 100000)
      (254527519478623 / 100000) := by
  exact
    packedTile65536 2545205504 2545336576 14 6082 50450 31 _ _ (1082873 / 50000) (2165749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2545336576 :
    ThetaLowerSegment 2545336576 2545467648 (254527519478623 / 100000)
      (127270279732697 / 50000) := by
  exact
    packedTile65536 2545336576 2545467648 14 6021 50451 31 _ _ (2165751 / 100000) (1082877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2545467648 :
    ThetaLowerSegment 2545467648 2545598720 (127270279732697 / 50000)
      (127276919943659 / 50000) := by
  exact
    packedTile65536 2545467648 2545598720 14 6132 50452 31 _ _ (2165757 / 100000) (13536 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2545598720 :
    ThetaLowerSegment 2545598720 2545729792 (127276919943659 / 50000)
      (127283454047613 / 50000) := by
  exact
    packedTile65536 2545598720 2545729792 14 6034 50453 31 _ _ (1082881 / 50000) (433153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2545729792 :
    ThetaLowerSegment 2545729792 2545860864 (127283454047613 / 50000)
      (127290055305429 / 50000) := by
  exact
    packedTile65536 2545729792 2545860864 14 6096 50455 31 _ _ (2165767 / 100000) (216577 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2545860864 :
    ThetaLowerSegment 2545860864 2545991936 (127290055305429 / 50000)
      (127296719385873 / 50000) := by
  exact
    packedTile65536 2545860864 2545991936 14 6154 50456 31 _ _ (541443 / 25000) (86631 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2545991936 :
    ThetaLowerSegment 2545991936 2546123008 (127296719385873 / 50000)
      (254606392283983 / 100000) := by
  exact
    packedTile65536 2545991936 2546123008 14 5981 50457 31 _ _ (2165777 / 100000) (108289 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2546123008 :
    ThetaLowerSegment 2546123008 2546254080 (254606392283983 / 100000)
      (254619490933519 / 100000) := by
  exact
    packedTile65536 2546123008 2546254080 14 6048 50459 31 _ _ (1082891 / 50000) (433157 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2546254080 :
    ThetaLowerSegment 2546254080 2546385152 (254619490933519 / 100000)
      (254632602608017 / 100000) := by
  exact
    packedTile65536 2546254080 2546385152 14 6054 50460 31 _ _ (2165787 / 100000) (216579 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2546385152 :
    ThetaLowerSegment 2546385152 2546516224 (254632602608017 / 100000)
      (254645753303113 / 100000) := by
  exact
    packedTile65536 2546385152 2546516224 14 6072 50461 31 _ _ (2165793 / 100000) (541449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2546516224 :
    ThetaLowerSegment 2546516224 2546647296 (254645753303113 / 100000)
      (254658923520751 / 100000) := by
  exact
    packedTile65536 2546516224 2546647296 14 6081 50463 31 _ _ (1082899 / 50000) (2165801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2546647296 :
    ThetaLowerSegment 2546647296 2546778368 (254658923520751 / 100000)
      (254671931333569 / 100000) := by
  exact
    packedTile65536 2546647296 2546778368 14 6006 50464 31 _ _ (2165803 / 100000) (1082903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2546778368 :
    ThetaLowerSegment 2546778368 2546909440 (254671931333569 / 100000)
      (254684997653233 / 100000) := by
  exact
    packedTile65536 2546778368 2546909440 14 6033 50465 31 _ _ (135363 / 6250) (2165811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2546909440 :
    ThetaLowerSegment 2546909440 2547040512 (254684997653233 / 100000)
      (254698100821883 / 100000) := by
  exact
    packedTile65536 2546909440 2547040512 14 6050 50466 31 _ _ (2165813 / 100000) (270727 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2547040512 :
    ThetaLowerSegment 2547040512 2547171584 (254698100821883 / 100000)
      (50942240370993 / 20000) := by
  exact
    packedTile65536 2547040512 2547171584 14 6049 50468 31 _ _ (1082909 / 50000) (2165821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2547171584 :
    ThetaLowerSegment 2547171584 2547302656 (50942240370993 / 20000)
      (254724313747407 / 100000) := by
  exact
    packedTile65536 2547171584 2547302656 14 6054 50469 31 _ _ (2165823 / 100000) (1082913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2547302656 :
    ThetaLowerSegment 2547302656 2547433728 (254724313747407 / 100000)
      (127368687931053 / 50000) := by
  exact
    packedTile65536 2547302656 2547433728 14 6031 50470 31 _ _ (2165829 / 100000) (270729 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2547433728 :
    ThetaLowerSegment 2547433728 2547564800 (127368687931053 / 50000)
      (127375339207267 / 50000) := by
  exact
    packedTile65536 2547433728 2547564800 14 6142 50472 31 _ _ (1082917 / 50000) (2165837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2547564800 :
    ThetaLowerSegment 2547564800 2547695872 (127375339207267 / 50000) (12738187354353 / 5000) := by
  exact
    packedTile65536 2547564800 2547695872 14 6034 50473 31 _ _ (2165839 / 100000) (1082921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2547695872 :
    ThetaLowerSegment 2547695872 2547826944 (12738187354353 / 5000) (12738836024631 / 5000) := by
  exact
    packedTile65536 2547695872 2547826944 14 5990 50474 31 _ _ (541461 / 25000) (2165847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2547826944 :
    ThetaLowerSegment 2547826944 2547958016 (12738836024631 / 5000) (50957975605059 / 20000) := by
  exact
    packedTile65536 2547826944 2547958016 14 6075 50476 31 _ _ (2165849 / 100000) (541463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2547958016 :
    ThetaLowerSegment 2547958016 2548089088 (50957975605059 / 20000)
      (254802961949309 / 100000) := by
  exact
    packedTile65536 2547958016 2548089088 14 6041 50477 31 _ _ (1082927 / 50000) (2165857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2548089088 :
    ThetaLowerSegment 2548089088 2548220160 (254802961949309 / 100000)
      (254815996088771 / 100000) := by
  exact
    packedTile65536 2548089088 2548220160 14 6018 50478 31 _ _ (2165859 / 100000) (1082931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2548220160 :
    ThetaLowerSegment 2548220160 2548351232 (254815996088771 / 100000)
      (254828960956661 / 100000) := by
  exact
    packedTile65536 2548220160 2548351232 14 5986 50479 31 _ _ (433173 / 20000) (541467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2548351232 :
    ThetaLowerSegment 2548351232 2548482304 (254828960956661 / 100000)
      (254842159768441 / 100000) := by
  exact
    packedTile65536 2548351232 2548482304 14 6094 50481 31 _ _ (216587 / 10000) (2165873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2548482304 :
    ThetaLowerSegment 2548482304 2548613376 (254842159768441 / 100000)
      (254855315293191 / 100000) := by
  exact
    packedTile65536 2548482304 2548613376 14 6074 50482 31 _ _ (17327 / 800) (1082939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2548613376 :
    ThetaLowerSegment 2548613376 2548744448 (254855315293191 / 100000)
      (254868520663551 / 100000) := by
  exact
    packedTile65536 2548613376 2548744448 14 6097 50483 31 _ _ (54147 / 2500) (2165883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2548744448 :
    ThetaLowerSegment 2548744448 2548875520 (254868520663551 / 100000)
      (254881654590191 / 100000) := by
  exact
    packedTile65536 2548744448 2548875520 14 6064 50485 31 _ _ (433177 / 20000) (67684 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2548875520 :
    ThetaLowerSegment 2548875520 2549006592 (254881654590191 / 100000)
      (254894905505211 / 100000) := by
  exact
    packedTile65536 2548875520 2549006592 14 6118 50486 31 _ _ (216589 / 10000) (2165893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2549006592 :
    ThetaLowerSegment 2549006592 2549137664 (254894905505211 / 100000)
      (127454038156353 / 50000) := by
  exact
    packedTile65536 2549006592 2549137664 14 6081 50487 31 _ _ (433179 / 20000) (1082949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2549137664 :
    ThetaLowerSegment 2549137664 2549268736 (127454038156353 / 50000)
      (127460566181967 / 50000) := by
  exact
    packedTile65536 2549137664 2549268736 14 6028 50488 31 _ _ (2165901 / 100000) (135369 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2549268736 :
    ThetaLowerSegment 2549268736 2549399808 (127460566181967 / 50000) (63733594219781 / 25000) := by
  exact
    packedTile65536 2549268736 2549399808 14 6115 50490 31 _ _ (1082953 / 50000) (2165909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2549399808 :
    ThetaLowerSegment 2549399808 2549530880 (63733594219781 / 25000) (127473818293133 / 50000) := by
  exact
    packedTile65536 2549399808 2549530880 14 6122 50491 31 _ _ (2165911 / 100000) (1082957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2549530880 :
    ThetaLowerSegment 2549530880 2549661952 (127473818293133 / 50000) (25496069489383 / 10000) := by
  exact
    packedTile65536 2549530880 2549661952 14 6029 50492 31 _ _ (541479 / 25000) (2165919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2549661952 :
    ThetaLowerSegment 2549661952 2549793024 (25496069489383 / 10000) (127486988160701 / 50000) := by
  exact
    packedTile65536 2549661952 2549793024 14 6132 50494 31 _ _ (2165921 / 100000) (541481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2549793024 :
    ThetaLowerSegment 2549793024 2549924096 (127486988160701 / 50000)
      (127493529257221 / 50000) := by
  exact
    packedTile65536 2549793024 2549924096 14 6040 50495 31 _ _ (1082963 / 50000) (2165929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2549924096 :
    ThetaLowerSegment 2549924096 2550055168 (127493529257221 / 50000) (7968757240837 / 3125) := by
  exact
    packedTile65536 2549924096 2550055168 14 6082 50496 31 _ _ (2165931 / 100000) (1082967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2550055168 :
    ThetaLowerSegment 2550055168 2550186240 (7968757240837 / 3125) (255013441756547 / 100000) := by
  exact
    packedTile65536 2550055168 2550186240 14 6099 50498 31 _ _ (2165937 / 100000) (108297 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2550186240 :
    ThetaLowerSegment 2550186240 2550317312 (255013441756547 / 100000) (2040212521593 / 800) := by
  exact
    packedTile65536 2550186240 2550317312 14 6059 50499 31 _ _ (1082971 / 50000) (433189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2550317312 :
    ThetaLowerSegment 2550317312 2550448384 (2040212521593 / 800) (2040316487049 / 800) := by
  exact
    packedTile65536 2550317312 2550448384 14 6000 50500 31 _ _ (2165947 / 100000) (43319 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2550448384 :
    ThetaLowerSegment 2550448384 2550579456 (2040316487049 / 800) (255052732035237 / 100000) := by
  exact
    packedTile65536 2550448384 2550579456 14 6081 50501 31 _ _ (67686 / 3125) (433191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2550579456 :
    ThetaLowerSegment 2550579456 2550710528 (255052732035237 / 100000)
      (63766472556003 / 25000) := by
  exact
    packedTile65536 2550579456 2550710528 14 6075 50503 31 _ _ (2165957 / 100000) (54149 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2550710528 :
    ThetaLowerSegment 2550710528 2550841600 (63766472556003 / 25000) (127539491732151 / 50000) := by
  exact
    packedTile65536 2550710528 2550841600 14 6045 50504 31 _ _ (1082981 / 50000) (433193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2550841600 :
    ThetaLowerSegment 2550841600 2550972672 (127539491732151 / 50000) (25509194461083 / 10000) := by
  exact
    packedTile65536 2550841600 2550972672 14 5984 50505 31 _ _ (2165967 / 100000) (216597 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2550972672 :
    ThetaLowerSegment 2550972672 2551103744 (25509194461083 / 10000) (127552474556361 / 50000) := by
  exact
    packedTile65536 2550972672 2551103744 14 6004 50507 31 _ _ (2165973 / 100000) (270747 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2551103744 :
    ThetaLowerSegment 2551103744 2551234816 (127552474556361 / 50000) (63779504114499 / 25000) := by
  exact
    packedTile65536 2551103744 2551234816 14 6033 50508 31 _ _ (1082989 / 50000) (2165981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2551234816 :
    ThetaLowerSegment 2551234816 2551365888 (63779504114499 / 25000) (25513113798301 / 10000) := by
  exact
    packedTile65536 2551234816 2551365888 14 6058 50509 31 _ _ (2165983 / 100000) (1082993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2551365888 :
    ThetaLowerSegment 2551365888 2551496960 (25513113798301 / 10000) (127572109192271 / 50000) := by
  exact
    packedTile65536 2551365888 2551496960 14 6039 50511 31 _ _ (541497 / 25000) (2165991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2551496960 :
    ThetaLowerSegment 2551496960 2551628032 (127572109192271 / 50000)
      (255157246832437 / 100000) := by
  exact
    packedTile65536 2551496960 2551628032 14 6015 50512 31 _ _ (2165993 / 100000) (541499 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2551628032 :
    ThetaLowerSegment 2551628032 2551759104 (255157246832437 / 100000)
      (255170496242203 / 100000) := by
  exact
    packedTile65536 2551628032 2551759104 14 6117 50513 31 _ _ (1082999 / 50000) (2166001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2551759104 :
    ThetaLowerSegment 2551759104 2551890176 (255170496242203 / 100000)
      (255183600560353 / 100000) := by
  exact
    packedTile65536 2551759104 2551890176 14 6050 50514 31 _ _ (2166003 / 100000) (1083003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2551890176 :
    ThetaLowerSegment 2551890176 2552021248 (255183600560353 / 100000)
      (127598390362559 / 50000) := by
  exact
    packedTile65536 2551890176 2552021248 14 6085 50516 31 _ _ (2166009 / 100000) (541503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552021248 :
    ThetaLowerSegment 2552021248 2552152320 (127598390362559 / 50000)
      (127604979377147 / 50000) := by
  exact
    packedTile65536 2552021248 2552152320 14 6084 50517 31 _ _ (1083007 / 50000) (2166017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552152320 :
    ThetaLowerSegment 2552152320 2552283392 (127604979377147 / 50000) (31902875315089 / 12500) := by
  exact
    packedTile65536 2552152320 2552283392 14 6022 50518 31 _ _ (2166019 / 100000) (1083011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552283392 :
    ThetaLowerSegment 2552283392 2552414464 (31902875315089 / 12500) (6380898991907 / 2500) := by
  exact
    packedTile65536 2552283392 2552414464 14 5982 50520 31 _ _ (270753 / 12500) (2166027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552414464 :
    ThetaLowerSegment 2552414464 2552545536 (6380898991907 / 2500) (127624666369663 / 50000) := by
  exact
    packedTile65536 2552414464 2552545536 14 6174 50521 31 _ _ (2166029 / 100000) (135377 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552545536 :
    ThetaLowerSegment 2552545536 2552676608 (127624666369663 / 50000)
      (127631255445091 / 50000) := by
  exact
    packedTile65536 2552545536 2552676608 14 6084 50522 31 _ _ (1083017 / 50000) (2166037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552676608 :
    ThetaLowerSegment 2552676608 2552807680 (127631255445091 / 50000) (6381886703387 / 2500) := by
  exact
    packedTile65536 2552676608 2552807680 14 5982 50524 31 _ _ (2166039 / 100000) (1083021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552807680 :
    ThetaLowerSegment 2552807680 2552938752 (6381886703387 / 2500) (12764422678463 / 5000) := by
  exact
    packedTile65536 2552807680 2552938752 14 5995 50525 31 _ _ (541511 / 25000) (2166047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552938752 :
    ThetaLowerSegment 2552938752 2553069824 (12764422678463 / 5000) (25530149102421 / 10000) := by
  exact
    packedTile65536 2552938752 2553069824 14 6019 50526 31 _ _ (43321 / 2000) (2166053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2553069824 :
    ThetaLowerSegment 2553069824 2553200896 (25530149102421 / 10000) (51062934293777 / 20000) := by
  exact
    packedTile65536 2553069824 2553200896 14 6085 50527 31 _ _ (433211 / 20000) (1083029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2553200896 :
    ThetaLowerSegment 2553200896 2553331968 (51062934293777 / 20000) (51065529666869 / 20000) := by
  exact
    packedTile65536 2553200896 2553331968 14 5991 50529 31 _ _ (108303 / 5000) (2166063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2553331968 :
    ThetaLowerSegment 2553331968 2553463040 (51065529666869 / 20000) (51068158403353 / 20000) := by
  exact
    packedTile65536 2553331968 2553463040 14 6068 50530 31 _ _ (433213 / 20000) (541517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2553463040 :
    ThetaLowerSegment 2553463040 2553594112 (51068158403353 / 20000) (10214151797399 / 4000) := by
  exact
    packedTile65536 2553463040 2553594112 14 6003 50531 31 _ _ (216607 / 10000) (2166073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2553594112 :
    ThetaLowerSegment 2553594112 2553725184 (10214151797399 / 4000) (2042935405453 / 800) := by
  exact
    packedTile65536 2553594112 2553725184 14 6062 50533 31 _ _ (86643 / 4000) (1083039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2553725184 :
    ThetaLowerSegment 2553725184 2553856256 (2042935405453 / 800) (51076022988549 / 20000) := by
  exact
    packedTile65536 2553725184 2553856256 14 6089 50534 31 _ _ (13538 / 625) (2166083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2553856256 :
    ThetaLowerSegment 2553856256 2553987328 (51076022988549 / 20000)
      (255393254420421 / 100000) := by
  exact
    packedTile65536 2553856256 2553987328 14 6066 50535 31 _ _ (1083043 / 50000) (2166089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2553987328 :
    ThetaLowerSegment 2553987328 2554118400 (255393254420421 / 100000)
      (127703224040351 / 50000) := by
  exact
    packedTile65536 2553987328 2554118400 14 6091 50536 31 _ _ (2166091 / 100000) (1083047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2554118400 :
    ThetaLowerSegment 2554118400 2554249472 (127703224040351 / 50000)
      (127709816553527 / 50000) := by
  exact
    packedTile65536 2554118400 2554249472 14 6087 50538 31 _ _ (135381 / 6250) (2166099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2554249472 :
    ThetaLowerSegment 2554249472 2554380544 (127709816553527 / 50000) (63858173674021 / 25000) := by
  exact
    packedTile65536 2554249472 2554380544 14 6030 50539 31 _ _ (2166101 / 100000) (270763 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2554380544 :
    ThetaLowerSegment 2554380544 2554511616 (63858173674021 / 25000) (127722818589717 / 50000) := by
  exact
    packedTile65536 2554380544 2554511616 14 5975 50540 31 _ _ (1083053 / 50000) (2166109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2554511616 :
    ThetaLowerSegment 2554511616 2554642688 (127722818589717 / 50000)
      (127729381906047 / 50000) := by
  exact
    packedTile65536 2554511616 2554642688 14 6060 50542 31 _ _ (2166111 / 100000) (1083057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2554642688 :
    ThetaLowerSegment 2554642688 2554773760 (127729381906047 / 50000)
      (127735950652817 / 50000) := by
  exact
    packedTile65536 2554642688 2554773760 14 6065 50543 31 _ _ (541529 / 25000) (2166119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2554773760 :
    ThetaLowerSegment 2554773760 2554904832 (127735950652817 / 50000) (10219406405291 / 4000) := by
  exact
    packedTile65536 2554773760 2554904832 14 6121 50544 31 _ _ (2166121 / 100000) (541531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2554904832 :
    ThetaLowerSegment 2554904832 2555035904 (10219406405291 / 4000) (255498174223291 / 100000) := by
  exact
    packedTile65536 2554904832 2555035904 14 6008 50546 31 _ _ (2166127 / 100000) (216613 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2555035904 :
    ThetaLowerSegment 2555035904 2555166976 (255498174223291 / 100000)
      (255511331309059 / 100000) := by
  exact
    packedTile65536 2555035904 2555166976 14 6074 50547 31 _ _ (541533 / 25000) (433227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2555166976 :
    ThetaLowerSegment 2555166976 2555298048 (255511331309059 / 100000)
      (255524436437909 / 100000) := by
  exact
    packedTile65536 2555166976 2555298048 14 6050 50548 31 _ _ (2166137 / 100000) (108307 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2555298048 :
    ThetaLowerSegment 2555298048 2555429120 (255524436437909 / 100000)
      (255537307653673 / 100000) := by
  exact
    packedTile65536 2555298048 2555429120 14 5942 50549 31 _ _ (1083071 / 50000) (433229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2555429120 :
    ThetaLowerSegment 2555429120 2555560192 (255537307653673 / 100000) (3194380458383 / 1250) := by
  exact
    packedTile65536 2555429120 2555560192 14 6061 50551 31 _ _ (2166147 / 100000) (43323 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2555560192 :
    ThetaLowerSegment 2555560192 2555691264 (3194380458383 / 1250) (31945465210107 / 12500) := by
  exact
    packedTile65536 2555560192 2555691264 14 6133 50552 31 _ _ (270769 / 12500) (433231 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2555691264 :
    ThetaLowerSegment 2555691264 2555822336 (31945465210107 / 12500) (127788409133039 / 50000) := by
  exact
    packedTile65536 2555691264 2555822336 14 6046 50553 31 _ _ (2166157 / 100000) (27077 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2555822336 :
    ThetaLowerSegment 2555822336 2555953408 (127788409133039 / 50000) (15974380917061 / 6250) := by
  exact
    packedTile65536 2555822336 2555953408 14 6129 50555 31 _ _ (1083081 / 50000) (433233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2555953408 :
    ThetaLowerSegment 2555953408 2556084480 (15974380917061 / 6250) (7987604061233 / 3125) := by
  exact
    packedTile65536 2555953408 2556084480 14 6110 50556 31 _ _ (270771 / 12500) (2166171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2556084480 :
    ThetaLowerSegment 2556084480 2556215552 (7987604061233 / 3125) (25561645263549 / 10000) := by
  exact
    packedTile65536 2556084480 2556215552 14 6058 50557 31 _ _ (2166173 / 100000) (67693 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2556215552 :
    ThetaLowerSegment 2556215552 2556346624 (25561645263549 / 10000) (63907399792443 / 25000) := by
  exact
    packedTile65536 2556215552 2556346624 14 6069 50559 31 _ _ (1083089 / 50000) (2166181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2556346624 :
    ThetaLowerSegment 2556346624 2556477696 (63907399792443 / 25000) (127821365285559 / 50000) := by
  exact
    packedTile65536 2556346624 2556477696 14 6062 50560 31 _ _ (2166183 / 100000) (1083093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2556477696 :
    ThetaLowerSegment 2556477696 2556608768 (127821365285559 / 50000)
      (127827901757849 / 50000) := by
  exact
    packedTile65536 2556477696 2556608768 14 6035 50561 31 _ _ (541547 / 25000) (2166191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2556608768 :
    ThetaLowerSegment 2556608768 2556739840 (127827901757849 / 50000) (15979310602297 / 6250) := by
  exact
    packedTile65536 2556608768 2556739840 14 6078 50562 31 _ _ (2166193 / 100000) (541549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2556739840 :
    ThetaLowerSegment 2556739840 2556870912 (15979310602297 / 6250) (63920468961109 / 25000) := by
  exact
    packedTile65536 2556739840 2556870912 14 5958 50564 31 _ _ (1083099 / 50000) (2166201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2556870912 :
    ThetaLowerSegment 2556870912 2557001984 (63920468961109 / 25000) (15980936200777 / 6250) := by
  exact
    packedTile65536 2556870912 2557001984 14 6049 50565 31 _ _ (541551 / 25000) (2166207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2557001984 :
    ThetaLowerSegment 2557001984 2557133056 (15980936200777 / 6250) (63927052604251 / 25000) := by
  exact
    packedTile65536 2557001984 2557133056 14 6108 50566 31 _ _ (2166209 / 100000) (541553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2557133056 :
    ThetaLowerSegment 2557133056 2557264128 (63927052604251 / 25000) (63930351748173 / 25000) := by
  exact
    packedTile65536 2557133056 2557264128 14 6092 50568 31 _ _ (1083107 / 50000) (2166217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2557264128 :
    ThetaLowerSegment 2557264128 2557395200 (63930351748173 / 25000) (127867260641259 / 50000) := by
  exact
    packedTile65536 2557264128 2557395200 14 6054 50569 31 _ _ (2166219 / 100000) (1083111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2557395200 :
    ThetaLowerSegment 2557395200 2557526272 (127867260641259 / 50000)
      (127873737651019 / 50000) := by
  exact
    packedTile65536 2557395200 2557526272 14 5980 50570 31 _ _ (135389 / 6250) (2166227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2557526272 :
    ThetaLowerSegment 2557526272 2557657344 (127873737651019 / 50000)
      (255760613480923 / 100000) := by
  exact
    packedTile65536 2557526272 2557657344 14 6065 50571 31 _ _ (2166229 / 100000) (270779 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2557657344 :
    ThetaLowerSegment 2557657344 2557788416 (255760613480923 / 100000)
      (255773615217391 / 100000) := by
  exact
    packedTile65536 2557657344 2557788416 14 6002 50573 31 _ _ (1083117 / 50000) (2166237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2557788416 :
    ThetaLowerSegment 2557788416 2557919488 (255773615217391 / 100000)
      (127893337736161 / 50000) := by
  exact
    packedTile65536 2557788416 2557919488 14 6029 50574 31 _ _ (2166239 / 100000) (1083121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2557919488 :
    ThetaLowerSegment 2557919488 2558050560 (127893337736161 / 50000)
      (255799826745717 / 100000) := by
  exact
    packedTile65536 2557919488 2558050560 14 6071 50575 31 _ _ (433249 / 20000) (270781 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2558050560 :
    ThetaLowerSegment 2558050560 2558181632 (255799826745717 / 100000)
      (255812986714467 / 100000) := by
  exact
    packedTile65536 2558050560 2558181632 14 6075 50577 31 _ _ (1733 / 80) (2166253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2558181632 :
    ThetaLowerSegment 2558181632 2558312704 (255812986714467 / 100000)
      (63956556174693 / 25000) := by
  exact
    packedTile65536 2558181632 2558312704 14 6111 50578 31 _ _ (433251 / 20000) (1083129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2558312704 :
    ThetaLowerSegment 2558312704 2558443776 (63956556174693 / 25000) (63959858638063 / 25000) := by
  exact
    packedTile65536 2558312704 2558443776 14 6098 50579 31 _ _ (108313 / 5000) (2166263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2558443776 :
    ThetaLowerSegment 2558443776 2558574848 (63959858638063 / 25000) (127926317885581 / 50000) := by
  exact
    packedTile65536 2558443776 2558574848 14 6094 50581 31 _ _ (433253 / 20000) (541567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2558574848 :
    ThetaLowerSegment 2558574848 2558705920 (127926317885581 / 50000) (63966390476063 / 25000) := by
  exact
    packedTile65536 2558574848 2558705920 14 5967 50582 31 _ _ (216627 / 10000) (2166273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2558705920 :
    ThetaLowerSegment 2558705920 2558836992 (63966390476063 / 25000) (127939329601451 / 50000) := by
  exact
    packedTile65536 2558705920 2558836992 14 6046 50583 31 _ _ (86651 / 4000) (1083139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2558836992 :
    ThetaLowerSegment 2558836992 2558968064 (127939329601451 / 50000)
      (127945917258931 / 50000) := by
  exact
    packedTile65536 2558836992 2558968064 14 6082 50584 31 _ _ (54157 / 2500) (2166283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2558968064 :
    ThetaLowerSegment 2558968064 2559099136 (127945917258931 / 50000)
      (127952420446501 / 50000) := by
  exact
    packedTile65536 2558968064 2559099136 14 6004 50586 31 _ _ (433257 / 20000) (135393 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2559099136 :
    ThetaLowerSegment 2559099136 2559230208 (127952420446501 / 50000) (63979510567589 / 25000) := by
  exact
    packedTile65536 2559099136 2559230208 14 6094 50587 31 _ _ (2166291 / 100000) (1083147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2559230208 :
    ThetaLowerSegment 2559230208 2559361280 (63979510567589 / 25000) (63982842330837 / 25000) := by
  exact
    packedTile65536 2559230208 2559361280 14 6152 50588 31 _ _ (270787 / 12500) (2166299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2559361280 :
    ThetaLowerSegment 2559361280 2559492352 (63982842330837 / 25000)
      (255944364963047 / 100000) := by
  exact
    packedTile65536 2559361280 2559492352 14 5999 50590 31 _ _ (2166301 / 100000) (67697 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2559492352 :
    ThetaLowerSegment 2559492352 2559623424 (255944364963047 / 100000)
      (255957464615429 / 100000) := by
  exact
    packedTile65536 2559492352 2559623424 14 6047 50591 31 _ _ (1083153 / 50000) (2166309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2559623424 :
    ThetaLowerSegment 2559623424 2559754496 (255957464615429 / 100000)
      (255970640118931 / 100000) := by
  exact
    packedTile65536 2559623424 2559754496 14 6082 50592 31 _ _ (2166311 / 100000) (1083157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2559754496 :
    ThetaLowerSegment 2559754496 2559885568 (255970640118931 / 100000)
      (255983789657051 / 100000) := by
  exact
    packedTile65536 2559754496 2559885568 14 6070 50594 31 _ _ (541579 / 25000) (2166319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2559885568 :
    ThetaLowerSegment 2559885568 2560016640 (255983789657051 / 100000)
      (255996826576829 / 100000) := by
  exact
    packedTile65536 2559885568 2560016640 14 6018 50595 31 _ _ (2166321 / 100000) (541581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2560016640 :
    ThetaLowerSegment 2560016640 2560147712 (255996826576829 / 100000)
      (256010002171561 / 100000) := by
  exact
    packedTile65536 2560016640 2560147712 14 6082 50596 31 _ _ (1083163 / 50000) (2166329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2560147712 :
    ThetaLowerSegment 2560147712 2560278784 (256010002171561 / 100000)
      (256023032658541 / 100000) := by
  exact
    packedTile65536 2560147712 2560278784 14 6015 50597 31 _ _ (541583 / 25000) (433267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2560278784 :
    ThetaLowerSegment 2560278784 2560409856 (256023032658541 / 100000) (3200450031477 / 1250) := by
  exact
    packedTile65536 2560278784 2560409856 14 5987 50599 31 _ _ (2166337 / 100000) (108317 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2560409856 :
    ThetaLowerSegment 2560409856 2560540928 (3200450031477 / 1250) (32006113156389 / 12500) := by
  exact
    packedTile65536 2560409856 2560540928 14 5956 50600 31 _ _ (1083171 / 50000) (433269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2560540928 :
    ThetaLowerSegment 2560540928 2560672000 (32006113156389 / 12500) (10242478646287 / 4000) := by
  exact
    packedTile65536 2560540928 2560672000 14 6029 50601 31 _ _ (2166347 / 100000) (43327 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2560672000 :
    ThetaLowerSegment 2560672000 2560803072 (10242478646287 / 4000) (256074977267287 / 100000) := by
  exact
    packedTile65536 2560672000 2560803072 14 6006 50603 31 _ _ (135397 / 6250) (433271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2560803072 :
    ThetaLowerSegment 2560803072 2560934144 (256074977267287 / 100000)
      (256088079394423 / 100000) := by
  exact
    packedTile65536 2560803072 2560934144 14 6048 50604 31 _ _ (2166357 / 100000) (54159 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2560934144 :
    ThetaLowerSegment 2560934144 2561065216 (256088079394423 / 100000)
      (256101289869899 / 100000) := by
  exact
    packedTile65536 2560934144 2561065216 14 6098 50605 31 _ _ (1083181 / 50000) (433273 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561065216 :
    ThetaLowerSegment 2561065216 2561196288 (256101289869899 / 100000)
      (256114387724781 / 100000) := by
  exact
    packedTile65536 2561065216 2561196288 14 6046 50606 31 _ _ (2166367 / 100000) (216637 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561196288 :
    ThetaLowerSegment 2561196288 2561327360 (256114387724781 / 100000) (6403188061107 / 2500) := by
  exact
    packedTile65536 2561196288 2561327360 14 6063 50608 31 _ _ (2166373 / 100000) (270797 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561327360 :
    ThetaLowerSegment 2561327360 2561458432 (6403188061107 / 2500) (128070241941927 / 50000) := by
  exact
    packedTile65536 2561327360 2561458432 14 5983 50609 31 _ _ (1083189 / 50000) (2166381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561458432 :
    ThetaLowerSegment 2561458432 2561589504 (128070241941927 / 50000)
      (128076810415183 / 50000) := by
  exact
    packedTile65536 2561458432 2561589504 14 6064 50610 31 _ _ (2166383 / 100000) (1083193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561589504 :
    ThetaLowerSegment 2561589504 2561720576 (128076810415183 / 50000)
      (128083468808701 / 50000) := by
  exact
    packedTile65536 2561589504 2561720576 14 6147 50612 31 _ _ (541597 / 25000) (2166391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561720576 :
    ThetaLowerSegment 2561720576 2561851648 (128083468808701 / 50000) (5123604612097 / 2000) := by
  exact
    packedTile65536 2561720576 2561851648 14 6136 50613 31 _ _ (2166393 / 100000) (541599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561851648 :
    ThetaLowerSegment 2561851648 2561982720 (5123604612097 / 2000) (64048343535379 / 25000) := by
  exact
    packedTile65536 2561851648 2561982720 14 6067 50614 31 _ _ (1083199 / 50000) (2166401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561982720 :
    ThetaLowerSegment 2561982720 2562113792 (64048343535379 / 25000) (128103266436669 / 50000) := by
  exact
    packedTile65536 2561982720 2562113792 14 6074 50616 31 _ _ (2166403 / 100000) (1083203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2562113792 :
    ThetaLowerSegment 2562113792 2562244864 (128103266436669 / 50000)
      (128109859899417 / 50000) := by
  exact
    packedTile65536 2562113792 2562244864 14 6087 50617 31 _ _ (270801 / 12500) (2166411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2562244864 :
    ThetaLowerSegment 2562244864 2562375936 (128109859899417 / 50000)
      (256232681447813 / 100000) := by
  exact
    packedTile65536 2562244864 2562375936 14 5983 50618 31 _ _ (2166413 / 100000) (135401 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2562375936 :
    ThetaLowerSegment 2562375936 2562507008 (256232681447813 / 100000)
      (128122795569317 / 50000) := by
  exact
    packedTile65536 2562375936 2562507008 14 5959 50619 31 _ _ (2166419 / 100000) (1083211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2562507008 :
    ThetaLowerSegment 2562507008 2562638080 (128122795569317 / 50000) (25625859834833 / 10000) := by
  exact
    packedTile65536 2562507008 2562638080 14 6004 50621 31 _ _ (270803 / 12500) (2166427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2562638080 :
    ThetaLowerSegment 2562638080 2562769152 (25625859834833 / 10000)
      (256271655415913 / 100000) := by
  exact
    packedTile65536 2562638080 2562769152 14 6027 50622 31 _ _ (2166429 / 100000) (67701 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2562769152 :
    ThetaLowerSegment 2562769152 2562900224 (256271655415913 / 100000)
      (51256973266089 / 20000) := by
  exact
    packedTile65536 2562769152 2562900224 14 6098 50623 31 _ _ (1083217 / 50000) (2166437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2562900224 :
    ThetaLowerSegment 2562900224 2563031296 (51256973266089 / 20000)
      (256297795638397 / 100000) := by
  exact
    packedTile65536 2562900224 2563031296 14 5968 50625 31 _ _ (2166439 / 100000) (1083221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2563031296 :
    ThetaLowerSegment 2563031296 2563162368 (256297795638397 / 100000)
      (256311075940117 / 100000) := by
  exact
    packedTile65536 2563031296 2563162368 14 6130 50626 31 _ _ (541611 / 25000) (2166447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2563162368 :
    ThetaLowerSegment 2563162368 2563293440 (256311075940117 / 100000)
      (256324044303831 / 100000) := by
  exact
    packedTile65536 2563162368 2563293440 14 5986 50627 31 _ _ (2166449 / 100000) (541613 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2563293440 :
    ThetaLowerSegment 2563293440 2563424512 (256324044303831 / 100000)
      (51267430703397 / 20000) := by
  exact
    packedTile65536 2563293440 2563424512 14 6051 50628 31 _ _ (1083227 / 50000) (2166457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2563424512 :
    ThetaLowerSegment 2563424512 2563555584 (51267430703397 / 20000) (32043785553123 / 12500) := by
  exact
    packedTile65536 2563424512 2563555584 14 6061 50630 31 _ _ (2166459 / 100000) (1083231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2563555584 :
    ThetaLowerSegment 2563555584 2563686656 (32043785553123 / 12500)
      (256363623349989 / 100000) := by
  exact
    packedTile65536 2563555584 2563686656 14 6157 50631 31 _ _ (433293 / 20000) (541617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2563686656 :
    ThetaLowerSegment 2563686656 2563817728 (256363623349989 / 100000)
      (256376780322299 / 100000) := by
  exact
    packedTile65536 2563686656 2563817728 14 6073 50632 31 _ _ (216647 / 10000) (2166473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2563817728 :
    ThetaLowerSegment 2563817728 2563948800 (256376780322299 / 100000)
      (128194886336437 / 50000) := by
  exact
    packedTile65536 2563817728 2563948800 14 5997 50634 31 _ _ (86659 / 4000) (1083239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2563948800 :
    ThetaLowerSegment 2563948800 2564079872 (128194886336437 / 50000)
      (128201437771957 / 50000) := by
  exact
    packedTile65536 2563948800 2564079872 14 6048 50635 31 _ _ (27081 / 1250) (2166483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2564079872 :
    ThetaLowerSegment 2564079872 2564210944 (128201437771957 / 50000)
      (128207967557747 / 50000) := by
  exact
    packedTile65536 2564079872 2564210944 14 6028 50636 31 _ _ (433297 / 20000) (270811 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2564210944 :
    ThetaLowerSegment 2564210944 2564342016 (128207967557747 / 50000)
      (128214618682047 / 50000) := by
  exact
    packedTile65536 2564210944 2564342016 14 6140 50638 31 _ _ (216649 / 10000) (2166493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2564342016 :
    ThetaLowerSegment 2564342016 2564473088 (128214618682047 / 50000) (32055302831583 / 12500) := by
  exact
    packedTile65536 2564342016 2564473088 14 6086 50639 31 _ _ (433299 / 20000) (1083249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2564473088 :
    ThetaLowerSegment 2564473088 2564604160 (32055302831583 / 12500) (64113892785291 / 25000) := by
  exact
    packedTile65536 2564473088 2564604160 14 6069 50640 31 _ _ (4333 / 200) (2166503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2564604160 :
    ThetaLowerSegment 2564604160 2564735232 (64113892785291 / 25000)
      (256468719660009 / 100000) := by
  exact
    packedTile65536 2564604160 2564735232 14 6069 50641 31 _ _ (433301 / 20000) (541627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2564735232 :
    ThetaLowerSegment 2564735232 2564866304 (256468719660009 / 100000)
      (256481640731613 / 100000) := by
  exact
    packedTile65536 2564735232 2564866304 14 5964 50643 31 _ _ (2166511 / 100000) (1083257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2564866304 :
    ThetaLowerSegment 2564866304 2564997376 (256481640731613 / 100000)
      (256494951805917 / 100000) := by
  exact
    packedTile65536 2564866304 2564997376 14 6144 50644 31 _ _ (541629 / 25000) (2166519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2564997376 :
    ThetaLowerSegment 2564997376 2565128448 (256494951805917 / 100000)
      (128254058877017 / 50000) := by
  exact
    packedTile65536 2564997376 2565128448 14 6077 50645 31 _ _ (2166521 / 100000) (541631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2565128448 :
    ThetaLowerSegment 2565128448 2565259520 (128254058877017 / 50000) (6413031226703 / 2500) := by
  exact
    packedTile65536 2565128448 2565259520 14 6061 50647 31 _ _ (1083263 / 50000) (2166529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2565259520 :
    ThetaLowerSegment 2565259520 2565390592 (6413031226703 / 2500) (12826714579237 / 5000) := by
  exact
    packedTile65536 2565259520 2565390592 14 6020 50648 31 _ _ (2166531 / 100000) (1083267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2565390592 :
    ThetaLowerSegment 2565390592 2565521664 (12826714579237 / 5000) (64136863864369 / 25000) := by
  exact
    packedTile65536 2565390592 2565521664 14 6076 50649 31 _ _ (270817 / 12500) (2166539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2565521664 :
    ThetaLowerSegment 2565521664 2565652736 (64136863864369 / 25000) (128280272849099 / 50000) := by
  exact
    packedTile65536 2565521664 2565652736 14 6042 50650 31 _ _ (2166541 / 100000) (135409 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2565652736 :
    ThetaLowerSegment 2565652736 2565783808 (128280272849099 / 50000) (16035864570301 / 6250) := by
  exact
    packedTile65536 2565652736 2565783808 14 6133 50652 31 _ _ (1083273 / 50000) (2166549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2565783808 :
    ThetaLowerSegment 2565783808 2565914880 (16035864570301 / 6250) (10263478410293 / 4000) := by
  exact
    packedTile65536 2565783808 2565914880 14 6059 50653 31 _ _ (2166551 / 100000) (1083277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2565914880 :
    ThetaLowerSegment 2565914880 2566045952 (10263478410293 / 4000) (64150034855889 / 25000) := by
  exact
    packedTile65536 2565914880 2566045952 14 6083 50654 31 _ _ (2166557 / 100000) (13541 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2566045952 :
    ThetaLowerSegment 2566045952 2566177024 (64150034855889 / 25000) (64153319363881 / 25000) := by
  exact
    packedTile65536 2566045952 2566177024 14 6064 50656 31 _ _ (1083281 / 50000) (433313 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2566177024 :
    ThetaLowerSegment 2566177024 2566308096 (64153319363881 / 25000) (16039142845237 / 6250) := by
  exact
    packedTile65536 2566177024 2566308096 14 6004 50657 31 _ _ (2166567 / 100000) (216657 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2566308096 :
    ThetaLowerSegment 2566308096 2566439168 (16039142845237 / 6250) (64159867278603 / 25000) := by
  exact
    packedTile65536 2566308096 2566439168 14 6085 50658 31 _ _ (541643 / 25000) (86663 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2566439168 :
    ThetaLowerSegment 2566439168 2566570240 (64159867278603 / 25000)
      (256652605070763 / 100000) := by
  exact
    packedTile65536 2566439168 2566570240 14 6063 50660 31 _ _ (2166577 / 100000) (108329 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2566570240 :
    ThetaLowerSegment 2566570240 2566701312 (256652605070763 / 100000)
      (256665702058953 / 100000) := by
  exact
    packedTile65536 2566570240 2566701312 14 6045 50661 31 _ _ (1083291 / 50000) (433317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2566701312 :
    ThetaLowerSegment 2566701312 2566832384 (256665702058953 / 100000)
      (256678814243477 / 100000) := by
  exact
    packedTile65536 2566701312 2566832384 14 6052 50662 31 _ _ (2166587 / 100000) (216659 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2566832384 :
    ThetaLowerSegment 2566832384 2566963456 (256678814243477 / 100000) (10267678531613 / 4000) := by
  exact
    packedTile65536 2566832384 2566963456 14 6069 50663 31 _ _ (67706 / 3125) (433319 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2566963456 :
    ThetaLowerSegment 2566963456 2567094528 (10267678531613 / 4000) (256704923873579 / 100000) := by
  exact
    packedTile65536 2566963456 2567094528 14 5982 50665 31 _ _ (2166597 / 100000) (10833 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2567094528 :
    ThetaLowerSegment 2567094528 2567225600 (256704923873579 / 100000) (2053743942583 / 800) := by
  exact
    packedTile65536 2567094528 2567225600 14 6032 50666 31 _ _ (2166603 / 100000) (1083303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2567225600 :
    ThetaLowerSegment 2567225600 2567356672 (2053743942583 / 800) (256731059635723 / 100000) := by
  exact
    packedTile65536 2567225600 2567356672 14 6031 50667 31 _ _ (135413 / 6250) (2166611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2567356672 :
    ThetaLowerSegment 2567356672 2567487744 (256731059635723 / 100000)
      (256744258642119 / 100000) := by
  exact
    packedTile65536 2567356672 2567487744 14 6092 50669 31 _ _ (2166613 / 100000) (270827 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2567487744 :
    ThetaLowerSegment 2567487744 2567618816 (256744258642119 / 100000)
      (256757303849097 / 100000) := by
  exact
    packedTile65536 2567487744 2567618816 14 6021 50670 31 _ _ (1083309 / 50000) (2166621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2567618816 :
    ThetaLowerSegment 2567618816 2567749888 (256757303849097 / 100000)
      (64192634937251 / 25000) := by
  exact
    packedTile65536 2567618816 2567749888 14 6109 50671 31 _ _ (2166623 / 100000) (1083313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2567749888 :
    ThetaLowerSegment 2567749888 2567880960 (64192634937251 / 25000) (64195906545531 / 25000) := by
  exact
    packedTile65536 2567749888 2567880960 14 6040 50672 31 _ _ (541657 / 25000) (2166631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2567880960 :
    ThetaLowerSegment 2567880960 2568012032 (64195906545531 / 25000) (128398406155281 / 50000) := by
  exact
    packedTile65536 2567880960 2568012032 14 6086 50674 31 _ _ (2166633 / 100000) (541659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2568012032 :
    ThetaLowerSegment 2568012032 2568143104 (128398406155281 / 50000) (32101236538021 / 12500) := by
  exact
    packedTile65536 2568012032 2568143104 14 6037 50675 31 _ _ (1083319 / 50000) (2166641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2568143104 :
    ThetaLowerSegment 2568143104 2568274176 (32101236538021 / 12500)
      (256822850995951 / 100000) := by
  exact
    packedTile65536 2568143104 2568274176 14 5981 50676 31 _ _ (2166643 / 100000) (1083323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2568274176 :
    ThetaLowerSegment 2568274176 2568405248 (256822850995951 / 100000)
      (256836035049031 / 100000) := by
  exact
    packedTile65536 2568274176 2568405248 14 6085 50678 31 _ _ (270831 / 12500) (2166651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2568405248 :
    ThetaLowerSegment 2568405248 2568536320 (256836035049031 / 100000)
      (51369820427861 / 20000) := by
  exact
    packedTile65536 2568405248 2568536320 14 6031 50679 31 _ _ (1083327 / 50000) (2166657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2568536320 :
    ThetaLowerSegment 2568536320 2568667392 (51369820427861 / 20000) (128431084629867 / 50000) := by
  exact
    packedTile65536 2568536320 2568667392 14 6031 50680 31 _ _ (2166659 / 100000) (1083331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2568667392 :
    ThetaLowerSegment 2568667392 2568798464 (128431084629867 / 50000)
      (128437703788387 / 50000) := by
  exact
    packedTile65536 2568667392 2568798464 14 6110 50682 31 _ _ (270833 / 12500) (2166667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2568798464 :
    ThetaLowerSegment 2568798464 2568929536 (128437703788387 / 50000)
      (256888630757681 / 100000) := by
  exact
    packedTile65536 2568798464 2568929536 14 6103 50683 31 _ _ (2166669 / 100000) (135417 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2568929536 :
    ThetaLowerSegment 2568929536 2569060608 (256888630757681 / 100000)
      (256901658968443 / 100000) := by
  exact
    packedTile65536 2568929536 2569060608 14 6013 50684 31 _ _ (1083337 / 50000) (2166677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569060608 :
    ThetaLowerSegment 2569060608 2569191680 (256901658968443 / 100000)
      (128457460605301 / 50000) := by
  exact
    packedTile65536 2569060608 2569191680 14 6121 50685 31 _ _ (2166679 / 100000) (1083341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569191680 :
    ThetaLowerSegment 2569191680 2569322752 (128457460605301 / 50000)
      (128464019157769 / 50000) := by
  exact
    packedTile65536 2569191680 2569322752 14 6054 50687 31 _ _ (541671 / 25000) (2166687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569322752 :
    ThetaLowerSegment 2569322752 2569339136 (128464019157769 / 50000) (64232400666249 / 25000) := by
  exact
    packedTile65536 2569322752 2569339136 11 722 50688 31 _ _ (2166689 / 100000) (541673 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569339136 :
    ThetaLowerSegment 2569339136 2569341184 (64232400666249 / 25000) (128464904250273 / 50000) := by
  exact
    packedTile65536 2569339136 2569341184 8 95 50688 31 _ _ (216669 / 10000) (2166693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2537341184_2569341184 :
    ThetaLowerSegment 2537341184 2569341184 (253728455215421 / 100000)
      (128464904250273 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2537341184 cell2537472256)
                  (ThetaLowerSegment.join cell2537603328 cell2537734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2537865472 cell2537996544)
                  (ThetaLowerSegment.join cell2538127616 cell2538258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2538389760 cell2538520832)
                  (ThetaLowerSegment.join cell2538651904 cell2538782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2538914048 cell2539045120)
                  (ThetaLowerSegment.join cell2539176192 cell2539307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2539438336 cell2539569408)
                  (ThetaLowerSegment.join cell2539700480 cell2539831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2539962624 cell2540093696)
                  (ThetaLowerSegment.join cell2540224768 cell2540355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2540486912 cell2540617984)
                  (ThetaLowerSegment.join cell2540749056 cell2540880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2541011200 cell2541142272)
                  (ThetaLowerSegment.join cell2541273344 cell2541404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2541535488 cell2541666560)
                  (ThetaLowerSegment.join cell2541797632 cell2541928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2542059776 cell2542190848)
                  (ThetaLowerSegment.join cell2542321920 cell2542452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2542584064 cell2542715136)
                  (ThetaLowerSegment.join cell2542846208 cell2542977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2543108352 cell2543239424)
                  (ThetaLowerSegment.join cell2543370496 cell2543501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2543632640 cell2543763712)
                  (ThetaLowerSegment.join cell2543894784 cell2544025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2544156928 cell2544288000)
                  (ThetaLowerSegment.join cell2544419072 cell2544550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2544681216 cell2544812288)
                  (ThetaLowerSegment.join cell2544943360 cell2545074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2545205504 cell2545336576)
                  (ThetaLowerSegment.join cell2545467648 cell2545598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2545729792 cell2545860864)
                  (ThetaLowerSegment.join cell2545991936 cell2546123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2546254080 cell2546385152)
                  (ThetaLowerSegment.join cell2546516224 cell2546647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2546778368 cell2546909440)
                  (ThetaLowerSegment.join cell2547040512 cell2547171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2547302656 cell2547433728)
                  (ThetaLowerSegment.join cell2547564800 cell2547695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2547826944 cell2547958016)
                  (ThetaLowerSegment.join cell2548089088 cell2548220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2548351232 cell2548482304)
                  (ThetaLowerSegment.join cell2548613376 cell2548744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2548875520 cell2549006592)
                  (ThetaLowerSegment.join cell2549137664 cell2549268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2549399808 cell2549530880)
                  (ThetaLowerSegment.join cell2549661952 cell2549793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2549924096 cell2550055168)
                  (ThetaLowerSegment.join cell2550186240 cell2550317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2550448384 cell2550579456)
                  (ThetaLowerSegment.join cell2550710528 cell2550841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2550972672 cell2551103744)
                  (ThetaLowerSegment.join cell2551234816 cell2551365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2551496960 cell2551628032)
                  (ThetaLowerSegment.join cell2551759104 cell2551890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2552021248 cell2552152320)
                  (ThetaLowerSegment.join cell2552283392 cell2552414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2552545536 cell2552676608)
                  (ThetaLowerSegment.join cell2552807680 cell2552938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2553069824 cell2553200896)
                  (ThetaLowerSegment.join cell2553331968 cell2553463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2553594112 cell2553725184)
                  (ThetaLowerSegment.join cell2553856256 cell2553987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2554118400 cell2554249472)
                  (ThetaLowerSegment.join cell2554380544 cell2554511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2554642688 cell2554773760)
                  (ThetaLowerSegment.join cell2554904832 cell2555035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2555166976 cell2555298048)
                  (ThetaLowerSegment.join cell2555429120 cell2555560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2555691264 cell2555822336)
                  (ThetaLowerSegment.join cell2555953408 cell2556084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2556215552 cell2556346624)
                  (ThetaLowerSegment.join cell2556477696 cell2556608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2556739840 cell2556870912)
                  (ThetaLowerSegment.join cell2557001984 cell2557133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2557264128 cell2557395200)
                  (ThetaLowerSegment.join cell2557526272 cell2557657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2557788416 cell2557919488)
                  (ThetaLowerSegment.join cell2558050560 cell2558181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2558312704 cell2558443776)
                  (ThetaLowerSegment.join cell2558574848 cell2558705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2558836992 cell2558968064)
                  (ThetaLowerSegment.join cell2559099136 cell2559230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2559361280 cell2559492352)
                  (ThetaLowerSegment.join cell2559623424 cell2559754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2559885568 cell2560016640)
                  (ThetaLowerSegment.join cell2560147712 cell2560278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2560409856 cell2560540928)
                  (ThetaLowerSegment.join cell2560672000 cell2560803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2560934144 cell2561065216)
                  (ThetaLowerSegment.join cell2561196288 cell2561327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2561458432 cell2561589504)
                  (ThetaLowerSegment.join cell2561720576 cell2561851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2561982720 cell2562113792)
                  (ThetaLowerSegment.join cell2562244864 cell2562375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2562507008 cell2562638080)
                  (ThetaLowerSegment.join cell2562769152 cell2562900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2563031296 cell2563162368)
                  (ThetaLowerSegment.join cell2563293440 cell2563424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2563555584 cell2563686656)
                  (ThetaLowerSegment.join cell2563817728 cell2563948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2564079872 cell2564210944)
                  (ThetaLowerSegment.join cell2564342016 cell2564473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2564604160 cell2564735232)
                  (ThetaLowerSegment.join cell2564866304 cell2564997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2565128448 cell2565259520)
                  (ThetaLowerSegment.join cell2565390592 cell2565521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2565652736 cell2565783808)
                  (ThetaLowerSegment.join cell2565914880 cell2566045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2566177024 cell2566308096)
                  (ThetaLowerSegment.join cell2566439168 cell2566570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2566701312 cell2566832384)
                  (ThetaLowerSegment.join cell2566963456 cell2567094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2567225600 cell2567356672)
                  (ThetaLowerSegment.join cell2567487744 cell2567618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2567749888 cell2567880960)
                  (ThetaLowerSegment.join cell2568012032 cell2568143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2568274176 cell2568405248)
                  (ThetaLowerSegment.join cell2568536320 cell2568667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2568798464 cell2568929536)
                (ThetaLowerSegment.join cell2569060608 cell2569191680))
              (ThetaLowerSegment.join cell2569322752 cell2569339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
