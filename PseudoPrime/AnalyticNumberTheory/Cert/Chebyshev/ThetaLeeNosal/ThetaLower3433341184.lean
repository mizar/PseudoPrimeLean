/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3433341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3401341184 :
    ThetaLowerSegment 3401341184 3401472256 (340124585378599 / 100000)
      (340137565082787 / 100000) := by
  exact
    packedTile65536 3401341184 3401472256 14 5914 58321 32 _ _ (1097371 / 50000) (438949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401472256 :
    ThetaLowerSegment 3401472256 3401603328 (340137565082787 / 100000)
      (340150518473679 / 100000) := by
  exact
    packedTile65536 3401472256 3401603328 14 5902 58322 32 _ _ (1097373 / 50000) (2194749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401603328 :
    ThetaLowerSegment 3401603328 3401734400 (340150518473679 / 100000)
      (340163796711179 / 100000) := by
  exact
    packedTile65536 3401603328 3401734400 14 6050 58323 32 _ _ (8779 / 400) (2194753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401734400 :
    ThetaLowerSegment 3401734400 3401865472 (340163796711179 / 100000)
      (340176925729607 / 100000) := by
  exact
    packedTile65536 3401734400 3401865472 14 5982 58324 32 _ _ (1097377 / 50000) (2194757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401865472 :
    ThetaLowerSegment 3401865472 3401996544 (340176925729607 / 100000)
      (85047510948049 / 25000) := by
  exact
    packedTile65536 3401865472 3401996544 14 5977 58325 32 _ _ (2194757 / 100000) (54869 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401996544 :
    ThetaLowerSegment 3401996544 3402127616 (85047510948049 / 25000) (850507833367 / 250) := by
  exact
    packedTile65536 3401996544 3402127616 14 5964 58326 32 _ _ (2194761 / 100000) (548691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3402127616 :
    ThetaLowerSegment 3402127616 3402258688 (850507833367 / 250) (68043228343791 / 20000) := by
  exact
    packedTile65536 3402127616 3402258688 14 5927 58327 32 _ _ (438953 / 20000) (137173 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3402258688 :
    ThetaLowerSegment 3402258688 3402389760 (68043228343791 / 20000) (85057301794703 / 25000) := by
  exact
    packedTile65536 3402258688 3402389760 14 5953 58328 32 _ _ (2194769 / 100000) (548693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3402389760 :
    ThetaLowerSegment 3402389760 3402520832 (85057301794703 / 25000) (34024247677637 / 10000) := by
  exact
    packedTile65536 3402389760 3402520832 14 6046 58330 32 _ _ (2194773 / 100000) (274347 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3402520832 :
    ThetaLowerSegment 3402520832 3402651904 (34024247677637 / 10000)
      (340255647633147 / 100000) := by
  exact
    packedTile65536 3402520832 3402651904 14 6001 58331 32 _ _ (2194777 / 100000) (109739 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3402651904 :
    ThetaLowerSegment 3402651904 3402782976 (340255647633147 / 100000)
      (340268522218493 / 100000) := by
  exact
    packedTile65536 3402651904 3402782976 14 5866 58332 32 _ _ (2194781 / 100000) (68587 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3402782976 :
    ThetaLowerSegment 3402782976 3402914048 (340268522218493 / 100000)
      (68056372423129 / 20000) := by
  exact
    packedTile65536 3402782976 3402914048 14 6078 58333 32 _ _ (68587 / 3125) (2194787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3402914048 :
    ThetaLowerSegment 3402914048 3403045120 (68056372423129 / 20000) (68059045674913 / 20000) := by
  exact
    packedTile65536 3402914048 3403045120 14 6090 58334 32 _ _ (548697 / 25000) (2194791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3403045120 :
    ThetaLowerSegment 3403045120 3403176192 (68059045674913 / 20000)
      (340308383957813 / 100000) := by
  exact
    packedTile65536 3403045120 3403176192 14 5994 58335 32 _ _ (274349 / 12500) (438959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3403176192 :
    ThetaLowerSegment 3403176192 3403307264 (340308383957813 / 100000)
      (340321451773197 / 100000) := by
  exact
    packedTile65536 3403176192 3403307264 14 5954 58336 32 _ _ (548699 / 25000) (2194799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3403307264 :
    ThetaLowerSegment 3403307264 3403438336 (340321451773197 / 100000)
      (340334392313997 / 100000) := by
  exact
    packedTile65536 3403307264 3403438336 14 5896 58337 32 _ _ (5487 / 250) (2194803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3403438336 :
    ThetaLowerSegment 3403438336 3403569408 (340334392313997 / 100000)
      (340347591865253 / 100000) := by
  exact
    packedTile65536 3403438336 3403569408 14 6014 58338 32 _ _ (548701 / 25000) (2194807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3403569408 :
    ThetaLowerSegment 3403569408 3403700480 (340347591865253 / 100000)
      (340360596102653 / 100000) := by
  exact
    packedTile65536 3403569408 3403700480 14 5925 58340 32 _ _ (274351 / 12500) (2194811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3403700480 :
    ThetaLowerSegment 3403700480 3403831552 (340360596102653 / 100000)
      (170186819932213 / 50000) := by
  exact
    packedTile65536 3403700480 3403831552 14 5943 58341 32 _ _ (2194811 / 100000) (1097407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3403831552 :
    ThetaLowerSegment 3403831552 3403962624 (170186819932213 / 50000)
      (340386666091451 / 100000) := by
  exact
    packedTile65536 3403831552 3403962624 14 5935 58342 32 _ _ (438963 / 20000) (1097409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3403962624 :
    ThetaLowerSegment 3403962624 3404093696 (340386666091451 / 100000)
      (68079974024511 / 20000) := by
  exact
    packedTile65536 3403962624 3404093696 14 6016 58343 32 _ _ (2194819 / 100000) (1097411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3404093696 :
    ThetaLowerSegment 3404093696 3404224768 (68079974024511 / 20000) (170206533796627 / 50000) := by
  exact
    packedTile65536 3404093696 3404224768 14 6013 58344 32 _ _ (2194823 / 100000) (1097413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3404224768 :
    ThetaLowerSegment 3404224768 3404355840 (170206533796627 / 50000) (85106516339687 / 25000) := by
  exact
    packedTile65536 3404224768 3404355840 14 5922 58345 32 _ _ (2194827 / 100000) (219483 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3404355840 :
    ThetaLowerSegment 3404355840 3404486912 (85106516339687 / 25000)
      (340439065342761 / 100000) := by
  exact
    packedTile65536 3404355840 3404486912 14 5923 58346 32 _ _ (2194831 / 100000) (1097417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3404486912 :
    ThetaLowerSegment 3404486912 3404617984 (340439065342761 / 100000)
      (340452067545301 / 100000) := by
  exact
    packedTile65536 3404486912 3404617984 14 5924 58347 32 _ _ (438967 / 20000) (1097419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3404617984 :
    ThetaLowerSegment 3404617984 3404749056 (340452067545301 / 100000)
      (340465322171983 / 100000) := by
  exact
    packedTile65536 3404617984 3404749056 14 6039 58349 32 _ _ (1097419 / 50000) (2194841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3404749056 :
    ThetaLowerSegment 3404749056 3404880128 (340465322171983 / 100000)
      (340478322221149 / 100000) := by
  exact
    packedTile65536 3404749056 3404880128 14 5923 58350 32 _ _ (1097421 / 50000) (438969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3404880128 :
    ThetaLowerSegment 3404880128 3405011200 (340478322221149 / 100000)
      (340491335463083 / 100000) := by
  exact
    packedTile65536 3404880128 3405011200 14 5929 58351 32 _ _ (1097423 / 50000) (2194849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3405011200 :
    ThetaLowerSegment 3405011200 3405142272 (340491335463083 / 100000)
      (340504664787133 / 100000) := by
  exact
    packedTile65536 3405011200 3405142272 14 6073 58352 32 _ _ (43897 / 2000) (2194853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3405142272 :
    ThetaLowerSegment 3405142272 3405273344 (340504664787133 / 100000)
      (340517772455221 / 100000) := by
  exact
    packedTile65536 3405142272 3405273344 14 5972 58353 32 _ _ (1097427 / 50000) (2194857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3405273344 :
    ThetaLowerSegment 3405273344 3405404416 (340517772455221 / 100000)
      (340530851614043 / 100000) := by
  exact
    packedTile65536 3405273344 3405404416 14 5959 58354 32 _ _ (1097429 / 50000) (2194861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3405404416 :
    ThetaLowerSegment 3405404416 3405535488 (340530851614043 / 100000)
      (340543880308939 / 100000) := by
  exact
    packedTile65536 3405404416 3405535488 14 5936 58355 32 _ _ (2194861 / 100000) (137179 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3405535488 :
    ThetaLowerSegment 3405535488 3405666560 (340543880308939 / 100000)
      (340557150462729 / 100000) := by
  exact
    packedTile65536 3405535488 3405666560 14 6046 58356 32 _ _ (438973 / 20000) (548717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3405666560 :
    ThetaLowerSegment 3405666560 3405797632 (340557150462729 / 100000)
      (68114043742551 / 20000) := by
  exact
    packedTile65536 3405666560 3405797632 14 5954 58358 32 _ _ (2194869 / 100000) (274359 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3405797632 :
    ThetaLowerSegment 3405797632 3405928704 (68114043742551 / 20000)
      (340583164073709 / 100000) := by
  exact
    packedTile65536 3405797632 3405928704 14 5898 58359 32 _ _ (2194873 / 100000) (548719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3405928704 :
    ThetaLowerSegment 3405928704 3406059776 (340583164073709 / 100000)
      (42574517248957 / 12500) := by
  exact
    packedTile65536 3405928704 3406059776 14 5911 58360 32 _ _ (2194877 / 100000) (13718 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3406059776 :
    ThetaLowerSegment 3406059776 3406190848 (42574517248957 / 12500) (42576163409707 / 12500) := by
  exact
    packedTile65536 3406059776 3406190848 14 6000 58361 32 _ _ (2194881 / 100000) (548721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3406190848 :
    ThetaLowerSegment 3406190848 3406321920 (42576163409707 / 12500) (170311152693313 / 50000) := by
  exact
    packedTile65536 3406190848 3406321920 14 5922 58362 32 _ _ (438977 / 20000) (274361 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3406321920 :
    ThetaLowerSegment 3406321920 3406452992 (170311152693313 / 50000)
      (170317765890857 / 50000) := by
  exact
    packedTile65536 3406321920 3406452992 14 6026 58363 32 _ _ (274361 / 12500) (2194891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3406452992 :
    ThetaLowerSegment 3406452992 3406584064 (170317765890857 / 50000)
      (170324226555459 / 50000) := by
  exact
    packedTile65536 3406452992 3406584064 14 5887 58364 32 _ _ (548723 / 25000) (438979 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3406584064 :
    ThetaLowerSegment 3406584064 3406715136 (170324226555459 / 50000)
      (170330809048563 / 50000) := by
  exact
    packedTile65536 3406584064 3406715136 14 5998 58365 32 _ _ (137181 / 6250) (2194899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3406715136 :
    ThetaLowerSegment 3406715136 3406846208 (170330809048563 / 50000)
      (170337334486263 / 50000) := by
  exact
    packedTile65536 3406715136 3406846208 14 5946 58367 32 _ _ (21949 / 1000) (2194903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3406846208 :
    ThetaLowerSegment 3406846208 3406977280 (170337334486263 / 50000)
      (170343874202731 / 50000) := by
  exact
    packedTile65536 3406846208 3406977280 14 5959 58368 32 _ _ (274363 / 12500) (2194907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3406977280 :
    ThetaLowerSegment 3406977280 3407108352 (170343874202731 / 50000)
      (170350406248939 / 50000) := by
  exact
    packedTile65536 3406977280 3407108352 14 5952 58369 32 _ _ (548727 / 25000) (2194911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3407108352 :
    ThetaLowerSegment 3407108352 3407239424 (170350406248939 / 50000) (68142777516541 / 20000) := by
  exact
    packedTile65536 3407108352 3407239424 14 5957 58370 32 _ _ (2194911 / 100000) (1097457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3407239424 :
    ThetaLowerSegment 3407239424 3407370496 (68142777516541 / 20000) (68145407902677 / 20000) := by
  exact
    packedTile65536 3407239424 3407370496 14 5992 58371 32 _ _ (438983 / 20000) (1097459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3407370496 :
    ThetaLowerSegment 3407370496 3407501568 (68145407902677 / 20000)
      (340740288044469 / 100000) := by
  exact
    packedTile65536 3407370496 3407501568 14 6036 58372 32 _ _ (2194919 / 100000) (1097461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3407501568 :
    ThetaLowerSegment 3407501568 3407632640 (340740288044469 / 100000)
      (42594171497559 / 12500) := by
  exact
    packedTile65536 3407501568 3407632640 14 5961 58373 32 _ _ (2194923 / 100000) (1097463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3407632640 :
    ThetaLowerSegment 3407632640 3407763712 (42594171497559 / 12500)
      (340766455940319 / 100000) := by
  exact
    packedTile65536 3407632640 3407763712 14 5961 58374 32 _ _ (2194927 / 100000) (219493 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3407763712 :
    ThetaLowerSegment 3407763712 3407894784 (340766455940319 / 100000)
      (170389831420073 / 50000) := by
  exact
    packedTile65536 3407763712 3407894784 14 6017 58376 32 _ _ (2194931 / 100000) (1097467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3407894784 :
    ThetaLowerSegment 3407894784 3408025856 (170389831420073 / 50000)
      (340792760017291 / 100000) := by
  exact
    packedTile65536 3407894784 3408025856 14 5967 58377 32 _ _ (438987 / 20000) (1097469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3408025856 :
    ThetaLowerSegment 3408025856 3408156928 (340792760017291 / 100000)
      (340805828678143 / 100000) := by
  exact
    packedTile65536 3408025856 3408156928 14 5954 58378 32 _ _ (1097469 / 50000) (2194941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3408156928 :
    ThetaLowerSegment 3408156928 3408288000 (340805828678143 / 100000)
      (340819046618867 / 100000) := by
  exact
    packedTile65536 3408156928 3408288000 14 6022 58379 32 _ _ (1097471 / 50000) (438989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3408288000 :
    ThetaLowerSegment 3408288000 3408419072 (340819046618867 / 100000)
      (340831977045753 / 100000) := by
  exact
    packedTile65536 3408288000 3408419072 14 5891 58380 32 _ _ (1097473 / 50000) (2194949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3408419072 :
    ThetaLowerSegment 3408419072 3408550144 (340831977045753 / 100000)
      (340845089677053 / 100000) := by
  exact
    packedTile65536 3408419072 3408550144 14 5974 58381 32 _ _ (43899 / 2000) (2194953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3408550144 :
    ThetaLowerSegment 3408550144 3408681216 (340845089677053 / 100000)
      (68171664171953 / 20000) := by
  exact
    packedTile65536 3408550144 3408681216 14 6028 58382 32 _ _ (1097477 / 50000) (2194957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3408681216 :
    ThetaLowerSegment 3408681216 3408812288 (68171664171953 / 20000)
      (340871330375831 / 100000) := by
  exact
    packedTile65536 3408681216 3408812288 14 5927 58383 32 _ _ (1097479 / 50000) (2194961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3408812288 :
    ThetaLowerSegment 3408812288 3408943360 (340871330375831 / 100000)
      (34088449794687 / 10000) := by
  exact
    packedTile65536 3408812288 3408943360 14 5999 58385 32 _ _ (2194961 / 100000) (548741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3408943360 :
    ThetaLowerSegment 3408943360 3409074432 (34088449794687 / 10000) (17044888435263 / 5000) := by
  exact
    packedTile65536 3408943360 3409074432 14 6046 58386 32 _ _ (438993 / 20000) (274371 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3409074432 :
    ThetaLowerSegment 3409074432 3409205504 (17044888435263 / 5000) (21306927621289 / 6250) := by
  exact
    packedTile65536 3409074432 3409205504 14 5956 58387 32 _ _ (2194969 / 100000) (548743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3409205504 :
    ThetaLowerSegment 3409205504 3409336576 (21306927621289 / 6250) (85231022699413 / 25000) := by
  exact
    packedTile65536 3409205504 3409336576 14 6036 58388 32 _ _ (2194973 / 100000) (68593 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3409336576 :
    ThetaLowerSegment 3409336576 3409467648 (85231022699413 / 25000) (170468474486459 / 50000) := by
  exact
    packedTile65536 3409336576 3409467648 14 5858 58389 32 _ _ (2194977 / 100000) (109749 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3409467648 :
    ThetaLowerSegment 3409467648 3409598720 (170468474486459 / 50000)
      (170475033089687 / 50000) := by
  exact
    packedTile65536 3409467648 3409598720 14 5976 58390 32 _ _ (2194981 / 100000) (274373 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3409598720 :
    ThetaLowerSegment 3409598720 3409729792 (170475033089687 / 50000) (85240785975001 / 25000) := by
  exact
    packedTile65536 3409598720 3409729792 14 5958 58391 32 _ _ (438997 / 20000) (548747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3409729792 :
    ThetaLowerSegment 3409729792 3409860864 (85240785975001 / 25000) (17048813715911 / 5000) := by
  exact
    packedTile65536 3409729792 3409860864 14 5982 58392 32 _ _ (548747 / 25000) (2194991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3409860864 :
    ThetaLowerSegment 3409860864 3409991936 (17048813715911 / 5000) (85247359970059 / 25000) := by
  exact
    packedTile65536 3409860864 3409991936 14 5998 58394 32 _ _ (137187 / 6250) (438999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3409991936 :
    ThetaLowerSegment 3409991936 3410123008 (85247359970059 / 25000) (85250648074067 / 25000) := by
  exact
    packedTile65536 3409991936 3410123008 14 5992 58395 32 _ _ (548749 / 25000) (2194999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3410123008 :
    ThetaLowerSegment 3410123008 3410254080 (85250648074067 / 25000) (85253868139067 / 25000) := by
  exact
    packedTile65536 3410123008 3410254080 14 5868 58396 32 _ _ (439 / 20) (2195003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3410254080 :
    ThetaLowerSegment 3410254080 3410385152 (85253868139067 / 25000) (17051419836991 / 5000) := by
  exact
    packedTile65536 3410254080 3410385152 14 5888 58397 32 _ _ (548751 / 25000) (2195007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3410385152 :
    ThetaLowerSegment 3410385152 3410516224 (17051419836991 / 5000) (85260435048363 / 25000) := by
  exact
    packedTile65536 3410385152 3410516224 14 6079 58398 32 _ _ (68594 / 3125) (2195011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3410516224 :
    ThetaLowerSegment 3410516224 3410647296 (85260435048363 / 25000) (68210996538963 / 20000) := by
  exact
    packedTile65536 3410516224 3410647296 14 6033 58399 32 _ _ (2195011 / 100000) (1097507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3410647296 :
    ThetaLowerSegment 3410647296 3410778368 (68210996538963 / 20000) (68213606850801 / 20000) := by
  exact
    packedTile65536 3410647296 3410778368 14 5946 58400 32 _ _ (439003 / 20000) (1097509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3410778368 :
    ThetaLowerSegment 3410778368 3410909440 (68213606850801 / 20000) (170540495725581 / 50000) := by
  exact
    packedTile65536 3410778368 3410909440 14 5903 58401 32 _ _ (2195019 / 100000) (1097511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3410909440 :
    ThetaLowerSegment 3410909440 3411040512 (170540495725581 / 50000)
      (341094093543449 / 100000) := by
  exact
    packedTile65536 3410909440 3411040512 14 5969 58402 32 _ _ (2195023 / 100000) (1097513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3411040512 :
    ThetaLowerSegment 3411040512 3411171584 (341094093543449 / 100000)
      (170553582464617 / 50000) := by
  exact
    packedTile65536 3411040512 3411171584 14 5955 58404 32 _ _ (2195027 / 100000) (219503 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3411171584 :
    ThetaLowerSegment 3411171584 3411302656 (170553582464617 / 50000) (426400380481 / 125) := by
  exact
    packedTile65536 3411171584 3411302656 14 5986 58405 32 _ _ (2195031 / 100000) (1097517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3411302656 :
    ThetaLowerSegment 3411302656 3411433728 (426400380481 / 125) (68226674285631 / 20000) := by
  exact
    packedTile65536 3411302656 3411433728 14 5953 58406 32 _ _ (439007 / 20000) (1097519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3411433728 :
    ThetaLowerSegment 3411433728 3411564800 (68226674285631 / 20000)
      (341146620677523 / 100000) := by
  exact
    packedTile65536 3411433728 3411564800 14 6036 58407 32 _ _ (1097519 / 50000) (2195041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3411564800 :
    ThetaLowerSegment 3411564800 3411695872 (341146620677523 / 100000)
      (341159755808851 / 100000) := by
  exact
    packedTile65536 3411564800 3411695872 14 5984 58408 32 _ _ (1097521 / 50000) (439009 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3411695872 :
    ThetaLowerSegment 3411695872 3411826944 (341159755808851 / 100000)
      (341172855843379 / 100000) := by
  exact
    packedTile65536 3411695872 3411826944 14 5968 58409 32 _ _ (1097523 / 50000) (2195049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3411826944 :
    ThetaLowerSegment 3411826944 3411958016 (341172855843379 / 100000)
      (341185896635429 / 100000) := by
  exact
    packedTile65536 3411826944 3411958016 14 5941 58410 32 _ _ (43901 / 2000) (2195053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3411958016 :
    ThetaLowerSegment 3411958016 3412089088 (341185896635429 / 100000)
      (341198981352323 / 100000) := by
  exact
    packedTile65536 3411958016 3412089088 14 5961 58411 32 _ _ (1097527 / 50000) (2195057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3412089088 :
    ThetaLowerSegment 3412089088 3412220160 (341198981352323 / 100000)
      (341212081458467 / 100000) := by
  exact
    packedTile65536 3412089088 3412220160 14 5968 58413 32 _ _ (1097529 / 50000) (2195061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3412220160 :
    ThetaLowerSegment 3412220160 3412351232 (341212081458467 / 100000)
      (85306311309821 / 25000) := by
  exact
    packedTile65536 3412220160 3412351232 14 5997 58414 32 _ _ (2195061 / 100000) (274383 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3412351232 :
    ThetaLowerSegment 3412351232 3412482304 (85306311309821 / 25000)
      (341238198317849 / 100000) := by
  exact
    packedTile65536 3412351232 3412482304 14 5901 58415 32 _ _ (439013 / 20000) (548767 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3412482304 :
    ThetaLowerSegment 3412482304 3412613376 (341238198317849 / 100000) (17062568326839 / 5000) := by
  exact
    packedTile65536 3412482304 3412613376 14 5999 58416 32 _ _ (2195069 / 100000) (68596 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3412613376 :
    ThetaLowerSegment 3412613376 3412744448 (17062568326839 / 5000) (170632253121879 / 50000) := by
  exact
    packedTile65536 3412613376 3412744448 14 5986 58417 32 _ _ (2195073 / 100000) (548769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3412744448 :
    ThetaLowerSegment 3412744448 3412875520 (170632253121879 / 50000)
      (170638741769491 / 50000) := by
  exact
    packedTile65536 3412744448 3412875520 14 5912 58418 32 _ _ (2195077 / 100000) (54877 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3412875520 :
    ThetaLowerSegment 3412875520 3413006592 (170638741769491 / 50000)
      (170645305061681 / 50000) := by
  exact
    packedTile65536 3412875520 3413006592 14 5980 58419 32 _ _ (2195081 / 100000) (548771 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3413006592 :
    ThetaLowerSegment 3413006592 3413137664 (170645305061681 / 50000)
      (170651828851329 / 50000) := by
  exact
    packedTile65536 3413006592 3413137664 14 5944 58420 32 _ _ (548771 / 25000) (2195087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3413137664 :
    ThetaLowerSegment 3413137664 3413268736 (170651828851329 / 50000) (6826339154817 / 2000) := by
  exact
    packedTile65536 3413137664 3413268736 14 6059 58422 32 _ _ (137193 / 6250) (2195091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3413268736 :
    ThetaLowerSegment 3413268736 3413399808 (6826339154817 / 2000) (170665041097959 / 50000) := by
  exact
    packedTile65536 3413268736 3413399808 14 5979 58423 32 _ _ (548773 / 25000) (439019 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3413399808 :
    ThetaLowerSegment 3413399808 3413530880 (170665041097959 / 50000)
      (170671581386491 / 50000) := by
  exact
    packedTile65536 3413399808 3413530880 14 5959 58424 32 _ _ (274387 / 12500) (2195099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3413530880 :
    ThetaLowerSegment 3413530880 3413661952 (170671581386491 / 50000)
      (170678083272691 / 50000) := by
  exact
    packedTile65536 3413530880 3413661952 14 5924 58425 32 _ _ (21951 / 1000) (2195103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3413661952 :
    ThetaLowerSegment 3413661952 3413793024 (170678083272691 / 50000)
      (170684686145523 / 50000) := by
  exact
    packedTile65536 3413661952 3413793024 14 6016 58426 32 _ _ (68597 / 3125) (2195107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3413793024 :
    ThetaLowerSegment 3413793024 3413924096 (170684686145523 / 50000)
      (170691236344811 / 50000) := by
  exact
    packedTile65536 3413793024 3413924096 14 5968 58427 32 _ _ (2195107 / 100000) (219511 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3413924096 :
    ThetaLowerSegment 3413924096 3414055168 (170691236344811 / 50000)
      (170697755824481 / 50000) := by
  exact
    packedTile65536 3413924096 3414055168 14 5940 58428 32 _ _ (2195111 / 100000) (1097557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3414055168 :
    ThetaLowerSegment 3414055168 3414186240 (170697755824481 / 50000)
      (170704349949941 / 50000) := by
  exact
    packedTile65536 3414055168 3414186240 14 6008 58429 32 _ _ (439023 / 20000) (1097559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3414186240 :
    ThetaLowerSegment 3414186240 3414317312 (170704349949941 / 50000)
      (341421697199481 / 100000) := by
  exact
    packedTile65536 3414186240 3414317312 14 5921 58431 32 _ _ (2195119 / 100000) (1097561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3414317312 :
    ThetaLowerSegment 3414317312 3414448384 (341421697199481 / 100000)
      (68287012221661 / 20000) := by
  exact
    packedTile65536 3414317312 3414448384 14 6088 58432 32 _ _ (2195123 / 100000) (1097563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3414448384 :
    ThetaLowerSegment 3414448384 3414579456 (68287012221661 / 20000) (170724013861747 / 50000) := by
  exact
    packedTile65536 3414448384 3414579456 14 5907 58433 32 _ _ (2195127 / 100000) (219513 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3414579456 :
    ThetaLowerSegment 3414579456 3414710528 (170724013861747 / 50000)
      (341461187533839 / 100000) := by
  exact
    packedTile65536 3414579456 3414710528 14 5995 58434 32 _ _ (2195131 / 100000) (1097567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3414710528 :
    ThetaLowerSegment 3414710528 3414841600 (341461187533839 / 100000)
      (341474255166541 / 100000) := by
  exact
    packedTile65536 3414710528 3414841600 14 5953 58435 32 _ _ (1097567 / 50000) (2195137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3414841600 :
    ThetaLowerSegment 3414841600 3414972672 (341474255166541 / 100000)
      (341487371116091 / 100000) := by
  exact
    packedTile65536 3414841600 3414972672 14 5975 58436 32 _ _ (1097569 / 50000) (2195141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3414972672 :
    ThetaLowerSegment 3414972672 3415103744 (341487371116091 / 100000)
      (68300089515397 / 20000) := by
  exact
    packedTile65536 3414972672 3415103744 14 5957 58437 32 _ _ (1097571 / 50000) (439029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3415103744 :
    ThetaLowerSegment 3415103744 3415234816 (68300089515397 / 20000)
      (341513636014153 / 100000) := by
  exact
    packedTile65536 3415103744 3415234816 14 6008 58438 32 _ _ (1097573 / 50000) (2195149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3415234816 :
    ThetaLowerSegment 3415234816 3415365888 (341513636014153 / 100000)
      (341526793743253 / 100000) := by
  exact
    packedTile65536 3415234816 3415365888 14 5994 58440 32 _ _ (43903 / 2000) (2195153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3415365888 :
    ThetaLowerSegment 3415365888 3415496960 (341526793743253 / 100000)
      (341539846128937 / 100000) := by
  exact
    packedTile65536 3415365888 3415496960 14 5946 58441 32 _ _ (1097577 / 50000) (2195157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3415496960 :
    ThetaLowerSegment 3415496960 3415628032 (341539846128937 / 100000) (17077650743789 / 5000) := by
  exact
    packedTile65536 3415496960 3415628032 14 5999 58442 32 _ _ (2195157 / 100000) (54879 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3415628032 :
    ThetaLowerSegment 3415628032 3415759104 (17077650743789 / 5000) (34156603218051 / 10000) := by
  exact
    packedTile65536 3415628032 3415759104 14 5930 58443 32 _ _ (2195161 / 100000) (548791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3415759104 :
    ThetaLowerSegment 3415759104 3415890176 (34156603218051 / 10000) (2134869498464 / 625) := by
  exact
    packedTile65536 3415759104 3415890176 14 5962 58444 32 _ _ (439033 / 20000) (68599 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3415890176 :
    ThetaLowerSegment 3415890176 3416021248 (2134869498464 / 625) (341592271011719 / 100000) := by
  exact
    packedTile65536 3415890176 3416021248 14 5991 58445 32 _ _ (2195169 / 100000) (548793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3416021248 :
    ThetaLowerSegment 3416021248 3416152320 (341592271011719 / 100000)
      (170802676023813 / 50000) := by
  exact
    packedTile65536 3416021248 3416152320 14 5959 58446 32 _ _ (2195173 / 100000) (274397 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3416152320 :
    ThetaLowerSegment 3416152320 3416283392 (170802676023813 / 50000) (85404623094287 / 25000) := by
  exact
    packedTile65536 3416152320 3416283392 14 5986 58447 32 _ _ (2195177 / 100000) (109759 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3416283392 :
    ThetaLowerSegment 3416283392 3416414464 (85404623094287 / 25000) (42703938449921 / 12500) := by
  exact
    packedTile65536 3416283392 3416414464 14 5929 58448 32 _ _ (109759 / 5000) (2195183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3416414464 :
    ThetaLowerSegment 3416414464 3416545536 (42703938449921 / 12500) (42705591972269 / 12500) := by
  exact
    packedTile65536 3416414464 3416545536 14 6026 58450 32 _ _ (137199 / 6250) (2195187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3416545536 :
    ThetaLowerSegment 3416545536 3416676608 (42705591972269 / 12500) (85414461909019 / 25000) := by
  exact
    packedTile65536 3416545536 3416676608 14 5973 58451 32 _ _ (548797 / 25000) (2195191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3416676608 :
    ThetaLowerSegment 3416676608 3416807680 (85414461909019 / 25000) (85417727257119 / 25000) := by
  exact
    packedTile65536 3416676608 3416807680 14 5950 58452 32 _ _ (274399 / 12500) (439039 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3416807680 :
    ThetaLowerSegment 3416807680 3416938752 (85417727257119 / 25000) (85420980537591 / 25000) := by
  exact
    packedTile65536 3416807680 3416938752 14 5928 58453 32 _ _ (548799 / 25000) (2195199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3416938752 :
    ThetaLowerSegment 3416938752 3417069824 (85420980537591 / 25000) (85424305716791 / 25000) := by
  exact
    packedTile65536 3416938752 3417069824 14 6059 58454 32 _ _ (2744 / 125) (2195203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417069824 :
    ThetaLowerSegment 3417069824 3417200896 (85424305716791 / 25000) (42713826700683 / 12500) := by
  exact
    packedTile65536 3417069824 3417200896 14 6100 58455 32 _ _ (2195203 / 100000) (1097603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417200896 :
    ThetaLowerSegment 3417200896 3417331968 (42713826700683 / 12500)
      (341723712405633 / 100000) := by
  exact
    packedTile65536 3417200896 3417331968 14 5967 58456 32 _ _ (2195207 / 100000) (219521 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417331968 :
    ThetaLowerSegment 3417331968 3417463040 (341723712405633 / 100000)
      (170868388053147 / 50000) := by
  exact
    packedTile65536 3417331968 3417463040 14 5951 58457 32 _ _ (2195211 / 100000) (1097607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417463040 :
    ThetaLowerSegment 3417463040 3417594112 (170868388053147 / 50000)
      (170874841985247 / 50000) := by
  exact
    packedTile65536 3417463040 3417594112 14 5880 58459 32 _ _ (439043 / 20000) (1097609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417594112 :
    ThetaLowerSegment 3417594112 3417725184 (170874841985247 / 50000)
      (341762572101243 / 100000) := by
  exact
    packedTile65536 3417594112 3417725184 14 5871 58460 32 _ _ (2195219 / 100000) (1097611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417725184 :
    ThetaLowerSegment 3417725184 3417856256 (341762572101243 / 100000)
      (341775804905487 / 100000) := by
  exact
    packedTile65536 3417725184 3417856256 14 6028 58461 32 _ _ (2195223 / 100000) (1097613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417856256 :
    ThetaLowerSegment 3417856256 3417987328 (341775804905487 / 100000)
      (341789094803691 / 100000) := by
  exact
    packedTile65536 3417856256 3417987328 14 6054 58462 32 _ _ (1097613 / 50000) (2195229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417987328 :
    ThetaLowerSegment 3417987328 3418118400 (341789094803691 / 100000)
      (341802279355071 / 100000) := by
  exact
    packedTile65536 3417987328 3418118400 14 6006 58463 32 _ _ (219523 / 10000) (2195233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3418118400 :
    ThetaLowerSegment 3418118400 3418249472 (341802279355071 / 100000)
      (341815351973541 / 100000) := by
  exact
    packedTile65536 3418118400 3418249472 14 5955 58464 32 _ _ (1097617 / 50000) (2195237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3418249472 :
    ThetaLowerSegment 3418249472 3418380544 (341815351973541 / 100000)
      (341828560720587 / 100000) := by
  exact
    packedTile65536 3418249472 3418380544 14 6017 58465 32 _ _ (1097619 / 50000) (2195241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3418380544 :
    ThetaLowerSegment 3418380544 3418511616 (341828560720587 / 100000)
      (341841628996213 / 100000) := by
  exact
    packedTile65536 3418380544 3418511616 14 5953 58466 32 _ _ (1097621 / 50000) (439049 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3418511616 :
    ThetaLowerSegment 3418511616 3418642688 (341841628996213 / 100000)
      (341854655585977 / 100000) := by
  exact
    packedTile65536 3418511616 3418642688 14 5934 58468 32 _ _ (1097623 / 50000) (2195249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3418642688 :
    ThetaLowerSegment 3418642688 3418773760 (341854655585977 / 100000)
      (170933839999147 / 50000) := by
  exact
    packedTile65536 3418642688 3418773760 14 5933 58469 32 _ _ (2195249 / 100000) (548813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3418773760 :
    ThetaLowerSegment 3418773760 3418904832 (170933839999147 / 50000) (85470167876387 / 25000) := by
  exact
    packedTile65536 3418773760 3418904832 14 5918 58470 32 _ _ (2195253 / 100000) (274407 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3418904832 :
    ThetaLowerSegment 3418904832 3419035904 (85470167876387 / 25000) (13675745906787 / 4000) := by
  exact
    packedTile65536 3418904832 3419035904 14 5911 58471 32 _ _ (2195257 / 100000) (109763 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3419035904 :
    ThetaLowerSegment 3419035904 3419166976 (13675745906787 / 4000) (170953395348641 / 50000) := by
  exact
    packedTile65536 3419035904 3419166976 14 5987 58472 32 _ _ (2195261 / 100000) (68602 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3419166976 :
    ThetaLowerSegment 3419166976 3419298048 (170953395348641 / 50000) (10684993196111 / 3125) := by
  exact
    packedTile65536 3419166976 3419298048 14 5918 58473 32 _ _ (439053 / 20000) (548817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3419298048 :
    ThetaLowerSegment 3419298048 3419429120 (10684993196111 / 3125) (85483271401423 / 25000) := by
  exact
    packedTile65536 3419298048 3419429120 14 6060 58474 32 _ _ (2195269 / 100000) (274409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3419429120 :
    ThetaLowerSegment 3419429120 3419560192 (85483271401423 / 25000) (17097311105667 / 5000) := by
  exact
    packedTile65536 3419429120 3419560192 14 5984 58475 32 _ _ (274409 / 12500) (87811 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3419560192 :
    ThetaLowerSegment 3419560192 3419691264 (17097311105667 / 5000) (42744916812111 / 12500) := by
  exact
    packedTile65536 3419560192 3419691264 14 5973 58477 32 _ _ (548819 / 25000) (2195279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3419691264 :
    ThetaLowerSegment 3419691264 3419822336 (42744916812111 / 12500) (42746559704781 / 12500) := by
  exact
    packedTile65536 3419691264 3419822336 14 5987 58478 32 _ _ (27441 / 1250) (2195283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3419822336 :
    ThetaLowerSegment 3419822336 3419953408 (42746559704781 / 12500) (85496377759839 / 25000) := by
  exact
    packedTile65536 3419822336 3419953408 14 5937 58479 32 _ _ (548821 / 25000) (2195287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3419953408 :
    ThetaLowerSegment 3419953408 3420084480 (85496377759839 / 25000) (85499661910687 / 25000) := by
  exact
    packedTile65536 3419953408 3420084480 14 5984 58480 32 _ _ (274411 / 12500) (2195291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3420084480 :
    ThetaLowerSegment 3420084480 3420215552 (85499661910687 / 25000) (85502946067519 / 25000) := by
  exact
    packedTile65536 3420084480 3420215552 14 5984 58481 32 _ _ (548823 / 25000) (439059 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3420215552 :
    ThetaLowerSegment 3420215552 3420346624 (85502946067519 / 25000) (171012488996513 / 50000) := by
  exact
    packedTile65536 3420215552 3420346624 14 6010 58482 32 _ _ (439059 / 20000) (1097649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3420346624 :
    ThetaLowerSegment 3420346624 3420477696 (171012488996513 / 50000) (34203800928789 / 10000) := by
  exact
    packedTile65536 3420346624 3420477696 14 5936 58483 32 _ _ (2195299 / 100000) (1097651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3420477696 :
    ThetaLowerSegment 3420477696 3420608768 (34203800928789 / 10000)
      (342051183301193 / 100000) := by
  exact
    packedTile65536 3420477696 3420608768 14 6001 58484 32 _ _ (2195303 / 100000) (1097653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3420608768 :
    ThetaLowerSegment 3420608768 3420739840 (342051183301193 / 100000) (13682576488847 / 4000) := by
  exact
    packedTile65536 3420608768 3420739840 14 6026 58485 32 _ _ (2195307 / 100000) (219531 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3420739840 :
    ThetaLowerSegment 3420739840 3420870912 (13682576488847 / 4000) (342077588477797 / 100000) := by
  exact
    packedTile65536 3420739840 3420870912 14 6002 58487 32 _ _ (2195311 / 100000) (1097657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3420870912 :
    ThetaLowerSegment 3420870912 3421001984 (342077588477797 / 100000)
      (85522684054833 / 25000) := by
  exact
    packedTile65536 3420870912 3421001984 14 5989 58488 32 _ _ (439063 / 20000) (1097659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3421001984 :
    ThetaLowerSegment 3421001984 3421133056 (85522684054833 / 25000) (34210408594809 / 10000) := by
  exact
    packedTile65536 3421001984 3421133056 14 6081 58489 32 _ _ (1097659 / 50000) (2195321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3421133056 :
    ThetaLowerSegment 3421133056 3421264128 (34210408594809 / 10000) (171058473072183 / 50000) := by
  exact
    packedTile65536 3421133056 3421264128 14 5858 58490 32 _ _ (1097661 / 50000) (87813 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3421264128 :
    ThetaLowerSegment 3421264128 3421395200 (171058473072183 / 50000)
      (171064984409099 / 50000) := by
  exact
    packedTile65536 3421264128 3421395200 14 5932 58491 32 _ _ (1097663 / 50000) (2195329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3421395200 :
    ThetaLowerSegment 3421395200 3421526272 (171064984409099 / 50000) (21383939302273 / 6250) := by
  exact
    packedTile65536 3421395200 3421526272 14 5949 58492 32 _ _ (219533 / 10000) (2195333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3421526272 :
    ThetaLowerSegment 3421526272 3421657344 (21383939302273 / 6250) (85539066675097 / 25000) := by
  exact
    packedTile65536 3421526272 3421657344 14 6030 58493 32 _ _ (1097667 / 50000) (2195337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3421657344 :
    ThetaLowerSegment 3421657344 3421788416 (85539066675097 / 25000) (171084672164427 / 50000) := by
  exact
    packedTile65536 3421657344 3421788416 14 5957 58494 32 _ _ (1097669 / 50000) (2195341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3421788416 :
    ThetaLowerSegment 3421788416 3421919488 (171084672164427 / 50000) (68436508104721 / 20000) := by
  exact
    packedTile65536 3421788416 3421919488 14 6011 58496 32 _ _ (2195341 / 100000) (137209 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3421919488 :
    ThetaLowerSegment 3421919488 3422050560 (68436508104721 / 20000) (34219577625861 / 10000) := by
  exact
    packedTile65536 3421919488 3422050560 14 6029 58497 32 _ _ (439069 / 20000) (548837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3422050560 :
    ThetaLowerSegment 3422050560 3422181632 (34219577625861 / 10000) (171104425878627 / 50000) := by
  exact
    packedTile65536 3422050560 3422181632 14 5956 58498 32 _ _ (2195349 / 100000) (274419 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3422181632 :
    ThetaLowerSegment 3422181632 3422312704 (171104425878627 / 50000)
      (342221990944959 / 100000) := by
  exact
    packedTile65536 3422181632 3422312704 14 5985 58499 32 _ _ (2195353 / 100000) (548839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3422312704 :
    ThetaLowerSegment 3422312704 3422443776 (342221990944959 / 100000)
      (68447053692819 / 20000) := by
  exact
    packedTile65536 3422312704 3422443776 14 6048 58500 32 _ _ (2195357 / 100000) (13721 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3422443776 :
    ThetaLowerSegment 3422443776 3422574848 (68447053692819 / 20000)
      (342248370378543 / 100000) := by
  exact
    packedTile65536 3422443776 3422574848 14 5968 58501 32 _ _ (2195361 / 100000) (548841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3422574848 :
    ThetaLowerSegment 3422574848 3422705920 (342248370378543 / 100000)
      (342261485483079 / 100000) := by
  exact
    packedTile65536 3422574848 3422705920 14 5974 58502 32 _ _ (548841 / 25000) (2195367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3422705920 :
    ThetaLowerSegment 3422705920 3422836992 (342261485483079 / 100000)
      (342274765264111 / 100000) := by
  exact
    packedTile65536 3422705920 3422836992 14 6049 58503 32 _ _ (274421 / 12500) (2195371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3422836992 :
    ThetaLowerSegment 3422836992 3422968064 (342274765264111 / 100000)
      (342287981403551 / 100000) := by
  exact
    packedTile65536 3422836992 3422968064 14 6020 58505 32 _ _ (548843 / 25000) (17563 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3422968064 :
    ThetaLowerSegment 3422968064 3423099136 (342287981403551 / 100000)
      (342301006569359 / 100000) := by
  exact
    packedTile65536 3422968064 3423099136 14 5933 58506 32 _ _ (137211 / 6250) (2195379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3423099136 :
    ThetaLowerSegment 3423099136 3423230208 (342301006569359 / 100000)
      (342314091034159 / 100000) := by
  exact
    packedTile65536 3423099136 3423230208 14 5960 58507 32 _ _ (109769 / 5000) (2195383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3423230208 :
    ThetaLowerSegment 3423230208 3423361280 (342314091034159 / 100000) (13693088250327 / 4000) := by
  exact
    packedTile65536 3423230208 3423361280 14 5974 58508 32 _ _ (274423 / 12500) (2195387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3423361280 :
    ThetaLowerSegment 3423361280 3423492352 (13693088250327 / 4000) (342340330281661 / 100000) := by
  exact
    packedTile65536 3423361280 3423492352 14 5978 58509 32 _ _ (2195387 / 100000) (219539 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3423492352 :
    ThetaLowerSegment 3423492352 3423623424 (342340330281661 / 100000)
      (68470689109499 / 20000) := by
  exact
    packedTile65536 3423492352 3423623424 14 5974 58510 32 _ _ (2195391 / 100000) (1097697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3423623424 :
    ThetaLowerSegment 3423623424 3423754496 (68470689109499 / 20000) (34236662889447 / 10000) := by
  exact
    packedTile65536 3423623424 3423754496 14 6005 58511 32 _ _ (439079 / 20000) (1097699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3423754496 :
    ThetaLowerSegment 3423754496 3423885568 (34236662889447 / 10000) (171189874299447 / 50000) := by
  exact
    packedTile65536 3423754496 3423885568 14 5976 58512 32 _ _ (2195399 / 100000) (1097701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3423885568 :
    ThetaLowerSegment 3423885568 3424016640 (171189874299447 / 50000) (68478556541301 / 20000) := by
  exact
    packedTile65536 3423885568 3424016640 14 5937 58513 32 _ _ (2195403 / 100000) (1097703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3424016640 :
    ThetaLowerSegment 3424016640 3424147712 (68478556541301 / 20000) (6848116248941 / 2000) := by
  exact
    packedTile65536 3424016640 3424147712 14 5935 58515 32 _ _ (2195407 / 100000) (219541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3424147712 :
    ThetaLowerSegment 3424147712 3424278784 (6848116248941 / 2000) (1369675676179 / 400) := by
  exact
    packedTile65536 3424147712 3424278784 14 5970 58516 32 _ _ (219541 / 10000) (2195413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3424278784 :
    ThetaLowerSegment 3424278784 3424409856 (1369675676179 / 400) (6848639635161 / 2000) := by
  exact
    packedTile65536 3424278784 3424409856 14 5950 58517 32 _ _ (1097707 / 50000) (2195417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3424409856 :
    ThetaLowerSegment 3424409856 3424540928 (6848639635161 / 2000) (34244506644933 / 10000) := by
  exact
    packedTile65536 3424409856 3424540928 14 5960 58518 32 _ _ (1097709 / 50000) (2195421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3424540928 :
    ThetaLowerSegment 3424540928 3424672000 (34244506644933 / 10000) (34245812921023 / 10000) := by
  exact
    packedTile65536 3424540928 3424672000 14 5950 58519 32 _ _ (1097711 / 50000) (87817 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3424672000 :
    ThetaLowerSegment 3424672000 3424803072 (34245812921023 / 10000) (34247125785771 / 10000) := by
  exact
    packedTile65536 3424672000 3424803072 14 5980 58520 32 _ _ (1097713 / 50000) (2195429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3424803072 :
    ThetaLowerSegment 3424803072 3424934144 (34247125785771 / 10000)
      (342484195520807 / 100000) := by
  exact
    packedTile65536 3424803072 3424934144 14 5893 58521 32 _ _ (2195429 / 100000) (274429 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3424934144 :
    ThetaLowerSegment 3424934144 3425065216 (342484195520807 / 100000)
      (342497275910621 / 100000) := by
  exact
    packedTile65536 3424934144 3425065216 14 5958 58522 32 _ _ (2195433 / 100000) (548859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425065216 :
    ThetaLowerSegment 3425065216 3425196288 (342497275910621 / 100000)
      (342510479268739 / 100000) := by
  exact
    packedTile65536 3425065216 3425196288 14 6014 58524 32 _ _ (2195437 / 100000) (27443 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425196288 :
    ThetaLowerSegment 3425196288 3425327360 (342510479268739 / 100000)
      (34252354433813 / 10000) := by
  exact
    packedTile65536 3425196288 3425327360 14 5951 58525 32 _ _ (2195441 / 100000) (548861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425327360 :
    ThetaLowerSegment 3425327360 3425458432 (34252354433813 / 10000) (68507367551521 / 20000) := by
  exact
    packedTile65536 3425327360 3425458432 14 6055 58526 32 _ _ (439089 / 20000) (274431 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425458432 :
    ThetaLowerSegment 3425458432 3425589504 (68507367551521 / 20000) (21409373869423 / 6250) := by
  exact
    packedTile65536 3425458432 3425589504 14 5987 58527 32 _ _ (2195449 / 100000) (548863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425589504 :
    ThetaLowerSegment 3425589504 3425720576 (21409373869423 / 6250) (4282038774149 / 1250) := by
  exact
    packedTile65536 3425589504 3425720576 14 5976 58528 32 _ _ (548863 / 25000) (439091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425720576 :
    ThetaLowerSegment 3425720576 3425851648 (4282038774149 / 1250) (21411023478681 / 6250) := by
  exact
    packedTile65536 3425720576 3425851648 14 6046 58529 32 _ _ (68608 / 3125) (2195459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425851648 :
    ThetaLowerSegment 3425851648 3425982720 (21411023478681 / 6250) (85647344842119 / 25000) := by
  exact
    packedTile65536 3425851648 3425982720 14 5923 58530 32 _ _ (109773 / 5000) (2195463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425982720 :
    ThetaLowerSegment 3425982720 3426113792 (85647344842119 / 25000) (85650633647191 / 25000) := by
  exact
    packedTile65536 3425982720 3426113792 14 5992 58531 32 _ _ (274433 / 12500) (2195467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3426113792 :
    ThetaLowerSegment 3426113792 3426244864 (85650633647191 / 25000) (21413458522667 / 6250) := by
  exact
    packedTile65536 3426113792 3426244864 14 5831 58533 32 _ _ (548867 / 25000) (2195471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3426244864 :
    ThetaLowerSegment 3426244864 3426375936 (21413458522667 / 6250) (21414279080327 / 6250) := by
  exact
    packedTile65536 3426244864 3426375936 14 5980 58534 32 _ _ (137217 / 6250) (87819 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3426375936 :
    ThetaLowerSegment 3426375936 3426507008 (21414279080327 / 6250) (342641666676407 / 100000) := by
  exact
    packedTile65536 3426375936 3426507008 14 6013 58535 32 _ _ (87819 / 4000) (1097739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3426507008 :
    ThetaLowerSegment 3426507008 3426638080 (342641666676407 / 100000)
      (68530960006357 / 20000) := by
  exact
    packedTile65536 3426507008 3426638080 14 5982 58536 32 _ _ (2195479 / 100000) (1097741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3426638080 :
    ThetaLowerSegment 3426638080 3426769152 (68530960006357 / 20000) (21416729234853 / 6250) := by
  exact
    packedTile65536 3426638080 3426769152 14 5861 58537 32 _ _ (2195483 / 100000) (1097743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3426769152 :
    ThetaLowerSegment 3426769152 3426900224 (21416729234853 / 6250) (342680772619551 / 100000) := by
  exact
    packedTile65536 3426769152 3426900224 14 5969 58538 32 _ _ (2195487 / 100000) (219549 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3426900224 :
    ThetaLowerSegment 3426900224 3427031296 (342680772619551 / 100000)
      (68538768914593 / 20000) := by
  exact
    packedTile65536 3426900224 3427031296 14 5954 58539 32 _ _ (2195491 / 100000) (1097747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3427031296 :
    ThetaLowerSegment 3427031296 3427162368 (68538768914593 / 20000) (68541413168771 / 20000) := by
  exact
    packedTile65536 3427031296 3427162368 14 6022 58540 32 _ _ (439099 / 20000) (1097749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3427162368 :
    ThetaLowerSegment 3427162368 3427293440 (68541413168771 / 20000)
      (342720071974007 / 100000) := by
  exact
    packedTile65536 3427162368 3427293440 14 5924 58541 32 _ _ (1097749 / 50000) (2195501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3427293440 :
    ThetaLowerSegment 3427293440 3427424512 (342720071974007 / 100000)
      (342733348174601 / 100000) := by
  exact
    packedTile65536 3427293440 3427424512 14 6047 58543 32 _ _ (1097751 / 50000) (439101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3427424512 :
    ThetaLowerSegment 3427424512 3427555584 (342733348174601 / 100000)
      (342746554143191 / 100000) := by
  exact
    packedTile65536 3427424512 3427555584 14 6015 58544 32 _ _ (1097753 / 50000) (2195509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3427555584 :
    ThetaLowerSegment 3427555584 3427686656 (342746554143191 / 100000)
      (342759709639111 / 100000) := by
  exact
    packedTile65536 3427555584 3427686656 14 5992 58545 32 _ _ (219551 / 10000) (2195513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3427686656 :
    ThetaLowerSegment 3427686656 3427817728 (342759709639111 / 100000)
      (342772801489093 / 100000) := by
  exact
    packedTile65536 3427686656 3427817728 14 5963 58546 32 _ _ (1097757 / 50000) (2195517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3427817728 :
    ThetaLowerSegment 3427817728 3427948800 (342772801489093 / 100000)
      (342786058020739 / 100000) := by
  exact
    packedTile65536 3427817728 3427948800 14 6038 58547 32 _ _ (2195517 / 100000) (13722 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3427948800 :
    ThetaLowerSegment 3427948800 3428079872 (342786058020739 / 100000)
      (342799174063193 / 100000) := by
  exact
    packedTile65536 3427948800 3428079872 14 5974 58548 32 _ _ (2195521 / 100000) (548881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3428079872 :
    ThetaLowerSegment 3428079872 3428210944 (342799174063193 / 100000)
      (342812140833843 / 100000) := by
  exact
    packedTile65536 3428079872 3428210944 14 5906 58549 32 _ _ (87821 / 4000) (274441 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3428210944 :
    ThetaLowerSegment 3428210944 3428342016 (342812140833843 / 100000)
      (171412686643563 / 50000) := by
  exact
    packedTile65536 3428210944 3428342016 14 6027 58550 32 _ _ (2195529 / 100000) (548883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3428342016 :
    ThetaLowerSegment 3428342016 3428473088 (171412686643563 / 50000)
      (342838632110913 / 100000) := by
  exact
    packedTile65536 3428342016 3428473088 14 6039 58552 32 _ _ (2195533 / 100000) (137221 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3428473088 :
    ThetaLowerSegment 3428473088 3428604160 (342838632110913 / 100000)
      (342851778986469 / 100000) := by
  exact
    packedTile65536 3428473088 3428604160 14 5988 58553 32 _ _ (2195537 / 100000) (109777 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3428604160 :
    ThetaLowerSegment 3428604160 3428735232 (342851778986469 / 100000)
      (342864838058389 / 100000) := by
  exact
    packedTile65536 3428604160 3428735232 14 5948 58554 32 _ _ (109777 / 5000) (2195543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3428735232 :
    ThetaLowerSegment 3428735232 3428866304 (342864838058389 / 100000)
      (342877840069957 / 100000) := by
  exact
    packedTile65536 3428735232 3428866304 14 5922 58555 32 _ _ (274443 / 12500) (2195547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3428866304 :
    ThetaLowerSegment 3428866304 3428997376 (342877840069957 / 100000)
      (342890822345281 / 100000) := by
  exact
    packedTile65536 3428866304 3428997376 14 5913 58556 32 _ _ (548887 / 25000) (2195551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3428997376 :
    ThetaLowerSegment 3428997376 3429128448 (342890822345281 / 100000)
      (342904050546081 / 100000) := by
  exact
    packedTile65536 3428997376 3429128448 14 6025 58557 32 _ _ (68611 / 3125) (439111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3429128448 :
    ThetaLowerSegment 3429128448 3429259520 (342904050546081 / 100000)
      (342917074584273 / 100000) := by
  exact
    packedTile65536 3429128448 3429259520 14 5932 58558 32 _ _ (548889 / 25000) (2195559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3429259520 :
    ThetaLowerSegment 3429259520 3429390592 (342917074584273 / 100000)
      (342930351135593 / 100000) := by
  exact
    packedTile65536 3429259520 3429390592 14 6047 58559 32 _ _ (54889 / 2500) (2195563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3429390592 :
    ThetaLowerSegment 3429390592 3429521664 (342930351135593 / 100000)
      (342943568424853 / 100000) := by
  exact
    packedTile65536 3429390592 3429521664 14 6020 58560 32 _ _ (2195563 / 100000) (1097783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3429521664 :
    ThetaLowerSegment 3429521664 3429652736 (342943568424853 / 100000)
      (85739216743543 / 25000) := by
  exact
    packedTile65536 3429521664 3429652736 14 6057 58562 32 _ _ (2195567 / 100000) (219557 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3429652736 :
    ThetaLowerSegment 3429652736 3429783808 (85739216743543 / 25000)
      (342969945990619 / 100000) := by
  exact
    packedTile65536 3429652736 3429783808 14 5957 58563 32 _ _ (2195571 / 100000) (1097787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3429783808 :
    ThetaLowerSegment 3429783808 3429914880 (342969945990619 / 100000)
      (42872866602093 / 12500) := by
  exact
    packedTile65536 3429783808 3429914880 14 5915 58564 32 _ _ (87823 / 4000) (1097789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3429914880 :
    ThetaLowerSegment 3429914880 3430045952 (42872866602093 / 12500) (171498116817163 / 50000) := by
  exact
    packedTile65536 3429914880 3430045952 14 6058 58565 32 _ _ (2195579 / 100000) (1097791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3430045952 :
    ThetaLowerSegment 3430045952 3430177024 (171498116817163 / 50000) (85752312810001 / 25000) := by
  exact
    packedTile65536 3430045952 3430177024 14 5929 58566 32 _ _ (1097791 / 50000) (439117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3430177024 :
    ThetaLowerSegment 3430177024 3430308096 (85752312810001 / 25000) (171511053198017 / 50000) := by
  exact
    packedTile65536 3430177024 3430308096 14 5855 58567 32 _ _ (1097793 / 50000) (2195589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3430308096 :
    ThetaLowerSegment 3430308096 3430439168 (171511053198017 / 50000) (85758832608651 / 25000) := by
  exact
    packedTile65536 3430308096 3430439168 14 6023 58568 32 _ _ (219559 / 10000) (2195593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3430439168 :
    ThetaLowerSegment 3430439168 3430570240 (85758832608651 / 25000) (171524171860121 / 50000) := by
  exact
    packedTile65536 3430439168 3430570240 14 5927 58569 32 _ _ (1097797 / 50000) (2195597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3430570240 :
    ThetaLowerSegment 3430570240 3430701312 (171524171860121 / 50000) (4288265700401 / 1250) := by
  exact
    packedTile65536 3430570240 3430701312 14 5881 58571 32 _ _ (1097799 / 50000) (2195601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3430701312 :
    ThetaLowerSegment 3430701312 3430832384 (4288265700401 / 1250) (85768542640761 / 25000) := by
  exact
    packedTile65536 3430701312 3430832384 14 5882 58572 32 _ _ (1097801 / 50000) (439121 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3430832384 :
    ThetaLowerSegment 3430832384 3430963456 (85768542640761 / 25000)
      (343087482516159 / 100000) := by
  exact
    packedTile65536 3430832384 3430963456 14 6063 58573 32 _ _ (439121 / 20000) (274451 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3430963456 :
    ThetaLowerSegment 3430963456 3431094528 (343087482516159 / 100000)
      (171550265510223 / 50000) := by
  exact
    packedTile65536 3430963456 3431094528 14 5943 58574 32 _ _ (2195609 / 100000) (548903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3431094528 :
    ThetaLowerSegment 3431094528 3431225600 (171550265510223 / 50000) (68622742257057 / 20000) := by
  exact
    packedTile65536 3431094528 3431225600 14 6003 58575 32 _ _ (2195613 / 100000) (68613 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3431225600 :
    ThetaLowerSegment 3431225600 3431356672 (68622742257057 / 20000) (171563461156387 / 50000) := by
  exact
    packedTile65536 3431225600 3431356672 14 6017 58576 32 _ _ (2195617 / 100000) (109781 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3431356672 :
    ThetaLowerSegment 3431356672 3431487744 (171563461156387 / 50000)
      (343139839151117 / 100000) := by
  exact
    packedTile65536 3431356672 3431487744 14 5883 58577 32 _ _ (2195621 / 100000) (274453 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3431487744 :
    ThetaLowerSegment 3431487744 3431618816 (343139839151117 / 100000)
      (343152953613269 / 100000) := by
  exact
    packedTile65536 3431487744 3431618816 14 5973 58578 32 _ _ (274453 / 12500) (2195627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3431618816 :
    ThetaLowerSegment 3431618816 3431749888 (343152953613269 / 100000)
      (343165942948517 / 100000) := by
  exact
    packedTile65536 3431618816 3431749888 14 5916 58580 32 _ _ (548907 / 25000) (2195631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3431749888 :
    ThetaLowerSegment 3431749888 3431880960 (343165942948517 / 100000)
      (343178941089957 / 100000) := by
  exact
    packedTile65536 3431749888 3431880960 14 5920 58581 32 _ _ (137227 / 6250) (439127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3431880960 :
    ThetaLowerSegment 3431880960 3432012032 (343178941089957 / 100000)
      (343192031471789 / 100000) := by
  exact
    packedTile65536 3431880960 3432012032 14 5962 58582 32 _ _ (548909 / 25000) (2195639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3432012032 :
    ThetaLowerSegment 3432012032 3432143104 (343192031471789 / 100000)
      (343205233855109 / 100000) := by
  exact
    packedTile65536 3432012032 3432143104 14 6013 58583 32 _ _ (54891 / 2500) (2195643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3432143104 :
    ThetaLowerSegment 3432143104 3432274176 (343205233855109 / 100000)
      (343218453827633 / 100000) := by
  exact
    packedTile65536 3432143104 3432274176 14 6021 58584 32 _ _ (548911 / 25000) (2195647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3432274176 :
    ThetaLowerSegment 3432274176 3432405248 (343218453827633 / 100000)
      (343231346666817 / 100000) := by
  exact
    packedTile65536 3432274176 3432405248 14 5872 58585 32 _ _ (2195647 / 100000) (43913 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3432405248 :
    ThetaLowerSegment 3432405248 3432536320 (343231346666817 / 100000)
      (343244546920629 / 100000) := by
  exact
    packedTile65536 3432405248 3432536320 14 6012 58586 32 _ _ (2195651 / 100000) (1097827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3432536320 :
    ThetaLowerSegment 3432536320 3432667392 (343244546920629 / 100000)
      (171628872501417 / 50000) := by
  exact
    packedTile65536 3432536320 3432667392 14 6011 58587 32 _ _ (439131 / 20000) (1097829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3432667392 :
    ThetaLowerSegment 3432667392 3432798464 (171628872501417 / 50000)
      (171635428739191 / 50000) := by
  exact
    packedTile65536 3432667392 3432798464 14 5972 58588 32 _ _ (2195659 / 100000) (1097831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3432798464 :
    ThetaLowerSegment 3432798464 3432929536 (171635428739191 / 50000)
      (343283888738287 / 100000) := by
  exact
    packedTile65536 3432798464 3432929536 14 5935 58590 32 _ _ (2195663 / 100000) (1097833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3432929536 :
    ThetaLowerSegment 3432929536 3433060608 (343283888738287 / 100000) (13731879698919 / 4000) := by
  exact
    packedTile65536 3432929536 3433060608 14 5968 58591 32 _ _ (1097833 / 50000) (2195669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433060608 :
    ThetaLowerSegment 3433060608 3433191680 (13731879698919 / 4000) (68661971380701 / 20000) := by
  exact
    packedTile65536 3433060608 3433191680 14 5859 58592 32 _ _ (219567 / 10000) (2195673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433191680 :
    ThetaLowerSegment 3433191680 3433322752 (68661971380701 / 20000)
      (343323004599417 / 100000) := by
  exact
    packedTile65536 3433191680 3433322752 14 5988 58593 32 _ _ (1097837 / 50000) (2195677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433322752 :
    ThetaLowerSegment 3433322752 3433339136 (343323004599417 / 100000)
      (343324684293087 / 100000) := by
  exact
    packedTile65536 3433322752 3433339136 11 765 58594 32 _ _ (1097839 / 50000) (2195681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433339136 :
    ThetaLowerSegment 3433339136 3433341184 (343324684293087 / 100000)
      (343324875317073 / 100000) := by
  exact
    packedTile65536 3433339136 3433341184 8 87 58594 32 _ _ (1097839 / 50000) (2195681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3401341184_3433341184 :
    ThetaLowerSegment 3401341184 3433341184 (340124585378599 / 100000)
      (343324875317073 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3401341184 cell3401472256)
                  (ThetaLowerSegment.join cell3401603328 cell3401734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3401865472 cell3401996544)
                  (ThetaLowerSegment.join cell3402127616 cell3402258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3402389760 cell3402520832)
                  (ThetaLowerSegment.join cell3402651904 cell3402782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3402914048 cell3403045120)
                  (ThetaLowerSegment.join cell3403176192 cell3403307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3403438336 cell3403569408)
                  (ThetaLowerSegment.join cell3403700480 cell3403831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3403962624 cell3404093696)
                  (ThetaLowerSegment.join cell3404224768 cell3404355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3404486912 cell3404617984)
                  (ThetaLowerSegment.join cell3404749056 cell3404880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3405011200 cell3405142272)
                  (ThetaLowerSegment.join cell3405273344 cell3405404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3405535488 cell3405666560)
                  (ThetaLowerSegment.join cell3405797632 cell3405928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3406059776 cell3406190848)
                  (ThetaLowerSegment.join cell3406321920 cell3406452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3406584064 cell3406715136)
                  (ThetaLowerSegment.join cell3406846208 cell3406977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3407108352 cell3407239424)
                  (ThetaLowerSegment.join cell3407370496 cell3407501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3407632640 cell3407763712)
                  (ThetaLowerSegment.join cell3407894784 cell3408025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3408156928 cell3408288000)
                  (ThetaLowerSegment.join cell3408419072 cell3408550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3408681216 cell3408812288)
                  (ThetaLowerSegment.join cell3408943360 cell3409074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3409205504 cell3409336576)
                  (ThetaLowerSegment.join cell3409467648 cell3409598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3409729792 cell3409860864)
                  (ThetaLowerSegment.join cell3409991936 cell3410123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3410254080 cell3410385152)
                  (ThetaLowerSegment.join cell3410516224 cell3410647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3410778368 cell3410909440)
                  (ThetaLowerSegment.join cell3411040512 cell3411171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3411302656 cell3411433728)
                  (ThetaLowerSegment.join cell3411564800 cell3411695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3411826944 cell3411958016)
                  (ThetaLowerSegment.join cell3412089088 cell3412220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3412351232 cell3412482304)
                  (ThetaLowerSegment.join cell3412613376 cell3412744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3412875520 cell3413006592)
                  (ThetaLowerSegment.join cell3413137664 cell3413268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3413399808 cell3413530880)
                  (ThetaLowerSegment.join cell3413661952 cell3413793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3413924096 cell3414055168)
                  (ThetaLowerSegment.join cell3414186240 cell3414317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3414448384 cell3414579456)
                  (ThetaLowerSegment.join cell3414710528 cell3414841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3414972672 cell3415103744)
                  (ThetaLowerSegment.join cell3415234816 cell3415365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3415496960 cell3415628032)
                  (ThetaLowerSegment.join cell3415759104 cell3415890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3416021248 cell3416152320)
                  (ThetaLowerSegment.join cell3416283392 cell3416414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3416545536 cell3416676608)
                  (ThetaLowerSegment.join cell3416807680 cell3416938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3417069824 cell3417200896)
                  (ThetaLowerSegment.join cell3417331968 cell3417463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3417594112 cell3417725184)
                  (ThetaLowerSegment.join cell3417856256 cell3417987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3418118400 cell3418249472)
                  (ThetaLowerSegment.join cell3418380544 cell3418511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3418642688 cell3418773760)
                  (ThetaLowerSegment.join cell3418904832 cell3419035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3419166976 cell3419298048)
                  (ThetaLowerSegment.join cell3419429120 cell3419560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3419691264 cell3419822336)
                  (ThetaLowerSegment.join cell3419953408 cell3420084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3420215552 cell3420346624)
                  (ThetaLowerSegment.join cell3420477696 cell3420608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3420739840 cell3420870912)
                  (ThetaLowerSegment.join cell3421001984 cell3421133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3421264128 cell3421395200)
                  (ThetaLowerSegment.join cell3421526272 cell3421657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3421788416 cell3421919488)
                  (ThetaLowerSegment.join cell3422050560 cell3422181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3422312704 cell3422443776)
                  (ThetaLowerSegment.join cell3422574848 cell3422705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3422836992 cell3422968064)
                  (ThetaLowerSegment.join cell3423099136 cell3423230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3423361280 cell3423492352)
                  (ThetaLowerSegment.join cell3423623424 cell3423754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3423885568 cell3424016640)
                  (ThetaLowerSegment.join cell3424147712 cell3424278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3424409856 cell3424540928)
                  (ThetaLowerSegment.join cell3424672000 cell3424803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3424934144 cell3425065216)
                  (ThetaLowerSegment.join cell3425196288 cell3425327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3425458432 cell3425589504)
                  (ThetaLowerSegment.join cell3425720576 cell3425851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3425982720 cell3426113792)
                  (ThetaLowerSegment.join cell3426244864 cell3426375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3426507008 cell3426638080)
                  (ThetaLowerSegment.join cell3426769152 cell3426900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3427031296 cell3427162368)
                  (ThetaLowerSegment.join cell3427293440 cell3427424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3427555584 cell3427686656)
                  (ThetaLowerSegment.join cell3427817728 cell3427948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3428079872 cell3428210944)
                  (ThetaLowerSegment.join cell3428342016 cell3428473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3428604160 cell3428735232)
                  (ThetaLowerSegment.join cell3428866304 cell3428997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3429128448 cell3429259520)
                  (ThetaLowerSegment.join cell3429390592 cell3429521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3429652736 cell3429783808)
                  (ThetaLowerSegment.join cell3429914880 cell3430045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3430177024 cell3430308096)
                  (ThetaLowerSegment.join cell3430439168 cell3430570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3430701312 cell3430832384)
                  (ThetaLowerSegment.join cell3430963456 cell3431094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3431225600 cell3431356672)
                  (ThetaLowerSegment.join cell3431487744 cell3431618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3431749888 cell3431880960)
                  (ThetaLowerSegment.join cell3432012032 cell3432143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3432274176 cell3432405248)
                  (ThetaLowerSegment.join cell3432536320 cell3432667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3432798464 cell3432929536)
                (ThetaLowerSegment.join cell3433060608 cell3433191680))
              (ThetaLowerSegment.join cell3433322752 cell3433339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
