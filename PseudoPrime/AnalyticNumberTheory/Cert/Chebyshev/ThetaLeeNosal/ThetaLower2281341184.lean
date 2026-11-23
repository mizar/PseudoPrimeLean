/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2281341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2249341184 :
    ThetaLowerSegment 2249341184 2249472256 (8997098227291 / 4000) (22494040831711 / 10000) := by
  exact
    packedTile65536 2249341184 2249472256 14 6015 47427 31 _ _ (2153389 / 100000) (134587 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249472256 :
    ThetaLowerSegment 2249472256 2249603328 (22494040831711 / 10000) (8998144086731 / 4000) := by
  exact
    packedTile65536 2249472256 2249603328 14 6127 47428 31 _ _ (430679 / 20000) (1076699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249603328 :
    ThetaLowerSegment 2249603328 2249734400 (8998144086731 / 4000) (8998666329299 / 4000) := by
  exact
    packedTile65536 2249603328 2249734400 14 6063 47429 31 _ _ (10767 / 500) (2153403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249734400 :
    ThetaLowerSegment 2249734400 2249865472 (8998666329299 / 4000) (8999189606957 / 4000) := by
  exact
    packedTile65536 2249734400 2249865472 14 6075 47431 31 _ _ (1076703 / 50000) (2153409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249865472 :
    ThetaLowerSegment 2249865472 2249996544 (8999189606957 / 4000) (224992841532533 / 100000) := by
  exact
    packedTile65536 2249865472 2249996544 14 6084 47432 31 _ _ (538353 / 25000) (430683 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249996544 :
    ThetaLowerSegment 2249996544 2250127616 (224992841532533 / 100000)
      (225006160422863 / 100000) := by
  exact
    packedTile65536 2249996544 2250127616 14 6185 47434 31 _ _ (1076709 / 50000) (2153421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2250127616 :
    ThetaLowerSegment 2250127616 2250258688 (225006160422863 / 100000)
      (225019201558607 / 100000) := by
  exact
    packedTile65536 2250127616 2250258688 14 6056 47435 31 _ _ (134589 / 6250) (2153427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2250258688 :
    ThetaLowerSegment 2250258688 2250389760 (225019201558607 / 100000)
      (225032275032137 / 100000) := by
  exact
    packedTile65536 2250258688 2250389760 14 6071 47436 31 _ _ (215343 / 10000) (2153433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2250389760 :
    ThetaLowerSegment 2250389760 2250520832 (225032275032137 / 100000)
      (225045458361207 / 100000) := by
  exact
    packedTile65536 2250389760 2250520832 14 6122 47438 31 _ _ (430687 / 20000) (1076719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2250520832 :
    ThetaLowerSegment 2250520832 2250651904 (225045458361207 / 100000)
      (112529352088399 / 50000) := by
  exact
    packedTile65536 2250520832 2250651904 14 6151 47439 31 _ _ (2153441 / 100000) (538361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2250651904 :
    ThetaLowerSegment 2250651904 2250782976 (112529352088399 / 50000) (45014394312753 / 20000) := by
  exact
    packedTile65536 2250651904 2250782976 14 6161 47441 31 _ _ (2153447 / 100000) (43069 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2250782976 :
    ThetaLowerSegment 2250782976 2250914048 (45014394312753 / 20000) (45017021525413 / 20000) := by
  exact
    packedTile65536 2250782976 2250914048 14 6100 47442 31 _ _ (2153453 / 100000) (134591 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2250914048 :
    ThetaLowerSegment 2250914048 2251045120 (45017021525413 / 20000) (112549017420721 / 50000) := by
  exact
    packedTile65536 2250914048 2251045120 14 6003 47443 31 _ _ (2153459 / 100000) (1076731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2251045120 :
    ThetaLowerSegment 2251045120 2251176192 (112549017420721 / 50000)
      (225111332487817 / 100000) := by
  exact
    packedTile65536 2251045120 2251176192 14 6175 47445 31 _ _ (430693 / 20000) (538367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2251176192 :
    ThetaLowerSegment 2251176192 2251307264 (225111332487817 / 100000)
      (225124539719327 / 100000) := by
  exact
    packedTile65536 2251176192 2251307264 14 6133 47446 31 _ _ (215347 / 10000) (2153473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2251307264 :
    ThetaLowerSegment 2251307264 2251438336 (225124539719327 / 100000)
      (225137688843783 / 100000) := by
  exact
    packedTile65536 2251307264 2251438336 14 6106 47447 31 _ _ (538369 / 25000) (2153479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2251438336 :
    ThetaLowerSegment 2251438336 2251569408 (225137688843783 / 100000)
      (225150909069781 / 100000) := by
  exact
    packedTile65536 2251438336 2251569408 14 6139 47449 31 _ _ (1076741 / 50000) (430697 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2251569408 :
    ThetaLowerSegment 2251569408 2251700480 (225150909069781 / 100000)
      (225163920444277 / 100000) := by
  exact
    packedTile65536 2251569408 2251700480 14 6042 47450 31 _ _ (134593 / 6250) (2153491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2251700480 :
    ThetaLowerSegment 2251700480 2251831552 (225163920444277 / 100000)
      (225177080446111 / 100000) := by
  exact
    packedTile65536 2251700480 2251831552 14 6111 47452 31 _ _ (1076747 / 50000) (2153497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2251831552 :
    ThetaLowerSegment 2251831552 2251962624 (225177080446111 / 100000)
      (225190031589097 / 100000) := by
  exact
    packedTile65536 2251831552 2251962624 14 6014 47453 31 _ _ (2153499 / 100000) (1076751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2251962624 :
    ThetaLowerSegment 2251962624 2252093696 (225190031589097 / 100000)
      (225203133513517 / 100000) := by
  exact
    packedTile65536 2251962624 2252093696 14 6084 47454 31 _ _ (430701 / 20000) (538377 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2252093696 :
    ThetaLowerSegment 2252093696 2252224768 (225203133513517 / 100000)
      (225216368992123 / 100000) := by
  exact
    packedTile65536 2252093696 2252224768 14 6146 47456 31 _ _ (2153511 / 100000) (1076757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2252224768 :
    ThetaLowerSegment 2252224768 2252355840 (225216368992123 / 100000)
      (112614691347677 / 50000) := by
  exact
    packedTile65536 2252224768 2252355840 14 6043 47457 31 _ _ (2153517 / 100000) (26919 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2252355840 :
    ThetaLowerSegment 2252355840 2252486912 (112614691347677 / 50000) (2252425234927 / 1000) := by
  exact
    packedTile65536 2252355840 2252486912 14 6102 47458 31 _ _ (2153523 / 100000) (1076763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2252486912 :
    ThetaLowerSegment 2252486912 2252617984 (2252425234927 / 1000) (7039236145319 / 3125) := by
  exact
    packedTile65536 2252486912 2252617984 14 6052 47460 31 _ _ (2153529 / 100000) (538383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2252617984 :
    ThetaLowerSegment 2252617984 2252749056 (7039236145319 / 3125) (56317165764533 / 25000) := by
  exact
    packedTile65536 2252617984 2252749056 14 6086 47461 31 _ _ (1076767 / 50000) (2153537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2252749056 :
    ThetaLowerSegment 2252749056 2252880128 (56317165764533 / 25000) (28160229532789 / 12500) := by
  exact
    packedTile65536 2252749056 2252880128 14 6117 47463 31 _ _ (107677 / 5000) (2153543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2252880128 :
    ThetaLowerSegment 2252880128 2253011200 (28160229532789 / 12500) (112647401381389 / 50000) := by
  exact
    packedTile65536 2252880128 2253011200 14 6021 47464 31 _ _ (1076773 / 50000) (2153549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253011200 :
    ThetaLowerSegment 2253011200 2253142272 (112647401381389 / 50000)
      (112653983713077 / 50000) := by
  exact
    packedTile65536 2253011200 2253142272 14 6113 47465 31 _ _ (134597 / 6250) (430711 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253142272 :
    ThetaLowerSegment 2253142272 2253273344 (112653983713077 / 50000) (56330256112077 / 25000) := by
  exact
    packedTile65536 2253142272 2253273344 14 6063 47467 31 _ _ (1076779 / 50000) (2153561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253273344 :
    ThetaLowerSegment 2253273344 2253404416 (56330256112077 / 25000) (45066823191557 / 20000) := by
  exact
    packedTile65536 2253273344 2253404416 14 6079 47468 31 _ _ (2153563 / 100000) (1076783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253404416 :
    ThetaLowerSegment 2253404416 2253535488 (45066823191557 / 20000)
      (225347213964443 / 100000) := by
  exact
    packedTile65536 2253404416 2253535488 14 6082 47470 31 _ _ (2153569 / 100000) (538393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253535488 :
    ThetaLowerSegment 2253535488 2253666560 (225347213964443 / 100000)
      (112680120469809 / 50000) := by
  exact
    packedTile65536 2253535488 2253666560 14 6049 47471 31 _ _ (86143 / 4000) (1076789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253666560 :
    ThetaLowerSegment 2253666560 2253797632 (112680120469809 / 50000)
      (112686719041993 / 50000) := by
  exact
    packedTile65536 2253666560 2253797632 14 6128 47472 31 _ _ (2153581 / 100000) (134599 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253797632 :
    ThetaLowerSegment 2253797632 2253928704 (112686719041993 / 50000)
      (112693184110167 / 50000) := by
  exact
    packedTile65536 2253797632 2253928704 14 6004 47474 31 _ _ (2153587 / 100000) (215359 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253928704 :
    ThetaLowerSegment 2253928704 2254059776 (112693184110167 / 50000) (22539948790889 / 10000) := by
  exact
    packedTile65536 2253928704 2254059776 14 6092 47475 31 _ _ (2153593 / 100000) (538399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2254059776 :
    ThetaLowerSegment 2254059776 2254190848 (22539948790889 / 10000) (56353123371803 / 25000) := by
  exact
    packedTile65536 2254059776 2254190848 14 6039 47476 31 _ _ (1076799 / 50000) (2153601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2254190848 :
    ThetaLowerSegment 2254190848 2254321920 (56353123371803 / 25000) (56356443152369 / 25000) := by
  exact
    packedTile65536 2254190848 2254321920 14 6166 47478 31 _ _ (538401 / 25000) (2153607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2254321920 :
    ThetaLowerSegment 2254321920 2254452992 (56356443152369 / 25000) (112719481735363 / 50000) := by
  exact
    packedTile65536 2254321920 2254452992 14 6125 47479 31 _ _ (215361 / 10000) (2153613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2254452992 :
    ThetaLowerSegment 2254452992 2254584064 (112719481735363 / 50000)
      (112726039496083 / 50000) := by
  exact
    packedTile65536 2254452992 2254584064 14 6090 47481 31 _ _ (134601 / 6250) (2153619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2254584064 :
    ThetaLowerSegment 2254584064 2254715136 (112726039496083 / 50000) (2254649942633 / 1000) := by
  exact
    packedTile65536 2254584064 2254715136 14 5997 47482 31 _ _ (1076811 / 50000) (17229 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2254715136 :
    ThetaLowerSegment 2254715136 2254846208 (2254649942633 / 1000) (28184759962619 / 12500) := by
  exact
    packedTile65536 2254715136 2254846208 14 6076 47483 31 _ _ (2153627 / 100000) (215363 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2254846208 :
    ThetaLowerSegment 2254846208 2254977280 (28184759962619 / 12500) (56372817137361 / 25000) := by
  exact
    packedTile65536 2254846208 2254977280 14 6124 47485 31 _ _ (2153633 / 100000) (538409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2254977280 :
    ThetaLowerSegment 2254977280 2255108352 (56372817137361 / 25000)
      (225504429437373 / 100000) := by
  exact
    packedTile65536 2254977280 2255108352 14 6111 47486 31 _ _ (2153639 / 100000) (1076821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2255108352 :
    ThetaLowerSegment 2255108352 2255239424 (225504429437373 / 100000)
      (56379404051427 / 25000) := by
  exact
    packedTile65536 2255108352 2255239424 14 6123 47487 31 _ _ (430729 / 20000) (134603 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2255239424 :
    ThetaLowerSegment 2255239424 2255370496 (56379404051427 / 25000)
      (225530759937761 / 100000) := by
  exact
    packedTile65536 2255239424 2255370496 14 6103 47489 31 _ _ (2153651 / 100000) (1076827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2255370496 :
    ThetaLowerSegment 2255370496 2255501568 (225530759937761 / 100000)
      (112771842016709 / 50000) := by
  exact
    packedTile65536 2255370496 2255501568 14 6001 47490 31 _ _ (2153657 / 100000) (107683 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2255501568 :
    ThetaLowerSegment 2255501568 2255632640 (112771842016709 / 50000) (22555681275697 / 10000) := by
  exact
    packedTile65536 2255501568 2255632640 14 6096 47492 31 _ _ (1076831 / 50000) (430733 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2255632640 :
    ThetaLowerSegment 2255632640 2255763712 (22555681275697 / 10000) (112784923377853 / 50000) := by
  exact
    packedTile65536 2255632640 2255763712 14 6052 47493 31 _ _ (538417 / 25000) (2153671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2255763712 :
    ThetaLowerSegment 2255763712 2255894784 (112784923377853 / 50000) (7049469533966 / 3125) := by
  exact
    packedTile65536 2255763712 2255894784 14 6119 47494 31 _ _ (1076837 / 50000) (2153677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2255894784 :
    ThetaLowerSegment 2255894784 2256025856 (7049469533966 / 3125) (7049875771856 / 3125) := by
  exact
    packedTile65536 2255894784 2256025856 14 6036 47496 31 _ _ (26921 / 1250) (2153683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2256025856 :
    ThetaLowerSegment 2256025856 2256156928 (7049875771856 / 3125) (28201123736139 / 12500) := by
  exact
    packedTile65536 2256025856 2256156928 14 6020 47497 31 _ _ (1076843 / 50000) (2153689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2256156928 :
    ThetaLowerSegment 2256156928 2256288000 (28201123736139 / 12500) (56405553387963 / 25000) := by
  exact
    packedTile65536 2256156928 2256288000 14 6140 47499 31 _ _ (2153691 / 100000) (1076847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2256288000 :
    ThetaLowerSegment 2256288000 2256419072 (56405553387963 / 25000)
      (225635318798097 / 100000) := by
  exact
    packedTile65536 2256288000 2256419072 14 6085 47500 31 _ _ (2153697 / 100000) (21537 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2256419072 :
    ThetaLowerSegment 2256419072 2256550144 (225635318798097 / 100000)
      (56412110327619 / 25000) := by
  exact
    packedTile65536 2256419072 2256550144 14 6093 47501 31 _ _ (2153703 / 100000) (1076853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2256550144 :
    ThetaLowerSegment 2256550144 2256681216 (56412110327619 / 25000) (22566172108017 / 10000) := by
  exact
    packedTile65536 2256550144 2256681216 14 6166 47503 31 _ _ (2153709 / 100000) (134607 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2256681216 :
    ThetaLowerSegment 2256681216 2256812288 (22566172108017 / 10000) (5641869207141 / 2500) := by
  exact
    packedTile65536 2256681216 2256812288 14 6058 47504 31 _ _ (430743 / 20000) (1076859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2256812288 :
    ThetaLowerSegment 2256812288 2256943360 (5641869207141 / 2500) (5642198726301 / 2500) := by
  exact
    packedTile65536 2256812288 2256943360 14 6120 47505 31 _ _ (53843 / 2500) (2153723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2256943360 :
    ThetaLowerSegment 2256943360 2257074432 (5642198726301 / 2500) (56425208160243 / 25000) := by
  exact
    packedTile65536 2256943360 2257074432 14 5982 47507 31 _ _ (1076863 / 50000) (2153729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2257074432 :
    ThetaLowerSegment 2257074432 2257205504 (56425208160243 / 25000) (56428454911233 / 25000) := by
  exact
    packedTile65536 2257074432 2257205504 14 6030 47508 31 _ _ (538433 / 25000) (430747 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2257205504 :
    ThetaLowerSegment 2257205504 2257336576 (56428454911233 / 25000) (14107929725293 / 6250) := by
  exact
    packedTile65536 2257205504 2257336576 14 6062 47510 31 _ _ (1076869 / 50000) (2153741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2257336576 :
    ThetaLowerSegment 2257336576 2257467648 (14107929725293 / 6250) (7054376429664 / 3125) := by
  exact
    packedTile65536 2257336576 2257467648 14 6115 47511 31 _ _ (134609 / 6250) (2153747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2257467648 :
    ThetaLowerSegment 2257467648 2257598720 (7054376429664 / 3125) (112876606885317 / 50000) := by
  exact
    packedTile65536 2257467648 2257598720 14 6114 47512 31 _ _ (2153749 / 100000) (269219 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2257598720 :
    ThetaLowerSegment 2257598720 2257729792 (112876606885317 / 50000)
      (225766263372179 / 100000) := by
  exact
    packedTile65536 2257598720 2257729792 14 6059 47514 31 _ _ (430751 / 20000) (1076879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2257729792 :
    ThetaLowerSegment 2257729792 2257860864 (225766263372179 / 100000)
      (225779254858531 / 100000) := by
  exact
    packedTile65536 2257729792 2257860864 14 6032 47515 31 _ _ (2153761 / 100000) (538441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2257860864 :
    ThetaLowerSegment 2257860864 2257991936 (225779254858531 / 100000)
      (112896188880431 / 50000) := by
  exact
    packedTile65536 2257860864 2257991936 14 6093 47516 31 _ _ (2153767 / 100000) (215377 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2257991936 :
    ThetaLowerSegment 2257991936 2258123008 (112896188880431 / 50000)
      (225805306860181 / 100000) := by
  exact
    packedTile65536 2257991936 2258123008 14 6003 47518 31 _ _ (2153773 / 100000) (134611 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2258123008 :
    ThetaLowerSegment 2258123008 2258254080 (225805306860181 / 100000)
      (225818367369973 / 100000) := by
  exact
    packedTile65536 2258123008 2258254080 14 6064 47519 31 _ _ (1076889 / 50000) (2153781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2258254080 :
    ThetaLowerSegment 2258254080 2258385152 (225818367369973 / 100000)
      (225831460222909 / 100000) := by
  exact
    packedTile65536 2258254080 2258385152 14 6079 47521 31 _ _ (269223 / 12500) (2153787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2258385152 :
    ThetaLowerSegment 2258385152 2258516224 (225831460222909 / 100000)
      (225844563881269 / 100000) := by
  exact
    packedTile65536 2258385152 2258516224 14 6084 47522 31 _ _ (215379 / 10000) (2153793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2258516224 :
    ThetaLowerSegment 2258516224 2258647296 (225844563881269 / 100000)
      (225857590039477 / 100000) := by
  exact
    packedTile65536 2258516224 2258647296 14 6048 47523 31 _ _ (538449 / 25000) (2153799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2258647296 :
    ThetaLowerSegment 2258647296 2258778368 (225857590039477 / 100000)
      (225870794999539 / 100000) := by
  exact
    packedTile65536 2258647296 2258778368 14 6131 47525 31 _ _ (1076901 / 50000) (430761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2258778368 :
    ThetaLowerSegment 2258778368 2258909440 (225870794999539 / 100000)
      (225883976298379 / 100000) := by
  exact
    packedTile65536 2258778368 2258909440 14 6120 47526 31 _ _ (2153807 / 100000) (215381 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2258909440 :
    ThetaLowerSegment 2258909440 2259040512 (225883976298379 / 100000)
      (45179449618817 / 20000) := by
  exact
    packedTile65536 2258909440 2259040512 14 6162 47527 31 _ _ (2153813 / 100000) (269227 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2259040512 :
    ThetaLowerSegment 2259040512 2259171584 (45179449618817 / 20000)
      (225910369159433 / 100000) := by
  exact
    packedTile65536 2259040512 2259171584 14 6092 47529 31 _ _ (2153819 / 100000) (1076911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2259171584 :
    ThetaLowerSegment 2259171584 2259302656 (225910369159433 / 100000)
      (225923559183733 / 100000) := by
  exact
    packedTile65536 2259171584 2259302656 14 6124 47530 31 _ _ (86153 / 4000) (538457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2259302656 :
    ThetaLowerSegment 2259302656 2259433728 (225923559183733 / 100000) (2824205946353 / 1250) := by
  exact
    packedTile65536 2259302656 2259433728 14 5997 47532 31 _ _ (2153831 / 100000) (1076917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2259433728 :
    ThetaLowerSegment 2259433728 2259564800 (2824205946353 / 1250) (7060920864157 / 3125) := by
  exact
    packedTile65536 2259433728 2259564800 14 6032 47533 31 _ _ (2153837 / 100000) (26923 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2259564800 :
    ThetaLowerSegment 2259564800 2259695872 (7060920864157 / 3125) (11298134396761 / 5000) := by
  exact
    packedTile65536 2259564800 2259695872 14 6138 47534 31 _ _ (1076921 / 50000) (430769 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2259695872 :
    ThetaLowerSegment 2259695872 2259826944 (11298134396761 / 5000) (11298794012711 / 5000) := by
  exact
    packedTile65536 2259695872 2259826944 14 6125 47536 31 _ _ (269231 / 12500) (2153851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2259826944 :
    ThetaLowerSegment 2259826944 2259958016 (11298794012711 / 5000) (112994527689569 / 50000) := by
  exact
    packedTile65536 2259826944 2259958016 14 6117 47537 31 _ _ (1076927 / 50000) (2153857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2259958016 :
    ThetaLowerSegment 2259958016 2260089088 (112994527689569 / 50000)
      (113001064654669 / 50000) := by
  exact
    packedTile65536 2259958016 2260089088 14 6070 47539 31 _ _ (107693 / 5000) (2153863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2260089088 :
    ThetaLowerSegment 2260089088 2260220160 (113001064654669 / 50000) (28251916832723 / 12500) := by
  exact
    packedTile65536 2260089088 2260220160 14 6131 47540 31 _ _ (1076933 / 50000) (2153869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2260220160 :
    ThetaLowerSegment 2260220160 2260351232 (28251916832723 / 12500)
      (226028384966173 / 100000) := by
  exact
    packedTile65536 2260220160 2260351232 14 6059 47541 31 _ _ (2153871 / 100000) (1076937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2260351232 :
    ThetaLowerSegment 2260351232 2260482304 (226028384966173 / 100000)
      (226041484846087 / 100000) := by
  exact
    packedTile65536 2260351232 2260482304 14 6082 47543 31 _ _ (2153877 / 100000) (53847 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2260482304 :
    ThetaLowerSegment 2260482304 2260613376 (226041484846087 / 100000)
      (226054545992599 / 100000) := by
  exact
    packedTile65536 2260482304 2260613376 14 6064 47544 31 _ _ (2153883 / 100000) (1076943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2260613376 :
    ThetaLowerSegment 2260613376 2260744448 (226054545992599 / 100000)
      (45213547281767 / 20000) := by
  exact
    packedTile65536 2260613376 2260744448 14 6124 47545 31 _ _ (2153889 / 100000) (538473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2260744448 :
    ThetaLowerSegment 2260744448 2260875520 (45213547281767 / 20000)
      (226080873008341 / 100000) := by
  exact
    packedTile65536 2260744448 2260875520 14 6099 47547 31 _ _ (1076947 / 50000) (2153897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2260875520 :
    ThetaLowerSegment 2260875520 2261006592 (226080873008341 / 100000)
      (226093990259341 / 100000) := by
  exact
    packedTile65536 2260875520 2261006592 14 6090 47548 31 _ _ (21539 / 1000) (2153903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2261006592 :
    ThetaLowerSegment 2261006592 2261137664 (226093990259341 / 100000)
      (45221434002031 / 20000) := by
  exact
    packedTile65536 2261006592 2261137664 14 6119 47550 31 _ _ (1076953 / 50000) (2153909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2261137664 :
    ThetaLowerSegment 2261137664 2261268736 (45221434002031 / 20000)
      (226120252871643 / 100000) := by
  exact
    packedTile65536 2261137664 2261268736 14 6074 47551 31 _ _ (269239 / 12500) (430783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2261268736 :
    ThetaLowerSegment 2261268736 2261399808 (226120252871643 / 100000)
      (226133542545703 / 100000) := by
  exact
    packedTile65536 2261268736 2261399808 14 6170 47552 31 _ _ (1076959 / 50000) (2153921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2261399808 :
    ThetaLowerSegment 2261399808 2261530880 (226133542545703 / 100000)
      (28268337069183 / 12500) := by
  exact
    packedTile65536 2261399808 2261530880 14 6107 47554 31 _ _ (2153923 / 100000) (1076963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2261530880 :
    ThetaLowerSegment 2261530880 2261661952 (28268337069183 / 12500)
      (226159824750719 / 100000) := by
  exact
    packedTile65536 2261530880 2261661952 14 6095 47555 31 _ _ (2153929 / 100000) (538483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2261661952 :
    ThetaLowerSegment 2261661952 2261793024 (226159824750719 / 100000)
      (226173019756529 / 100000) := by
  exact
    packedTile65536 2261661952 2261793024 14 6126 47556 31 _ _ (430787 / 20000) (1076969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2261793024 :
    ThetaLowerSegment 2261793024 2261924096 (226173019756529 / 100000) (7068313087202 / 3125) := by
  exact
    packedTile65536 2261793024 2261924096 14 6035 47558 31 _ _ (2153941 / 100000) (269243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2261924096 :
    ThetaLowerSegment 2261924096 2262055168 (7068313087202 / 3125) (2827490227221 / 1250) := by
  exact
    packedTile65536 2261924096 2262055168 14 6128 47559 31 _ _ (2153947 / 100000) (43079 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2262055168 :
    ThetaLowerSegment 2262055168 2262186240 (2827490227221 / 1250) (14138278926783 / 6250) := by
  exact
    packedTile65536 2262055168 2262186240 14 6149 47561 31 _ _ (67311 / 3125) (430791 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2262186240 :
    ThetaLowerSegment 2262186240 2262317312 (14138278926783 / 6250) (113112750368151 / 50000) := by
  exact
    packedTile65536 2262186240 2262317312 14 6053 47562 31 _ _ (1076979 / 50000) (2153961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2262317312 :
    ThetaLowerSegment 2262317312 2262448384 (113112750368151 / 50000) (22623873038319 / 10000) := by
  exact
    packedTile65536 2262317312 2262448384 14 6142 47563 31 _ _ (538491 / 25000) (2153967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2262448384 :
    ThetaLowerSegment 2262448384 2262579456 (22623873038319 / 10000) (452503838283 / 200) := by
  exact
    packedTile65536 2262448384 2262579456 14 6123 47565 31 _ _ (215397 / 10000) (2153973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2262579456 :
    ThetaLowerSegment 2262579456 2262710528 (452503838283 / 200) (56566294754439 / 25000) := by
  exact
    packedTile65536 2262579456 2262710528 14 6156 47566 31 _ _ (269247 / 12500) (2153979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2262710528 :
    ThetaLowerSegment 2262710528 2262841600 (56566294754439 / 25000)
      (226278303223989 / 100000) := by
  exact
    packedTile65536 2262710528 2262841600 14 6093 47567 31 _ _ (2153981 / 100000) (67312 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2262841600 :
    ThetaLowerSegment 2262841600 2262972672 (226278303223989 / 100000) (2262913413073 / 1000) := by
  exact
    packedTile65536 2262841600 2262972672 14 6053 47569 31 _ _ (2153987 / 100000) (215399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2262972672 :
    ThetaLowerSegment 2262972672 2263103744 (2262913413073 / 1000) (113152220946363 / 50000) := by
  exact
    packedTile65536 2262972672 2263103744 14 6082 47570 31 _ _ (2153993 / 100000) (538499 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2263103744 :
    ThetaLowerSegment 2263103744 2263234816 (113152220946363 / 50000) (2828969389133 / 1250) := by
  exact
    packedTile65536 2263103744 2263234816 14 6086 47572 31 _ _ (2153999 / 100000) (1077001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2263234816 :
    ThetaLowerSegment 2263234816 2263365888 (2828969389133 / 1250) (2263306733291 / 1000) := by
  exact
    packedTile65536 2263234816 2263365888 14 6092 47573 31 _ _ (430801 / 20000) (269251 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2263365888 :
    ThetaLowerSegment 2263365888 2263496960 (2263306733291 / 1000) (22634379771203 / 10000) := by
  exact
    packedTile65536 2263365888 2263496960 14 6093 47574 31 _ _ (215401 / 10000) (2154013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2263496960 :
    ThetaLowerSegment 2263496960 2263628032 (22634379771203 / 10000) (113178515993167 / 50000) := by
  exact
    packedTile65536 2263496960 2263628032 14 6144 47576 31 _ _ (67313 / 3125) (2154019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2263628032 :
    ThetaLowerSegment 2263628032 2263759104 (113178515993167 / 50000)
      (113185036217761 / 50000) := by
  exact
    packedTile65536 2263628032 2263759104 14 6054 47577 31 _ _ (1077011 / 50000) (86161 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2263759104 :
    ThetaLowerSegment 2263759104 2263890176 (113185036217761 / 50000)
      (113191609234203 / 50000) := by
  exact
    packedTile65536 2263759104 2263890176 14 6103 47578 31 _ _ (538507 / 25000) (2154031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2263890176 :
    ThetaLowerSegment 2263890176 2264021248 (113191609234203 / 50000) (11319810472373 / 5000) := by
  exact
    packedTile65536 2263890176 2264021248 14 6031 47580 31 _ _ (1077017 / 50000) (2154037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2264021248 :
    ThetaLowerSegment 2264021248 2264152320 (11319810472373 / 5000) (226409239229371 / 100000) := by
  exact
    packedTile65536 2264021248 2264152320 14 6049 47581 31 _ _ (2154039 / 100000) (1077021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2264152320 :
    ThetaLowerSegment 2264152320 2264283392 (226409239229371 / 100000)
      (226422391828141 / 100000) := by
  exact
    packedTile65536 2264152320 2264283392 14 6106 47583 31 _ _ (430809 / 20000) (67314 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2264283392 :
    ThetaLowerSegment 2264283392 2264414464 (226422391828141 / 100000)
      (226435570312159 / 100000) := by
  exact
    packedTile65536 2264283392 2264414464 14 6118 47584 31 _ _ (2154051 / 100000) (1077027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2264414464 :
    ThetaLowerSegment 2264414464 2264545536 (226435570312159 / 100000) (905794521439 / 400) := by
  exact
    packedTile65536 2264414464 2264545536 14 6063 47585 31 _ _ (2154057 / 100000) (107703 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2264545536 :
    ThetaLowerSegment 2264545536 2264676608 (905794521439 / 400) (56615453843313 / 25000) := by
  exact
    packedTile65536 2264545536 2264676608 14 6121 47587 31 _ _ (1077031 / 50000) (430813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2264676608 :
    ThetaLowerSegment 2264676608 2264807680 (56615453843313 / 25000) (2830935081967 / 1250) := by
  exact
    packedTile65536 2264676608 2264807680 14 6031 47588 31 _ _ (538517 / 25000) (2154071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2264807680 :
    ThetaLowerSegment 2264807680 2264938752 (2830935081967 / 1250) (56621955368117 / 25000) := by
  exact
    packedTile65536 2264807680 2264938752 14 6042 47589 31 _ _ (1077037 / 50000) (2154077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2264938752 :
    ThetaLowerSegment 2264938752 2265069824 (56621955368117 / 25000) (56625262957957 / 25000) := by
  exact
    packedTile65536 2264938752 2265069824 14 6142 47591 31 _ _ (13463 / 625) (2154083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2265069824 :
    ThetaLowerSegment 2265069824 2265200896 (56625262957957 / 25000) (22651427145761 / 10000) := by
  exact
    packedTile65536 2265069824 2265200896 14 6137 47592 31 _ _ (1077043 / 50000) (2154089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2265200896 :
    ThetaLowerSegment 2265200896 2265331968 (22651427145761 / 10000) (56631845313859 / 25000) := by
  exact
    packedTile65536 2265200896 2265331968 14 6086 47594 31 _ _ (2154091 / 100000) (1077047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2265331968 :
    ThetaLowerSegment 2265331968 2265463040 (56631845313859 / 25000)
      (226540480319293 / 100000) := by
  exact
    packedTile65536 2265331968 2265463040 14 6081 47595 31 _ _ (2154097 / 100000) (21541 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2265463040 :
    ThetaLowerSegment 2265463040 2265594112 (226540480319293 / 100000)
      (56638347464643 / 25000) := by
  exact
    packedTile65536 2265463040 2265594112 14 5993 47596 31 _ _ (2154103 / 100000) (1077053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2265594112 :
    ThetaLowerSegment 2265594112 2265725184 (56638347464643 / 25000) (14160408120217 / 6250) := by
  exact
    packedTile65536 2265594112 2265725184 14 6100 47598 31 _ _ (2154109 / 100000) (67316 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2265725184 :
    ThetaLowerSegment 2265725184 2265856256 (14160408120217 / 6250) (226579685103777 / 100000) := by
  exact
    packedTile65536 2265725184 2265856256 14 6107 47599 31 _ _ (430823 / 20000) (1077059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2265856256 :
    ThetaLowerSegment 2265856256 2265987328 (226579685103777 / 100000)
      (226592670139137 / 100000) := by
  exact
    packedTile65536 2265856256 2265987328 14 6028 47601 31 _ _ (53853 / 2500) (2154123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2265987328 :
    ThetaLowerSegment 2265987328 2266118400 (226592670139137 / 100000)
      (226605909397533 / 100000) := by
  exact
    packedTile65536 2265987328 2266118400 14 6146 47602 31 _ _ (1077063 / 50000) (2154129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2266118400 :
    ThetaLowerSegment 2266118400 2266249472 (226605909397533 / 100000)
      (226618737253593 / 100000) := by
  exact
    packedTile65536 2266118400 2266249472 14 5955 47603 31 _ _ (538533 / 25000) (430827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2266249472 :
    ThetaLowerSegment 2266249472 2266380544 (226618737253593 / 100000)
      (226632163995747 / 100000) := by
  exact
    packedTile65536 2266249472 2266380544 14 6233 47605 31 _ _ (1077069 / 50000) (2154141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2266380544 :
    ThetaLowerSegment 2266380544 2266511616 (226632163995747 / 100000)
      (45329050513723 / 20000) := by
  exact
    packedTile65536 2266380544 2266511616 14 6076 47606 31 _ _ (2154143 / 100000) (1077073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2266511616 :
    ThetaLowerSegment 2266511616 2266642688 (45329050513723 / 20000)
      (226658336869641 / 100000) := by
  exact
    packedTile65536 2266511616 2266642688 14 6074 47607 31 _ _ (2154149 / 100000) (269269 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2266642688 :
    ThetaLowerSegment 2266642688 2266773760 (226658336869641 / 100000)
      (226671563381341 / 100000) := by
  exact
    packedTile65536 2266642688 2266773760 14 6140 47609 31 _ _ (430831 / 20000) (1077079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2266773760 :
    ThetaLowerSegment 2266773760 2266904832 (226671563381341 / 100000)
      (22668468006767 / 10000) := by
  exact
    packedTile65536 2266773760 2266904832 14 6089 47610 31 _ _ (2154161 / 100000) (538541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2266904832 :
    ThetaLowerSegment 2266904832 2267035904 (22668468006767 / 10000) (113348918859853 / 50000) := by
  exact
    packedTile65536 2266904832 2267035904 14 6108 47612 31 _ _ (2154167 / 100000) (215417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2267035904 :
    ThetaLowerSegment 2267035904 2267166976 (113348918859853 / 50000)
      (113355508472001 / 50000) := by
  exact
    packedTile65536 2267035904 2267166976 14 6118 47613 31 _ _ (538543 / 25000) (86167 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2267166976 :
    ThetaLowerSegment 2267166976 2267298048 (113355508472001 / 50000) (2267240303333 / 1000) := by
  exact
    packedTile65536 2267166976 2267298048 14 6041 47614 31 _ _ (1077089 / 50000) (2154181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2267298048 :
    ThetaLowerSegment 2267298048 2267429120 (2267240303333 / 1000) (56684302946299 / 25000) := by
  exact
    packedTile65536 2267298048 2267429120 14 6119 47616 31 _ _ (269273 / 12500) (2154187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2267429120 :
    ThetaLowerSegment 2267429120 2267560192 (56684302946299 / 25000) (28343802121237 / 12500) := by
  exact
    packedTile65536 2267429120 2267560192 14 6130 47617 31 _ _ (215419 / 10000) (2154193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2267560192 :
    ThetaLowerSegment 2267560192 2267691264 (28343802121237 / 12500) (11338178847663 / 5000) := by
  exact
    packedTile65536 2267560192 2267691264 14 6109 47618 31 _ _ (538549 / 25000) (2154199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2267691264 :
    ThetaLowerSegment 2267691264 2267822336 (11338178847663 / 5000) (45355345670073 / 20000) := by
  exact
    packedTile65536 2267691264 2267822336 14 6105 47620 31 _ _ (2154201 / 100000) (538551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2267822336 :
    ThetaLowerSegment 2267822336 2267953408 (45355345670073 / 20000)
      (226789899171963 / 100000) := by
  exact
    packedTile65536 2267822336 2267953408 14 6114 47621 31 _ _ (2154207 / 100000) (215421 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2267953408 :
    ThetaLowerSegment 2267953408 2268084480 (226789899171963 / 100000)
      (56700756197943 / 25000) := by
  exact
    packedTile65536 2267953408 2268084480 14 6093 47623 31 _ _ (2154213 / 100000) (269277 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2268084480 :
    ThetaLowerSegment 2268084480 2268215552 (56700756197943 / 25000) (113408071992741 / 50000) := by
  exact
    packedTile65536 2268084480 2268215552 14 6090 47624 31 _ _ (2154219 / 100000) (1077111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2268215552 :
    ThetaLowerSegment 2268215552 2268346624 (113408071992741 / 50000)
      (113414549744309 / 50000) := by
  exact
    packedTile65536 2268215552 2268346624 14 6014 47625 31 _ _ (134639 / 6250) (2154227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2268346624 :
    ThetaLowerSegment 2268346624 2268477696 (113414549744309 / 50000) (56710576768187 / 25000) := by
  exact
    packedTile65536 2268346624 2268477696 14 6131 47627 31 _ _ (215423 / 10000) (2154233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2268477696 :
    ThetaLowerSegment 2268477696 2268608768 (56710576768187 / 25000) (28356916178671 / 12500) := by
  exact
    packedTile65536 2268477696 2268608768 14 6045 47628 31 _ _ (538559 / 25000) (2154239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2268608768 :
    ThetaLowerSegment 2268608768 2268739840 (28356916178671 / 12500) (14179263237283 / 6250) := by
  exact
    packedTile65536 2268608768 2268739840 14 5980 47629 31 _ _ (1077121 / 50000) (430849 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2268739840 :
    ThetaLowerSegment 2268739840 2268870912 (14179263237283 / 6250) (1134406645063 / 500) := by
  exact
    packedTile65536 2268739840 2268870912 14 6089 47631 31 _ _ (269281 / 12500) (2154251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2268870912 :
    ThetaLowerSegment 2268870912 2269001984 (1134406645063 / 500) (113447211281167 / 50000) := by
  exact
    packedTile65536 2268870912 2269001984 14 6078 47632 31 _ _ (2154253 / 100000) (134641 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2269001984 :
    ThetaLowerSegment 2269001984 2269133056 (113447211281167 / 50000)
      (226907617398709 / 100000) := by
  exact
    packedTile65536 2269001984 2269133056 14 6125 47634 31 _ _ (2154259 / 100000) (1077131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2269133056 :
    ThetaLowerSegment 2269133056 2269264128 (226907617398709 / 100000)
      (56730208453621 / 25000) := by
  exact
    packedTile65536 2269133056 2269264128 14 6135 47635 31 _ _ (430853 / 20000) (538567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2269264128 :
    ThetaLowerSegment 2269264128 2269395200 (56730208453621 / 25000)
      (226933778828923 / 100000) := by
  exact
    packedTile65536 2269264128 2269395200 14 6009 47636 31 _ _ (2154271 / 100000) (1077137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2269395200 :
    ThetaLowerSegment 2269395200 2269526272 (226933778828923 / 100000)
      (226946863901347 / 100000) := by
  exact
    packedTile65536 2269395200 2269526272 14 6074 47638 31 _ _ (538569 / 25000) (2154279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2269526272 :
    ThetaLowerSegment 2269526272 2269657344 (226946863901347 / 100000) (9078407008393 / 4000) := by
  exact
    packedTile65536 2269526272 2269657344 14 6179 47639 31 _ _ (1077141 / 50000) (430857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2269657344 :
    ThetaLowerSegment 2269657344 2269788416 (9078407008393 / 4000) (226973355143809 / 100000) := by
  exact
    packedTile65536 2269657344 2269788416 14 6118 47640 31 _ _ (134643 / 6250) (2154291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2269788416 :
    ThetaLowerSegment 2269788416 2269919488 (226973355143809 / 100000)
      (45397292373701 / 20000) := by
  exact
    packedTile65536 2269788416 2269919488 14 6084 47642 31 _ _ (1077147 / 50000) (2154297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2269919488 :
    ThetaLowerSegment 2269919488 2270050560 (45397292373701 / 20000) (45399918465401 / 20000) := by
  exact
    packedTile65536 2269919488 2270050560 14 6095 47643 31 _ _ (21543 / 1000) (2154303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270050560 :
    ThetaLowerSegment 2270050560 2270181632 (45399918465401 / 20000) (11350636140799 / 5000) := by
  exact
    packedTile65536 2270050560 2270181632 14 6095 47645 31 _ _ (430861 / 20000) (538577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270181632 :
    ThetaLowerSegment 2270181632 2270312704 (11350636140799 / 5000) (56756429404983 / 25000) := by
  exact
    packedTile65536 2270181632 2270312704 14 6032 47646 31 _ _ (2154311 / 100000) (1077157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270312704 :
    ThetaLowerSegment 2270312704 2270443776 (56756429404983 / 25000) (45407788594399 / 20000) := by
  exact
    packedTile65536 2270312704 2270443776 14 6139 47647 31 _ _ (2154317 / 100000) (26929 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270443776 :
    ThetaLowerSegment 2270443776 2270574848 (45407788594399 / 20000) (9082084235421 / 4000) := by
  exact
    packedTile65536 2270443776 2270574848 14 6110 47649 31 _ _ (2154323 / 100000) (1077163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270574848 :
    ThetaLowerSegment 2270574848 2270705920 (9082084235421 / 4000) (227065374391677 / 100000) := by
  exact
    packedTile65536 2270574848 2270705920 14 6159 47650 31 _ _ (269291 / 12500) (2154331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270705920 :
    ThetaLowerSegment 2270705920 2270836992 (227065374391677 / 100000)
      (45415699718881 / 20000) := by
  exact
    packedTile65536 2270705920 2270836992 14 6092 47651 31 _ _ (1077167 / 50000) (2154337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270836992 :
    ThetaLowerSegment 2270836992 2270968064 (45415699718881 / 20000) (45418323274133 / 20000) := by
  exact
    packedTile65536 2270836992 2270968064 14 6089 47653 31 _ _ (107717 / 5000) (2154343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270968064 :
    ThetaLowerSegment 2270968064 2271099136 (45418323274133 / 20000)
      (227104859135527 / 100000) := by
  exact
    packedTile65536 2270968064 2271099136 14 6147 47654 31 _ _ (1077173 / 50000) (2154349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2271099136 :
    ThetaLowerSegment 2271099136 2271230208 (227104859135527 / 100000)
      (56779503939271 / 25000) := by
  exact
    packedTile65536 2271099136 2271230208 14 6107 47656 31 _ _ (2154351 / 100000) (1077177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2271230208 :
    ThetaLowerSegment 2271230208 2271361280 (56779503939271 / 25000)
      (227131004375437 / 100000) := by
  exact
    packedTile65536 2271230208 2271361280 14 6029 47657 31 _ _ (2154357 / 100000) (53859 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2271361280 :
    ThetaLowerSegment 2271361280 2271492352 (227131004375437 / 100000)
      (113572132239851 / 50000) := by
  exact
    packedTile65536 2271361280 2271492352 14 6155 47658 31 _ _ (2154363 / 100000) (1077183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2271492352 :
    ThetaLowerSegment 2271492352 2271623424 (113572132239851 / 50000) (5678934183799 / 2500) := by
  exact
    packedTile65536 2271492352 2271623424 14 6082 47660 31 _ _ (2154369 / 100000) (538593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2271623424 :
    ThetaLowerSegment 2271623424 2271754496 (5678934183799 / 2500) (45434098791767 / 20000) := by
  exact
    packedTile65536 2271623424 2271754496 14 6093 47661 31 _ _ (3447 / 160) (1077189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2271754496 :
    ThetaLowerSegment 2271754496 2271885568 (45434098791767 / 20000) (45436731444127 / 20000) := by
  exact
    packedTile65536 2271754496 2271885568 14 6110 47662 31 _ _ (107719 / 5000) (2154383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2271885568 :
    ThetaLowerSegment 2271885568 2272016640 (45436731444127 / 20000)
      (227196956245413 / 100000) := by
  exact
    packedTile65536 2271885568 2272016640 14 6173 47664 31 _ _ (1077193 / 50000) (2154389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2272016640 :
    ThetaLowerSegment 2272016640 2272147712 (227196956245413 / 100000)
      (227209979545053 / 100000) := by
  exact
    packedTile65536 2272016640 2272147712 14 6045 47665 31 _ _ (269299 / 12500) (430879 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2272147712 :
    ThetaLowerSegment 2272147712 2272278784 (227209979545053 / 100000)
      (227223095520077 / 100000) := by
  exact
    packedTile65536 2272147712 2272278784 14 6088 47667 31 _ _ (1077199 / 50000) (2154401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2272278784 :
    ThetaLowerSegment 2272278784 2272409856 (227223095520077 / 100000)
      (45447224208123 / 20000) := by
  exact
    packedTile65536 2272278784 2272409856 14 6046 47668 31 _ _ (2154403 / 100000) (1077203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2272409856 :
    ThetaLowerSegment 2272409856 2272540928 (45447224208123 / 20000)
      (227249181067973 / 100000) := by
  exact
    packedTile65536 2272409856 2272540928 14 6062 47669 31 _ _ (2154409 / 100000) (538603 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2272540928 :
    ThetaLowerSegment 2272540928 2272672000 (227249181067973 / 100000)
      (227262357470113 / 100000) := by
  exact
    packedTile65536 2272540928 2272672000 14 6116 47671 31 _ _ (430883 / 20000) (1077209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2272672000 :
    ThetaLowerSegment 2272672000 2272803072 (227262357470113 / 100000)
      (113637802502421 / 50000) := by
  exact
    packedTile65536 2272672000 2272803072 14 6149 47672 31 _ _ (2154421 / 100000) (269303 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2272803072 :
    ThetaLowerSegment 2272803072 2272934144 (113637802502421 / 50000)
      (113644367038443 / 50000) := by
  exact
    packedTile65536 2272803072 2272934144 14 6094 47673 31 _ _ (1077213 / 50000) (2154429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2272934144 :
    ThetaLowerSegment 2272934144 2273065216 (113644367038443 / 50000) (22730199891471 / 10000) := by
  exact
    packedTile65536 2272934144 2273065216 14 6157 47675 31 _ _ (67326 / 3125) (430887 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2273065216 :
    ThetaLowerSegment 2273065216 2273196288 (22730199891471 / 10000) (113657471389107 / 50000) := by
  exact
    packedTile65536 2273065216 2273196288 14 6008 47676 31 _ _ (1077219 / 50000) (2154441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2273196288 :
    ThetaLowerSegment 2273196288 2273327360 (113657471389107 / 50000)
      (113664096304407 / 50000) := by
  exact
    packedTile65536 2273196288 2273327360 14 6150 47678 31 _ _ (538611 / 25000) (2154447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2273327360 :
    ThetaLowerSegment 2273327360 2273458432 (113664096304407 / 50000)
      (113670652295757 / 50000) := by
  exact
    packedTile65536 2273327360 2273458432 14 6086 47679 31 _ _ (43089 / 2000) (2154453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2273458432 :
    ThetaLowerSegment 2273458432 2273589504 (113670652295757 / 50000)
      (227354556644219 / 100000) := by
  exact
    packedTile65536 2273458432 2273589504 14 6151 47680 31 _ _ (430891 / 20000) (1077229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2273589504 :
    ThetaLowerSegment 2273589504 2273720576 (227354556644219 / 100000)
      (227367720400929 / 100000) := by
  exact
    packedTile65536 2273589504 2273720576 14 6110 47682 31 _ _ (2154461 / 100000) (67327 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2273720576 :
    ThetaLowerSegment 2273720576 2273851648 (227367720400929 / 100000)
      (56845231282293 / 25000) := by
  exact
    packedTile65536 2273720576 2273851648 14 6129 47683 31 _ _ (2154467 / 100000) (215447 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2273851648 :
    ThetaLowerSegment 2273851648 2273982720 (56845231282293 / 25000)
      (227394017861593 / 100000) := by
  exact
    packedTile65536 2273851648 2273982720 14 6077 47684 31 _ _ (2154473 / 100000) (538619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2273982720 :
    ThetaLowerSegment 2273982720 2274113792 (227394017861593 / 100000)
      (227407069689317 / 100000) := by
  exact
    packedTile65536 2273982720 2274113792 14 6058 47686 31 _ _ (1077239 / 50000) (2154481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2274113792 :
    ThetaLowerSegment 2274113792 2274244864 (227407069689317 / 100000)
      (227420384400437 / 100000) := by
  exact
    packedTile65536 2274113792 2274244864 14 6180 47687 31 _ _ (538621 / 25000) (2154487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2274244864 :
    ThetaLowerSegment 2274244864 2274375936 (227420384400437 / 100000)
      (227433485854127 / 100000) := by
  exact
    packedTile65536 2274244864 2274375936 14 6081 47689 31 _ _ (215449 / 10000) (2154493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2274375936 :
    ThetaLowerSegment 2274375936 2274507008 (227433485854127 / 100000)
      (227446628279727 / 100000) := by
  exact
    packedTile65536 2274375936 2274507008 14 6100 47690 31 _ _ (67328 / 3125) (2154499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2274507008 :
    ThetaLowerSegment 2274507008 2274638080 (227446628279727 / 100000)
      (227459736263811 / 100000) := by
  exact
    packedTile65536 2274507008 2274638080 14 6084 47691 31 _ _ (2154501 / 100000) (269313 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2274638080 :
    ThetaLowerSegment 2274638080 2274769152 (227459736263811 / 100000)
      (45494628321273 / 20000) := by
  exact
    packedTile65536 2274638080 2274769152 14 6222 47693 31 _ _ (2154507 / 100000) (215451 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2274769152 :
    ThetaLowerSegment 2274769152 2274900224 (45494628321273 / 20000)
      (227486055757287 / 100000) := by
  exact
    packedTile65536 2274769152 2274900224 14 5994 47694 31 _ _ (2154513 / 100000) (538629 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2274900224 :
    ThetaLowerSegment 2274900224 2275031296 (227486055757287 / 100000)
      (227499133687617 / 100000) := by
  exact
    packedTile65536 2274900224 2275031296 14 6070 47695 31 _ _ (2154519 / 100000) (1077261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2275031296 :
    ThetaLowerSegment 2275031296 2275162368 (227499133687617 / 100000)
      (227512304292829 / 100000) := by
  exact
    packedTile65536 2275031296 2275162368 14 6113 47697 31 _ _ (538631 / 25000) (2154527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2275162368 :
    ThetaLowerSegment 2275162368 2275293440 (227512304292829 / 100000)
      (227525410298819 / 100000) := by
  exact
    packedTile65536 2275162368 2275293440 14 6083 47698 31 _ _ (215453 / 10000) (2154533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2275293440 :
    ThetaLowerSegment 2275293440 2275424512 (227525410298819 / 100000)
      (227538432314403 / 100000) := by
  exact
    packedTile65536 2275293440 2275424512 14 6044 47700 31 _ _ (269317 / 12500) (2154539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2275424512 :
    ThetaLowerSegment 2275424512 2275555584 (227538432314403 / 100000)
      (227551482375297 / 100000) := by
  exact
    packedTile65536 2275424512 2275555584 14 6057 47701 31 _ _ (1077271 / 50000) (430909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2275555584 :
    ThetaLowerSegment 2275555584 2275686656 (227551482375297 / 100000)
      (45512923299981 / 20000) := by
  exact
    packedTile65536 2275555584 2275686656 14 6096 47702 31 _ _ (538637 / 25000) (2154551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2275686656 :
    ThetaLowerSegment 2275686656 2275817728 (45512923299981 / 20000)
      (227577681709297 / 100000) := by
  exact
    packedTile65536 2275686656 2275817728 14 6064 47704 31 _ _ (2154553 / 100000) (538639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2275817728 :
    ThetaLowerSegment 2275817728 2275948800 (227577681709297 / 100000)
      (227590863301259 / 100000) := by
  exact
    packedTile65536 2275817728 2275948800 14 6118 47705 31 _ _ (2154559 / 100000) (1077281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2275948800 :
    ThetaLowerSegment 2275948800 2276079872 (227590863301259 / 100000)
      (113802066633547 / 50000) := by
  exact
    packedTile65536 2275948800 2276079872 14 6159 47706 31 _ _ (430913 / 20000) (269321 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2276079872 :
    ThetaLowerSegment 2276079872 2276210944 (113802066633547 / 50000)
      (227617355869321 / 100000) := by
  exact
    packedTile65536 2276079872 2276210944 14 6137 47708 31 _ _ (2154571 / 100000) (1077287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2276210944 :
    ThetaLowerSegment 2276210944 2276342016 (227617355869321 / 100000)
      (227630412599881 / 100000) := by
  exact
    packedTile65536 2276210944 2276342016 14 6060 47709 31 _ _ (134661 / 6250) (2154579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2276342016 :
    ThetaLowerSegment 2276342016 2276473088 (227630412599881 / 100000)
      (45528683962283 / 20000) := by
  exact
    packedTile65536 2276342016 2276473088 14 6037 47711 31 _ _ (1077291 / 50000) (430917 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2276473088 :
    ThetaLowerSegment 2276473088 2276604160 (45528683962283 / 20000)
      (227656590807859 / 100000) := by
  exact
    packedTile65536 2276473088 2276604160 14 6113 47712 31 _ _ (538647 / 25000) (2154591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2276604160 :
    ThetaLowerSegment 2276604160 2276735232 (227656590807859 / 100000)
      (227669738140447 / 100000) := by
  exact
    packedTile65536 2276604160 2276735232 14 6102 47713 31 _ _ (1077297 / 50000) (2154597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2276735232 :
    ThetaLowerSegment 2276735232 2276866304 (227669738140447 / 100000)
      (56920719759937 / 25000) := by
  exact
    packedTile65536 2276735232 2276866304 14 6099 47715 31 _ _ (2154599 / 100000) (1077301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2276866304 :
    ThetaLowerSegment 2276866304 2276997376 (56920719759937 / 25000) (7115497998314 / 3125) := by
  exact
    packedTile65536 2276866304 2276997376 14 6060 47716 31 _ _ (430921 / 20000) (134663 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2276997376 :
    ThetaLowerSegment 2276997376 2277128448 (7115497998314 / 3125) (45541801594197 / 20000) := by
  exact
    packedTile65536 2276997376 2277128448 14 6067 47717 31 _ _ (2154611 / 100000) (1077307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2277128448 :
    ThetaLowerSegment 2277128448 2277259520 (45541801594197 / 20000)
      (227722176990089 / 100000) := by
  exact
    packedTile65536 2277128448 2277259520 14 6112 47719 31 _ _ (2154617 / 100000) (107731 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2277259520 :
    ThetaLowerSegment 2277259520 2277390592 (227722176990089 / 100000)
      (227735249081763 / 100000) := by
  exact
    packedTile65536 2277259520 2277390592 14 6067 47720 31 _ _ (1077311 / 50000) (17237 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2277390592 :
    ThetaLowerSegment 2277390592 2277521664 (227735249081763 / 100000)
      (227748364302399 / 100000) := by
  exact
    packedTile65536 2277390592 2277521664 14 6087 47722 31 _ _ (538657 / 25000) (2154631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2277521664 :
    ThetaLowerSegment 2277521664 2277652736 (227748364302399 / 100000)
      (227761542043943 / 100000) := by
  exact
    packedTile65536 2277521664 2277652736 14 6116 47723 31 _ _ (1077317 / 50000) (2154637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2277652736 :
    ThetaLowerSegment 2277652736 2277783808 (227761542043943 / 100000)
      (227774709048983 / 100000) := by
  exact
    packedTile65536 2277652736 2277783808 14 6111 47724 31 _ _ (26933 / 1250) (2154643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2277783808 :
    ThetaLowerSegment 2277783808 2277914880 (227774709048983 / 100000)
      (227787667084013 / 100000) := by
  exact
    packedTile65536 2277783808 2277914880 14 6014 47726 31 _ _ (430929 / 20000) (269331 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2277914880 :
    ThetaLowerSegment 2277914880 2278045952 (227787667084013 / 100000)
      (113900378294419 / 50000) := by
  exact
    packedTile65536 2277914880 2278045952 14 6075 47727 31 _ _ (2154651 / 100000) (1077327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278045952 :
    ThetaLowerSegment 2278045952 2278177024 (113900378294419 / 50000)
      (227813850439427 / 100000) := by
  exact
    packedTile65536 2278045952 2278177024 14 6077 47728 31 _ _ (2154657 / 100000) (107733 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278177024 :
    ThetaLowerSegment 2278177024 2278308096 (227813850439427 / 100000)
      (227826929243837 / 100000) := by
  exact
    packedTile65536 2278177024 2278308096 14 6070 47730 31 _ _ (2154663 / 100000) (1077333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278308096 :
    ThetaLowerSegment 2278308096 2278439168 (227826929243837 / 100000)
      (227839997305257 / 100000) := by
  exact
    packedTile65536 2278308096 2278439168 14 6065 47731 31 _ _ (538667 / 25000) (2154671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278439168 :
    ThetaLowerSegment 2278439168 2278570240 (227839997305257 / 100000)
      (227853052475023 / 100000) := by
  exact
    packedTile65536 2278439168 2278570240 14 6059 47732 31 _ _ (1077337 / 50000) (2154677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278570240 :
    ThetaLowerSegment 2278570240 2278701312 (227853052475023 / 100000)
      (227865952544183 / 100000) := by
  exact
    packedTile65536 2278570240 2278701312 14 5987 47734 31 _ _ (53867 / 2500) (2154683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278701312 :
    ThetaLowerSegment 2278701312 2278832384 (227865952544183 / 100000) (9115159277217 / 4000) := by
  exact
    packedTile65536 2278701312 2278832384 14 6047 47735 31 _ _ (1077343 / 50000) (2154689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278832384 :
    ThetaLowerSegment 2278832384 2278963456 (9115159277217 / 4000) (227892246208221 / 100000) := by
  exact
    packedTile65536 2278832384 2278963456 14 6156 47737 31 _ _ (2154691 / 100000) (1077347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278963456 :
    ThetaLowerSegment 2278963456 2279094528 (227892246208221 / 100000)
      (113952674460339 / 50000) := by
  exact
    packedTile65536 2278963456 2279094528 14 6081 47738 31 _ _ (2154697 / 100000) (21547 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2279094528 :
    ThetaLowerSegment 2279094528 2279225600 (113952674460339 / 50000)
      (227918443050809 / 100000) := by
  exact
    packedTile65536 2279094528 2279225600 14 6077 47739 31 _ _ (2154703 / 100000) (1077353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2279225600 :
    ThetaLowerSegment 2279225600 2279356672 (227918443050809 / 100000)
      (113965721205103 / 50000) := by
  exact
    packedTile65536 2279225600 2279356672 14 6033 47741 31 _ _ (2154709 / 100000) (269339 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2279356672 :
    ThetaLowerSegment 2279356672 2279487744 (113965721205103 / 50000) (22794440516963 / 10000) := by
  exact
    packedTile65536 2279356672 2279487744 14 6016 47742 31 _ _ (1077357 / 50000) (2154717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2279487744 :
    ThetaLowerSegment 2279487744 2279618816 (22794440516963 / 10000) (22795745846339 / 10000) := by
  exact
    packedTile65536 2279487744 2279618816 14 6058 47743 31 _ _ (13467 / 625) (2154723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2279618816 :
    ThetaLowerSegment 2279618816 2279749888 (22795745846339 / 10000) (4559408167333 / 2000) := by
  exact
    packedTile65536 2279618816 2279749888 14 6010 47745 31 _ _ (1077363 / 50000) (2154729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2279749888 :
    ThetaLowerSegment 2279749888 2279880960 (4559408167333 / 2000) (113991753491239 / 50000) := by
  exact
    packedTile65536 2279749888 2279880960 14 6079 47746 31 _ _ (538683 / 25000) (430947 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2279880960 :
    ThetaLowerSegment 2279880960 2280012032 (113991753491239 / 50000) (11399826726119 / 5000) := by
  exact
    packedTile65536 2279880960 2280012032 14 6046 47748 31 _ _ (2154737 / 100000) (107737 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2280012032 :
    ThetaLowerSegment 2280012032 2280143104 (11399826726119 / 5000) (57002434696871 / 25000) := by
  exact
    packedTile65536 2280012032 2280143104 14 6128 47749 31 _ _ (2154743 / 100000) (1077373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2280143104 :
    ThetaLowerSegment 2280143104 2280274176 (57002434696871 / 25000) (114011361652479 / 50000) := by
  exact
    packedTile65536 2280143104 2280274176 14 6026 47750 31 _ _ (2154749 / 100000) (67336 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2280274176 :
    ThetaLowerSegment 2280274176 2280405248 (114011361652479 / 50000) (14252244131003 / 6250) := by
  exact
    packedTile65536 2280274176 2280405248 14 6118 47752 31 _ _ (430951 / 20000) (1077379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2280405248 :
    ThetaLowerSegment 2280405248 2280536320 (14252244131003 / 6250) (28506145541791 / 12500) := by
  exact
    packedTile65536 2280405248 2280536320 14 6153 47753 31 _ _ (53869 / 2500) (2154763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2280536320 :
    ThetaLowerSegment 2280536320 2280667392 (28506145541791 / 12500) (114031017375823 / 50000) := by
  exact
    packedTile65536 2280536320 2280667392 14 5973 47754 31 _ _ (1077383 / 50000) (2154769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2280667392 :
    ThetaLowerSegment 2280667392 2280798464 (114031017375823 / 50000)
      (114037632525863 / 50000) := by
  exact
    packedTile65536 2280667392 2280798464 14 6140 47756 31 _ _ (538693 / 25000) (86191 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2280798464 :
    ThetaLowerSegment 2280798464 2280929536 (114037632525863 / 50000)
      (114044165812759 / 50000) := by
  exact
    packedTile65536 2280798464 2280929536 14 6064 47757 31 _ _ (1077389 / 50000) (2154781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2280929536 :
    ThetaLowerSegment 2280929536 2281060608 (114044165812759 / 50000) (22810139822963 / 10000) := by
  exact
    packedTile65536 2280929536 2281060608 14 6064 47759 31 _ _ (2154783 / 100000) (1077393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281060608 :
    ThetaLowerSegment 2281060608 2281191680 (22810139822963 / 10000)
      (228114518739851 / 100000) := by
  exact
    packedTile65536 2281060608 2281191680 14 6089 47760 31 _ _ (2154789 / 100000) (269349 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281191680 :
    ThetaLowerSegment 2281191680 2281322752 (228114518739851 / 100000)
      (228127494915341 / 100000) := by
  exact
    packedTile65536 2281191680 2281322752 14 6022 47761 31 _ _ (430959 / 20000) (1077399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281322752 :
    ThetaLowerSegment 2281322752 2281339136 (228127494915341 / 100000)
      (57032278292723 / 25000) := by
  exact
    packedTile65536 2281322752 2281339136 11 751 47763 31 _ _ (2154801 / 100000) (538701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281339136 :
    ThetaLowerSegment 2281339136 2281341184 (57032278292723 / 25000)
      (228129339424997 / 100000) := by
  exact
    packedTile65536 2281339136 2281341184 8 105 47763 31 _ _ (2154801 / 100000) (538701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2249341184_2281341184 :
    ThetaLowerSegment 2249341184 2281341184 (8997098227291 / 4000) (228129339424997 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2249341184 cell2249472256)
                  (ThetaLowerSegment.join cell2249603328 cell2249734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2249865472 cell2249996544)
                  (ThetaLowerSegment.join cell2250127616 cell2250258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2250389760 cell2250520832)
                  (ThetaLowerSegment.join cell2250651904 cell2250782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2250914048 cell2251045120)
                  (ThetaLowerSegment.join cell2251176192 cell2251307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2251438336 cell2251569408)
                  (ThetaLowerSegment.join cell2251700480 cell2251831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2251962624 cell2252093696)
                  (ThetaLowerSegment.join cell2252224768 cell2252355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2252486912 cell2252617984)
                  (ThetaLowerSegment.join cell2252749056 cell2252880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2253011200 cell2253142272)
                  (ThetaLowerSegment.join cell2253273344 cell2253404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2253535488 cell2253666560)
                  (ThetaLowerSegment.join cell2253797632 cell2253928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2254059776 cell2254190848)
                  (ThetaLowerSegment.join cell2254321920 cell2254452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2254584064 cell2254715136)
                  (ThetaLowerSegment.join cell2254846208 cell2254977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2255108352 cell2255239424)
                  (ThetaLowerSegment.join cell2255370496 cell2255501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2255632640 cell2255763712)
                  (ThetaLowerSegment.join cell2255894784 cell2256025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2256156928 cell2256288000)
                  (ThetaLowerSegment.join cell2256419072 cell2256550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2256681216 cell2256812288)
                  (ThetaLowerSegment.join cell2256943360 cell2257074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2257205504 cell2257336576)
                  (ThetaLowerSegment.join cell2257467648 cell2257598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2257729792 cell2257860864)
                  (ThetaLowerSegment.join cell2257991936 cell2258123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2258254080 cell2258385152)
                  (ThetaLowerSegment.join cell2258516224 cell2258647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2258778368 cell2258909440)
                  (ThetaLowerSegment.join cell2259040512 cell2259171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2259302656 cell2259433728)
                  (ThetaLowerSegment.join cell2259564800 cell2259695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2259826944 cell2259958016)
                  (ThetaLowerSegment.join cell2260089088 cell2260220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2260351232 cell2260482304)
                  (ThetaLowerSegment.join cell2260613376 cell2260744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2260875520 cell2261006592)
                  (ThetaLowerSegment.join cell2261137664 cell2261268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2261399808 cell2261530880)
                  (ThetaLowerSegment.join cell2261661952 cell2261793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2261924096 cell2262055168)
                  (ThetaLowerSegment.join cell2262186240 cell2262317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2262448384 cell2262579456)
                  (ThetaLowerSegment.join cell2262710528 cell2262841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2262972672 cell2263103744)
                  (ThetaLowerSegment.join cell2263234816 cell2263365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2263496960 cell2263628032)
                  (ThetaLowerSegment.join cell2263759104 cell2263890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2264021248 cell2264152320)
                  (ThetaLowerSegment.join cell2264283392 cell2264414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2264545536 cell2264676608)
                  (ThetaLowerSegment.join cell2264807680 cell2264938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2265069824 cell2265200896)
                  (ThetaLowerSegment.join cell2265331968 cell2265463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2265594112 cell2265725184)
                  (ThetaLowerSegment.join cell2265856256 cell2265987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2266118400 cell2266249472)
                  (ThetaLowerSegment.join cell2266380544 cell2266511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2266642688 cell2266773760)
                  (ThetaLowerSegment.join cell2266904832 cell2267035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2267166976 cell2267298048)
                  (ThetaLowerSegment.join cell2267429120 cell2267560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2267691264 cell2267822336)
                  (ThetaLowerSegment.join cell2267953408 cell2268084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2268215552 cell2268346624)
                  (ThetaLowerSegment.join cell2268477696 cell2268608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2268739840 cell2268870912)
                  (ThetaLowerSegment.join cell2269001984 cell2269133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2269264128 cell2269395200)
                  (ThetaLowerSegment.join cell2269526272 cell2269657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2269788416 cell2269919488)
                  (ThetaLowerSegment.join cell2270050560 cell2270181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2270312704 cell2270443776)
                  (ThetaLowerSegment.join cell2270574848 cell2270705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2270836992 cell2270968064)
                  (ThetaLowerSegment.join cell2271099136 cell2271230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2271361280 cell2271492352)
                  (ThetaLowerSegment.join cell2271623424 cell2271754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2271885568 cell2272016640)
                  (ThetaLowerSegment.join cell2272147712 cell2272278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2272409856 cell2272540928)
                  (ThetaLowerSegment.join cell2272672000 cell2272803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2272934144 cell2273065216)
                  (ThetaLowerSegment.join cell2273196288 cell2273327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2273458432 cell2273589504)
                  (ThetaLowerSegment.join cell2273720576 cell2273851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2273982720 cell2274113792)
                  (ThetaLowerSegment.join cell2274244864 cell2274375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2274507008 cell2274638080)
                  (ThetaLowerSegment.join cell2274769152 cell2274900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2275031296 cell2275162368)
                  (ThetaLowerSegment.join cell2275293440 cell2275424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2275555584 cell2275686656)
                  (ThetaLowerSegment.join cell2275817728 cell2275948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2276079872 cell2276210944)
                  (ThetaLowerSegment.join cell2276342016 cell2276473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2276604160 cell2276735232)
                  (ThetaLowerSegment.join cell2276866304 cell2276997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2277128448 cell2277259520)
                  (ThetaLowerSegment.join cell2277390592 cell2277521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2277652736 cell2277783808)
                  (ThetaLowerSegment.join cell2277914880 cell2278045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2278177024 cell2278308096)
                  (ThetaLowerSegment.join cell2278439168 cell2278570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2278701312 cell2278832384)
                  (ThetaLowerSegment.join cell2278963456 cell2279094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2279225600 cell2279356672)
                  (ThetaLowerSegment.join cell2279487744 cell2279618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2279749888 cell2279880960)
                  (ThetaLowerSegment.join cell2280012032 cell2280143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2280274176 cell2280405248)
                  (ThetaLowerSegment.join cell2280536320 cell2280667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2280798464 cell2280929536)
                (ThetaLowerSegment.join cell2281060608 cell2281191680))
              (ThetaLowerSegment.join cell2281322752 cell2281339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
