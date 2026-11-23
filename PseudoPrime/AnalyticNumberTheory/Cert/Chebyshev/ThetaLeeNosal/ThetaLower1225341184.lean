/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1225341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1193341184 :
    ThetaLowerSegment 1193341184 1193406720 (3729049404488 / 3125) (119336124736747 / 100000) := by
  exact
    packedTile65536 1193341184 1193406720 13 3131 34544 30 _ _ (2090001 / 100000) (522501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193406720 :
    ThetaLowerSegment 1193406720 1193472256 (119336124736747 / 100000)
      (119342785585869 / 100000) := by
  exact
    packedTile65536 1193406720 1193472256 13 3187 34545 30 _ _ (1045003 / 50000) (2090009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193472256 :
    ThetaLowerSegment 1193472256 1193537792 (119342785585869 / 100000)
      (119349329413441 / 100000) := by
  exact
    packedTile65536 1193472256 1193537792 13 3131 34546 30 _ _ (522503 / 25000) (418003 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193537792 :
    ThetaLowerSegment 1193537792 1193603328 (119349329413441 / 100000)
      (119355766665801 / 100000) := by
  exact
    packedTile65536 1193537792 1193603328 13 3080 34547 30 _ _ (2090017 / 100000) (104501 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193603328 :
    ThetaLowerSegment 1193603328 1193668864 (119355766665801 / 100000) (1492027366331 / 1250) := by
  exact
    packedTile65536 1193603328 1193668864 13 3073 34548 30 _ _ (2090023 / 100000) (1045013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193668864 :
    ThetaLowerSegment 1193668864 1193734400 (1492027366331 / 1250) (29842184341051 / 25000) := by
  exact
    packedTile65536 1193668864 1193734400 13 3133 34549 30 _ _ (522507 / 25000) (2090031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193734400 :
    ThetaLowerSegment 1193734400 1193799936 (29842184341051 / 25000) (59687626000091 / 50000) := by
  exact
    packedTile65536 1193734400 1193799936 13 3117 34550 30 _ _ (1045017 / 50000) (2090037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193799936 :
    ThetaLowerSegment 1193799936 1193865472 (59687626000091 / 50000) (14922725272801 / 12500) := by
  exact
    packedTile65536 1193799936 1193865472 13 3134 34551 30 _ _ (2090039 / 100000) (1045021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193865472 :
    ThetaLowerSegment 1193865472 1193931008 (14922725272801 / 12500)
      (119388392094293 / 100000) := by
  exact
    packedTile65536 1193865472 1193931008 13 3153 34552 30 _ _ (418009 / 20000) (65314 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193931008 :
    ThetaLowerSegment 1193931008 1193996544 (119388392094293 / 100000)
      (119394898419943 / 100000) := by
  exact
    packedTile65536 1193931008 1193996544 13 3113 34553 30 _ _ (41801 / 2000) (2090053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193996544 :
    ThetaLowerSegment 1193996544 1194062080 (119394898419943 / 100000)
      (119401584509087 / 100000) := by
  exact
    packedTile65536 1193996544 1194062080 13 3199 34554 30 _ _ (261257 / 12500) (2090059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194062080 :
    ThetaLowerSegment 1194062080 1194127616 (119401584509087 / 100000)
      (119408076238553 / 100000) := by
  exact
    packedTile65536 1194062080 1194127616 13 3106 34555 30 _ _ (2090061 / 100000) (130629 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194127616 :
    ThetaLowerSegment 1194127616 1194193152 (119408076238553 / 100000)
      (119414530365449 / 100000) := by
  exact
    packedTile65536 1194127616 1194193152 13 3088 34556 30 _ _ (2090067 / 100000) (209007 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194193152 :
    ThetaLowerSegment 1194193152 1194258688 (119414530365449 / 100000)
      (119421124542609 / 100000) := by
  exact
    packedTile65536 1194193152 1194258688 13 3155 34557 30 _ _ (261259 / 12500) (83603 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194258688 :
    ThetaLowerSegment 1194258688 1194324224 (119421124542609 / 100000)
      (119427762630337 / 100000) := by
  exact
    packedTile65536 1194258688 1194324224 13 3176 34558 30 _ _ (1045039 / 50000) (2090081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194324224 :
    ThetaLowerSegment 1194324224 1194389760 (119427762630337 / 100000)
      (119434241887637 / 100000) := by
  exact
    packedTile65536 1194324224 1194389760 13 3100 34558 30 _ _ (2090083 / 100000) (1045043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194389760 :
    ThetaLowerSegment 1194389760 1194455296 (119434241887637 / 100000)
      (119440779686029 / 100000) := by
  exact
    packedTile65536 1194389760 1194455296 13 3128 34559 30 _ _ (2090089 / 100000) (522523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194455296 :
    ThetaLowerSegment 1194455296 1194520832 (119440779686029 / 100000)
      (119447263157617 / 100000) := by
  exact
    packedTile65536 1194455296 1194520832 13 3102 34560 30 _ _ (1045047 / 50000) (2090097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194520832 :
    ThetaLowerSegment 1194520832 1194586368 (119447263157617 / 100000)
      (119453941027117 / 100000) := by
  exact
    packedTile65536 1194520832 1194586368 13 3195 34561 30 _ _ (20901 / 1000) (2090103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194586368 :
    ThetaLowerSegment 1194586368 1194651904 (119453941027117 / 100000)
      (119460416172407 / 100000) := by
  exact
    packedTile65536 1194586368 1194651904 13 3098 34562 30 _ _ (418021 / 20000) (522527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194651904 :
    ThetaLowerSegment 1194651904 1194717440 (119460416172407 / 100000)
      (59733498965973 / 50000) := by
  exact
    packedTile65536 1194651904 1194717440 13 3149 34563 30 _ _ (2090111 / 100000) (1045057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194717440 :
    ThetaLowerSegment 1194717440 1194782976 (59733498965973 / 50000) (59736817025123 / 50000) := by
  exact
    packedTile65536 1194717440 1194782976 13 3175 34564 30 _ _ (522529 / 25000) (2090119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194782976 :
    ThetaLowerSegment 1194782976 1194848512 (59736817025123 / 50000) (59740077615443 / 50000) := by
  exact
    packedTile65536 1194782976 1194848512 13 3120 34565 30 _ _ (1045061 / 50000) (16721 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194848512 :
    ThetaLowerSegment 1194848512 1194914048 (59740077615443 / 50000) (59743346574071 / 50000) := by
  exact
    packedTile65536 1194848512 1194914048 13 3128 34566 30 _ _ (2090127 / 100000) (209013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194914048 :
    ThetaLowerSegment 1194914048 1194979584 (59743346574071 / 50000) (7468331384293 / 6250) := by
  exact
    packedTile65536 1194914048 1194979584 13 3162 34567 30 _ _ (2090133 / 100000) (261267 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194979584 :
    ThetaLowerSegment 1194979584 1195045120 (7468331384293 / 6250) (29874965250433 / 25000) := by
  exact
    packedTile65536 1194979584 1195045120 13 3138 34568 30 _ _ (1045069 / 50000) (2090141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195045120 :
    ThetaLowerSegment 1195045120 1195110656 (29874965250433 / 25000) (59753268459237 / 50000) := by
  exact
    packedTile65536 1195045120 1195110656 13 3194 34569 30 _ _ (2090143 / 100000) (1045073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195110656 :
    ThetaLowerSegment 1195110656 1195176192 (59753268459237 / 50000)
      (119513047732609 / 100000) := by
  exact
    packedTile65536 1195110656 1195176192 13 3115 34570 30 _ _ (2090149 / 100000) (261269 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195176192 :
    ThetaLowerSegment 1195176192 1195241728 (119513047732609 / 100000)
      (119519497947853 / 100000) := by
  exact
    packedTile65536 1195176192 1195241728 13 3086 34571 30 _ _ (1045077 / 50000) (2090157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195241728 :
    ThetaLowerSegment 1195241728 1195307264 (119519497947853 / 100000)
      (119526090312493 / 100000) := by
  exact
    packedTile65536 1195241728 1195307264 13 3154 34572 30 _ _ (26127 / 1250) (2090163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195307264 :
    ThetaLowerSegment 1195307264 1195372800 (119526090312493 / 100000)
      (119532640889603 / 100000) := by
  exact
    packedTile65536 1195307264 1195372800 13 3134 34573 30 _ _ (418033 / 20000) (261271 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195372800 :
    ThetaLowerSegment 1195372800 1195438336 (119532640889603 / 100000)
      (119539174764149 / 100000) := by
  exact
    packedTile65536 1195372800 1195438336 13 3126 34574 30 _ _ (2090171 / 100000) (1045087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195438336 :
    ThetaLowerSegment 1195438336 1195503872 (119539174764149 / 100000)
      (119545744187317 / 100000) := by
  exact
    packedTile65536 1195438336 1195503872 13 3143 34575 30 _ _ (65318 / 3125) (2090179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195503872 :
    ThetaLowerSegment 1195503872 1195569408 (119545744187317 / 100000)
      (23910423430447 / 20000) := by
  exact
    packedTile65536 1195503872 1195569408 13 3049 34576 30 _ _ (1045091 / 50000) (418037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195569408 :
    ThetaLowerSegment 1195569408 1195634944 (23910423430447 / 20000)
      (119558709602033 / 100000) := by
  exact
    packedTile65536 1195569408 1195634944 13 3154 34577 30 _ _ (2090187 / 100000) (209019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195634944 :
    ThetaLowerSegment 1195634944 1195700480 (119558709602033 / 100000)
      (23913068774923 / 20000) := by
  exact
    packedTile65536 1195634944 1195700480 13 3174 34577 30 _ _ (2090193 / 100000) (522549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195700480 :
    ThetaLowerSegment 1195700480 1195766016 (23913068774923 / 20000)
      (119571879923761 / 100000) := by
  exact
    packedTile65536 1195700480 1195766016 13 3127 34578 30 _ _ (1045099 / 50000) (2090201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195766016 :
    ThetaLowerSegment 1195766016 1195831552 (119571879923761 / 100000)
      (119578484968401 / 100000) := by
  exact
    packedTile65536 1195766016 1195831552 13 3160 34579 30 _ _ (522551 / 25000) (2090207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195831552 :
    ThetaLowerSegment 1195831552 1195897088 (119578484968401 / 100000)
      (23917012153183 / 20000) := by
  exact
    packedTile65536 1195831552 1195897088 13 3146 34580 30 _ _ (2090209 / 100000) (522553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195897088 :
    ThetaLowerSegment 1195897088 1195962624 (23917012153183 / 20000) (2989790130727 / 2500) := by
  exact
    packedTile65536 1195897088 1195962624 13 3131 34581 30 _ _ (418043 / 20000) (1045109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1195962624 :
    ThetaLowerSegment 1195962624 1196028160 (2989790130727 / 2500) (298995243631 / 250) := by
  exact
    packedTile65536 1195962624 1196028160 13 3106 34582 30 _ _ (104511 / 5000) (2090223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196028160 :
    ThetaLowerSegment 1196028160 1196093696 (298995243631 / 250) (2392092588173 / 2000) := by
  exact
    packedTile65536 1196028160 1196093696 13 3125 34583 30 _ _ (1045113 / 50000) (2090229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196093696 :
    ThetaLowerSegment 1196093696 1196159232 (2392092588173 / 2000) (747569823948 / 625) := by
  exact
    packedTile65536 1196093696 1196159232 13 3130 34584 30 _ _ (2090231 / 100000) (1045117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196159232 :
    ThetaLowerSegment 1196159232 1196224768 (747569823948 / 625) (119617699641831 / 100000) := by
  exact
    packedTile65536 1196159232 1196224768 13 3123 34585 30 _ _ (2090237 / 100000) (13064 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196224768 :
    ThetaLowerSegment 1196224768 1196290304 (119617699641831 / 100000)
      (23924863887649 / 20000) := by
  exact
    packedTile65536 1196224768 1196290304 13 3167 34586 30 _ _ (1045121 / 50000) (418049 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196290304 :
    ThetaLowerSegment 1196290304 1196355840 (23924863887649 / 20000)
      (119630978968373 / 100000) := by
  exact
    packedTile65536 1196290304 1196355840 13 3186 34587 30 _ _ (261281 / 12500) (2090251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196355840 :
    ThetaLowerSegment 1196355840 1196421376 (119630978968373 / 100000)
      (29909368346111 / 25000) := by
  exact
    packedTile65536 1196355840 1196421376 13 3107 34588 30 _ _ (2090253 / 100000) (130641 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196421376 :
    ThetaLowerSegment 1196421376 1196486912 (29909368346111 / 25000) (59822003767039 / 50000) := by
  exact
    packedTile65536 1196421376 1196486912 13 3126 34589 30 _ _ (2090259 / 100000) (1045131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196486912 :
    ThetaLowerSegment 1196486912 1196552448 (59822003767039 / 50000) (59825254127559 / 50000) := by
  exact
    packedTile65536 1196486912 1196552448 13 3110 34590 30 _ _ (261283 / 12500) (2090267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196552448 :
    ThetaLowerSegment 1196552448 1196617984 (59825254127559 / 50000) (59828548393079 / 50000) := by
  exact
    packedTile65536 1196552448 1196617984 13 3152 34591 30 _ _ (209027 / 10000) (2090273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196617984 :
    ThetaLowerSegment 1196617984 1196683520 (59828548393079 / 50000) (59831842666479 / 50000) := by
  exact
    packedTile65536 1196617984 1196683520 13 3152 34592 30 _ _ (83611 / 4000) (1045139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196683520 :
    ThetaLowerSegment 1196683520 1196749056 (59831842666479 / 50000) (59835113954679 / 50000) := by
  exact
    packedTile65536 1196683520 1196749056 13 3130 34593 30 _ _ (52257 / 2500) (2090283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196749056 :
    ThetaLowerSegment 1196749056 1196814592 (59835113954679 / 50000) (59838431238561 / 50000) := by
  exact
    packedTile65536 1196749056 1196814592 13 3174 34594 30 _ _ (1045143 / 50000) (2090289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196814592 :
    ThetaLowerSegment 1196814592 1196880128 (59838431238561 / 50000)
      (119683277580201 / 100000) := by
  exact
    packedTile65536 1196814592 1196880128 13 3069 34595 30 _ _ (2090291 / 100000) (1045147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196880128 :
    ThetaLowerSegment 1196880128 1196945664 (119683277580201 / 100000)
      (119689728236743 / 100000) := by
  exact
    packedTile65536 1196880128 1196945664 13 3086 34595 30 _ _ (2090297 / 100000) (20903 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1196945664 :
    ThetaLowerSegment 1196945664 1197011200 (119689728236743 / 100000)
      (119696289694721 / 100000) := by
  exact
    packedTile65536 1196945664 1197011200 13 3139 34596 30 _ _ (1045151 / 50000) (418061 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197011200 :
    ThetaLowerSegment 1197011200 1197076736 (119696289694721 / 100000)
      (119702878345537 / 100000) := by
  exact
    packedTile65536 1197011200 1197076736 13 3152 34597 30 _ _ (522577 / 25000) (2090311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197076736 :
    ThetaLowerSegment 1197076736 1197142272 (119702878345537 / 100000)
      (23941890894047 / 20000) := by
  exact
    packedTile65536 1197076736 1197142272 13 3146 34598 30 _ _ (2090313 / 100000) (522579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197142272 :
    ThetaLowerSegment 1197142272 1197207808 (23941890894047 / 20000)
      (119715959542963 / 100000) := by
  exact
    packedTile65536 1197142272 1197207808 13 3112 34599 30 _ _ (2090319 / 100000) (1045161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197207808 :
    ThetaLowerSegment 1197207808 1197273344 (119715959542963 / 100000)
      (119722619315227 / 100000) := by
  exact
    packedTile65536 1197207808 1197273344 13 3186 34600 30 _ _ (522581 / 25000) (2090327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197273344 :
    ThetaLowerSegment 1197273344 1197338880 (119722619315227 / 100000)
      (119729224758027 / 100000) := by
  exact
    packedTile65536 1197273344 1197338880 13 3160 34601 30 _ _ (209033 / 10000) (2090333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197338880 :
    ThetaLowerSegment 1197338880 1197404416 (119729224758027 / 100000)
      (119735813493947 / 100000) := by
  exact
    packedTile65536 1197338880 1197404416 13 3152 34602 30 _ _ (418067 / 20000) (1045169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197404416 :
    ThetaLowerSegment 1197404416 1197469952 (119735813493947 / 100000)
      (59871091381487 / 50000) := by
  exact
    packedTile65536 1197404416 1197469952 13 3047 34603 30 _ _ (2090341 / 100000) (261293 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197469952 :
    ThetaLowerSegment 1197469952 1197535488 (59871091381487 / 50000) (29937198631843 / 25000) := by
  exact
    packedTile65536 1197469952 1197535488 13 3163 34604 30 _ _ (1045173 / 50000) (2090349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197535488 :
    ThetaLowerSegment 1197535488 1197601024 (29937198631843 / 25000) (29938822835347 / 25000) := by
  exact
    packedTile65536 1197535488 1197601024 13 3108 34605 30 _ _ (130647 / 6250) (418071 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197601024 :
    ThetaLowerSegment 1197601024 1197666560 (29938822835347 / 25000)
      (119761882237009 / 100000) := by
  exact
    packedTile65536 1197601024 1197666560 13 3153 34606 30 _ _ (2090357 / 100000) (52259 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197666560 :
    ThetaLowerSegment 1197666560 1197732096 (119761882237009 / 100000)
      (11976854422389 / 10000) := by
  exact
    packedTile65536 1197666560 1197732096 13 3187 34607 30 _ _ (2090363 / 100000) (1045183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197732096 :
    ThetaLowerSegment 1197732096 1197797632 (11976854422389 / 10000) (11977513933493 / 10000) := by
  exact
    packedTile65536 1197732096 1197797632 13 3155 34608 30 _ _ (65324 / 3125) (2090371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197797632 :
    ThetaLowerSegment 1197797632 1197863168 (11977513933493 / 10000) (59890859916141 / 50000) := by
  exact
    packedTile65536 1197797632 1197863168 13 3148 34609 30 _ _ (1045187 / 50000) (2090377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197863168 :
    ThetaLowerSegment 1197863168 1197928704 (59890859916141 / 50000) (23957651289483 / 20000) := by
  exact
    packedTile65536 1197863168 1197928704 13 3127 34610 30 _ _ (2090379 / 100000) (1045191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197928704 :
    ThetaLowerSegment 1197928704 1197994240 (23957651289483 / 20000)
      (119794897597383 / 100000) := by
  exact
    packedTile65536 1197928704 1197994240 13 3177 34611 30 _ _ (130649 / 6250) (2090387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1197994240 :
    ThetaLowerSegment 1197994240 1198059776 (119794897597383 / 100000)
      (119801450970033 / 100000) := by
  exact
    packedTile65536 1197994240 1198059776 13 3135 34612 30 _ _ (209039 / 10000) (2090393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198059776 :
    ThetaLowerSegment 1198059776 1198125312 (119801450970033 / 100000)
      (59904006359969 / 50000) := by
  exact
    packedTile65536 1198059776 1198125312 13 3139 34613 30 _ _ (418079 / 20000) (1045199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198125312 :
    ThetaLowerSegment 1198125312 1198190848 (59904006359969 / 50000)
      (119814607935093 / 100000) := by
  exact
    packedTile65536 1198125312 1198190848 13 3155 34613 30 _ _ (2090401 / 100000) (522601 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198190848 :
    ThetaLowerSegment 1198190848 1198256384 (119814607935093 / 100000)
      (119821261697391 / 100000) := by
  exact
    packedTile65536 1198190848 1198256384 13 3183 34614 30 _ _ (1045203 / 50000) (2090409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198256384 :
    ThetaLowerSegment 1198256384 1198321920 (119821261697391 / 100000)
      (119827783782831 / 100000) := by
  exact
    packedTile65536 1198256384 1198321920 13 3120 34615 30 _ _ (522603 / 25000) (418083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198321920 :
    ThetaLowerSegment 1198321920 1198387456 (119827783782831 / 100000)
      (119834410404721 / 100000) := by
  exact
    packedTile65536 1198321920 1198387456 13 3170 34616 30 _ _ (2090417 / 100000) (104521 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198387456 :
    ThetaLowerSegment 1198387456 1198452992 (119834410404721 / 100000)
      (29960231563303 / 25000) := by
  exact
    packedTile65536 1198387456 1198452992 13 3117 34617 30 _ _ (2090423 / 100000) (1045213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198452992 :
    ThetaLowerSegment 1198452992 1198518528 (29960231563303 / 25000) (299618887501 / 250) := by
  exact
    packedTile65536 1198452992 1198518528 13 3171 34618 30 _ _ (522607 / 25000) (2090431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198518528 :
    ThetaLowerSegment 1198518528 1198584064 (299618887501 / 250) (1498175964431 / 1250) := by
  exact
    packedTile65536 1198518528 1198584064 13 3120 34619 30 _ _ (1045217 / 50000) (2090437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198584064 :
    ThetaLowerSegment 1198584064 1198649600 (1498175964431 / 1250) (59930322656909 / 50000) := by
  exact
    packedTile65536 1198584064 1198649600 13 3142 34620 30 _ _ (2090439 / 100000) (1045221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198649600 :
    ThetaLowerSegment 1198649600 1198715136 (59930322656909 / 50000)
      (119867311742923 / 100000) := by
  exact
    packedTile65536 1198649600 1198715136 13 3189 34621 30 _ _ (418089 / 20000) (130653 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198715136 :
    ThetaLowerSegment 1198715136 1198846208 (119867311742923 / 100000)
      (119880272532923 / 100000) := by
  exact
    packedTile65536 1198715136 1198846208 14 6200 34622 30 _ _ (41809 / 2000) (2090453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198846208 :
    ThetaLowerSegment 1198846208 1198911744 (119880272532923 / 100000)
      (119886874208761 / 100000) := by
  exact
    packedTile65536 1198846208 1198911744 13 3158 34624 30 _ _ (2090461 / 100000) (65327 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198911744 :
    ThetaLowerSegment 1198911744 1198977280 (119886874208761 / 100000)
      (59946713911403 / 50000) := by
  exact
    packedTile65536 1198911744 1198977280 13 3135 34625 30 _ _ (2090467 / 100000) (209047 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198977280 :
    ThetaLowerSegment 1198977280 1199042816 (59946713911403 / 50000) (59949976092959 / 50000) := by
  exact
    packedTile65536 1198977280 1199042816 13 3121 34626 30 _ _ (261309 / 12500) (83619 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199042816 :
    ThetaLowerSegment 1199042816 1199108352 (59949976092959 / 50000) (59953299951389 / 50000) := by
  exact
    packedTile65536 1199042816 1199108352 13 3180 34627 30 _ _ (2090477 / 100000) (26131 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199108352 :
    ThetaLowerSegment 1199108352 1199173888 (59953299951389 / 50000) (14989155432219 / 12500) := by
  exact
    packedTile65536 1199108352 1199173888 13 3178 34628 30 _ _ (2090483 / 100000) (1045243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199173888 :
    ThetaLowerSegment 1199173888 1199304960 (14989155432219 / 12500) (599630980607 / 500) := by
  exact
    packedTile65536 1199173888 1199304960 14 6196 34629 30 _ _ (261311 / 12500) (2090491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199304960 :
    ThetaLowerSegment 1199304960 1199370496 (599630980607 / 500) (1499157935729 / 1250) := by
  exact
    packedTile65536 1199304960 1199370496 13 3080 34630 30 _ _ (2090499 / 100000) (1045251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199370496 :
    ThetaLowerSegment 1199370496 1199436032 (1499157935729 / 1250) (5996956607393 / 5000) := by
  exact
    packedTile65536 1199370496 1199436032 13 3108 34631 30 _ _ (418101 / 20000) (522627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199436032 :
    ThetaLowerSegment 1199436032 1199501568 (5996956607393 / 5000) (11994567753467 / 10000) := by
  exact
    packedTile65536 1199436032 1199501568 13 3131 34632 30 _ _ (209051 / 10000) (2090513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199501568 :
    ThetaLowerSegment 1199501568 1199567104 (11994567753467 / 10000) (59976140737357 / 50000) := by
  exact
    packedTile65536 1199501568 1199567104 13 3159 34633 30 _ _ (522629 / 25000) (2090519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199567104 :
    ThetaLowerSegment 1199567104 1199632640 (59976140737357 / 50000)
      (119958772542419 / 100000) := by
  exact
    packedTile65536 1199567104 1199632640 13 3105 34634 30 _ _ (2090521 / 100000) (522631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199632640 :
    ThetaLowerSegment 1199632640 1199698176 (119958772542419 / 100000)
      (119965466409873 / 100000) := by
  exact
    packedTile65536 1199632640 1199698176 13 3202 34635 30 _ _ (2090527 / 100000) (209053 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199698176 :
    ThetaLowerSegment 1199698176 1199763712 (119965466409873 / 100000)
      (119971882252581 / 100000) := by
  exact
    packedTile65536 1199698176 1199763712 13 3069 34636 30 _ _ (522633 / 25000) (418107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199763712 :
    ThetaLowerSegment 1199763712 1199829248 (119971882252581 / 100000)
      (119978496714813 / 100000) := by
  exact
    packedTile65536 1199763712 1199829248 13 3164 34637 30 _ _ (1045269 / 50000) (2090541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199829248 :
    ThetaLowerSegment 1199829248 1199894784 (119978496714813 / 100000)
      (29996246962707 / 25000) := by
  exact
    packedTile65536 1199829248 1199894784 13 3105 34638 30 _ _ (2090543 / 100000) (1045273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199894784 :
    ThetaLowerSegment 1199894784 1199960320 (29996246962707 / 25000) (7499476322477 / 6250) := by
  exact
    packedTile65536 1199894784 1199960320 13 3173 34639 30 _ _ (522637 / 25000) (2090551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1199960320 :
    ThetaLowerSegment 1199960320 1200025856 (7499476322477 / 6250) (29999532786197 / 25000) := by
  exact
    packedTile65536 1199960320 1200025856 13 3114 34640 30 _ _ (1045277 / 50000) (2090557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200025856 :
    ThetaLowerSegment 1200025856 1200091392 (29999532786197 / 25000) (60002308029403 / 50000) := by
  exact
    packedTile65536 1200025856 1200091392 13 3102 34641 30 _ _ (2090559 / 100000) (1045281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200091392 :
    ThetaLowerSegment 1200091392 1200156928 (60002308029403 / 50000) (60005548405153 / 50000) := by
  exact
    packedTile65536 1200091392 1200156928 13 3100 34642 30 _ _ (418113 / 20000) (261321 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200156928 :
    ThetaLowerSegment 1200156928 1200222464 (60005548405153 / 50000) (30004399098109 / 25000) := by
  exact
    packedTile65536 1200156928 1200222464 13 3109 34643 30 _ _ (209057 / 10000) (2090573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200222464 :
    ThetaLowerSegment 1200222464 1200288000 (30004399098109 / 25000) (30006028179457 / 25000) := by
  exact
    packedTile65536 1200222464 1200288000 13 3117 34644 30 _ _ (130661 / 6250) (2090579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200288000 :
    ThetaLowerSegment 1200288000 1200353536 (30006028179457 / 25000)
      (120030633239967 / 100000) := by
  exact
    packedTile65536 1200288000 1200353536 13 3119 34645 30 _ _ (2090581 / 100000) (261323 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200353536 :
    ThetaLowerSegment 1200353536 1200419072 (120030633239967 / 100000)
      (120037201864321 / 100000) := by
  exact
    packedTile65536 1200353536 1200419072 13 3142 34646 30 _ _ (2090587 / 100000) (209059 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200419072 :
    ThetaLowerSegment 1200419072 1200484608 (120037201864321 / 100000)
      (120043653431233 / 100000) := by
  exact
    packedTile65536 1200419072 1200484608 13 3086 34647 30 _ _ (65331 / 3125) (418119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200484608 :
    ThetaLowerSegment 1200484608 1200550144 (120043653431233 / 100000)
      (120050224180747 / 100000) := by
  exact
    packedTile65536 1200484608 1200550144 13 3143 34648 30 _ _ (1045299 / 50000) (2090601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200550144 :
    ThetaLowerSegment 1200550144 1200615680 (120050224180747 / 100000)
      (30014179921067 / 25000) := by
  exact
    packedTile65536 1200550144 1200615680 13 3107 34648 30 _ _ (2090603 / 100000) (1045303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200615680 :
    ThetaLowerSegment 1200615680 1200681216 (30014179921067 / 25000) (12006332182749 / 10000) := by
  exact
    packedTile65536 1200615680 1200681216 13 3158 34649 30 _ _ (2090609 / 100000) (522653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200681216 :
    ThetaLowerSegment 1200681216 1200746752 (12006332182749 / 10000) (60034886731147 / 50000) := by
  exact
    packedTile65536 1200681216 1200746752 13 3086 34650 30 _ _ (1045307 / 50000) (2090617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200746752 :
    ThetaLowerSegment 1200746752 1200812288 (60034886731147 / 50000)
      (120076373546477 / 100000) := by
  exact
    packedTile65536 1200746752 1200812288 13 3157 34651 30 _ _ (2090619 / 100000) (1045311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200812288 :
    ThetaLowerSegment 1200812288 1200877824 (120076373546477 / 100000)
      (60041516093551 / 50000) := by
  exact
    packedTile65536 1200812288 1200877824 13 3185 34652 30 _ _ (669 / 32) (522657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200877824 :
    ThetaLowerSegment 1200877824 1200943360 (60041516093551 / 50000) (30022418529653 / 25000) := by
  exact
    packedTile65536 1200877824 1200943360 13 3177 34653 30 _ _ (209063 / 10000) (2090633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1200943360 :
    ThetaLowerSegment 1200943360 1201008896 (30022418529653 / 25000) (15012032714081 / 12500) := by
  exact
    packedTile65536 1200943360 1201008896 13 3151 34654 30 _ _ (522659 / 25000) (2090639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201008896 :
    ThetaLowerSegment 1201008896 1201074432 (15012032714081 / 12500) (60051377621797 / 50000) := by
  exact
    packedTile65536 1201008896 1201074432 13 3106 34655 30 _ _ (2090641 / 100000) (522661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201074432 :
    ThetaLowerSegment 1201074432 1201139968 (60051377621797 / 50000)
      (120109313603233 / 100000) := by
  exact
    packedTile65536 1201074432 1201139968 13 3137 34656 30 _ _ (2090647 / 100000) (41813 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201139968 :
    ThetaLowerSegment 1201139968 1201205504 (120109313603233 / 100000)
      (120115892885077 / 100000) := by
  exact
    packedTile65536 1201139968 1201205504 13 3147 34657 30 _ _ (522663 / 25000) (418131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201205504 :
    ThetaLowerSegment 1201205504 1201271040 (120115892885077 / 100000)
      (120122482639093 / 100000) := by
  exact
    packedTile65536 1201205504 1201271040 13 3152 34658 30 _ _ (1045329 / 50000) (2090661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201271040 :
    ThetaLowerSegment 1201271040 1201336576 (120122482639093 / 100000)
      (60064551884407 / 50000) := by
  exact
    packedTile65536 1201271040 1201336576 13 3167 34659 30 _ _ (2090663 / 100000) (1045333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201336576 :
    ThetaLowerSegment 1201336576 1201402112 (60064551884407 / 50000) (24027137457099 / 20000) := by
  exact
    packedTile65536 1201336576 1201402112 13 3149 34660 30 _ _ (2090669 / 100000) (130667 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201402112 :
    ThetaLowerSegment 1201402112 1201467648 (24027137457099 / 20000)
      (120142281271291 / 100000) := by
  exact
    packedTile65536 1201402112 1201467648 13 3154 34661 30 _ _ (1045337 / 50000) (2090677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201467648 :
    ThetaLowerSegment 1201467648 1201533184 (120142281271291 / 100000)
      (12014872265329 / 10000) := by
  exact
    packedTile65536 1201467648 1201533184 13 3081 34662 30 _ _ (2090679 / 100000) (1045341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201533184 :
    ThetaLowerSegment 1201533184 1201598720 (12014872265329 / 10000) (24031064589167 / 20000) := by
  exact
    packedTile65536 1201533184 1201598720 13 3157 34663 30 _ _ (418137 / 20000) (65334 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201598720 :
    ThetaLowerSegment 1201598720 1201664256 (24031064589167 / 20000) (4806473083297 / 4000) := by
  exact
    packedTile65536 1201598720 1201664256 13 3111 34664 30 _ _ (209069 / 10000) (2090693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201664256 :
    ThetaLowerSegment 1201664256 1201729792 (4806473083297 / 4000) (120168316602809 / 100000) := by
  exact
    packedTile65536 1201664256 1201729792 13 3104 34665 30 _ _ (261337 / 12500) (2090699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201729792 :
    ThetaLowerSegment 1201729792 1201795328 (120168316602809 / 100000)
      (120174931580773 / 100000) := by
  exact
    packedTile65536 1201729792 1201795328 13 3164 34665 30 _ _ (2090701 / 100000) (130669 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201795328 :
    ThetaLowerSegment 1201795328 1201860864 (120174931580773 / 100000)
      (15022677903251 / 12500) := by
  exact
    packedTile65536 1201795328 1201860864 13 3105 34666 30 _ _ (2090707 / 100000) (209071 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201860864 :
    ThetaLowerSegment 1201860864 1201926400 (15022677903251 / 12500) (3755876129627 / 3125) := by
  exact
    packedTile65536 1201860864 1201926400 13 3163 34667 30 _ _ (261339 / 12500) (418143 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201926400 :
    ThetaLowerSegment 1201926400 1201991936 (3755876129627 / 3125) (6009723987047 / 5000) := by
  exact
    packedTile65536 1201926400 1201991936 13 3082 34668 30 _ _ (1045359 / 50000) (2090721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1201991936 :
    ThetaLowerSegment 1201991936 1202057472 (6009723987047 / 5000) (120200921258503 / 100000) := by
  exact
    packedTile65536 1201991936 1202057472 13 3081 34669 30 _ _ (2090723 / 100000) (1045363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202057472 :
    ThetaLowerSegment 1202057472 1202123008 (120200921258503 / 100000)
      (60103700213837 / 50000) := by
  exact
    packedTile65536 1202057472 1202123008 13 3099 34670 30 _ _ (2090729 / 100000) (522683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202123008 :
    ThetaLowerSegment 1202123008 1202188544 (60103700213837 / 50000) (6010693980617 / 5000) := by
  exact
    packedTile65536 1202123008 1202188544 13 3099 34671 30 _ _ (1045367 / 50000) (2090737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202188544 :
    ThetaLowerSegment 1202188544 1202254080 (6010693980617 / 5000) (60110282897831 / 50000) := by
  exact
    packedTile65536 1202188544 1202254080 13 3198 34672 30 _ _ (2090739 / 100000) (1045371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202254080 :
    ThetaLowerSegment 1202254080 1202319616 (60110282897831 / 50000) (60113494282151 / 50000) := by
  exact
    packedTile65536 1202254080 1202319616 13 3072 34673 30 _ _ (418149 / 20000) (522687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202319616 :
    ThetaLowerSegment 1202319616 1202385152 (60113494282151 / 50000) (60116734944651 / 50000) := by
  exact
    packedTile65536 1202319616 1202385152 13 3100 34674 30 _ _ (8363 / 400) (2090753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202385152 :
    ThetaLowerSegment 1202385152 1202450688 (60116734944651 / 50000) (12024003068163 / 10000) := by
  exact
    packedTile65536 1202385152 1202450688 13 3138 34675 30 _ _ (522689 / 25000) (2090759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202450688 :
    ThetaLowerSegment 1202450688 1202516224 (12024003068163 / 10000) (60123322924717 / 50000) := by
  exact
    packedTile65536 1202450688 1202516224 13 3164 34676 30 _ _ (2090761 / 100000) (522691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202516224 :
    ThetaLowerSegment 1202516224 1202581760 (60123322924717 / 50000) (15031638289933 / 12500) := by
  exact
    packedTile65536 1202516224 1202581760 13 3090 34677 30 _ _ (2090767 / 100000) (209077 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202581760 :
    ThetaLowerSegment 1202581760 1202647296 (15031638289933 / 12500) (30064934039369 / 25000) := by
  exact
    packedTile65536 1202581760 1202647296 13 3171 34678 30 _ _ (522693 / 25000) (83631 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202647296 :
    ThetaLowerSegment 1202647296 1202712832 (30064934039369 / 25000) (30066602480213 / 25000) := by
  exact
    packedTile65536 1202647296 1202712832 13 3192 34679 30 _ _ (1045389 / 50000) (2090781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202712832 :
    ThetaLowerSegment 1202712832 1202778368 (30066602480213 / 25000) (15034107236953 / 12500) := by
  exact
    packedTile65536 1202712832 1202778368 13 3084 34680 30 _ _ (2090783 / 100000) (1045393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202778368 :
    ThetaLowerSegment 1202778368 1202843904 (15034107236953 / 12500) (15034935189397 / 12500) := by
  exact
    packedTile65536 1202778368 1202843904 13 3168 34681 30 _ _ (2090789 / 100000) (261349 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202843904 :
    ThetaLowerSegment 1202843904 1202909440 (15034935189397 / 12500) (60143005532419 / 50000) := by
  exact
    packedTile65536 1202843904 1202909440 13 3123 34682 30 _ _ (1045397 / 50000) (2090797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202909440 :
    ThetaLowerSegment 1202909440 1202974976 (60143005532419 / 50000) (24058512307621 / 20000) := by
  exact
    packedTile65536 1202909440 1202974976 13 3133 34682 30 _ _ (2090799 / 100000) (1045401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202974976 :
    ThetaLowerSegment 1202974976 1203040512 (24058512307621 / 20000) (12029912875661 / 10000) := by
  exact
    packedTile65536 1202974976 1203040512 13 3141 34683 30 _ _ (418161 / 20000) (261351 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203040512 :
    ThetaLowerSegment 1203040512 1203106048 (12029912875661 / 10000) (2406113627103 / 2000) := by
  exact
    packedTile65536 1203040512 1203106048 13 3134 34684 30 _ _ (209081 / 10000) (2090813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203106048 :
    ThetaLowerSegment 1203106048 1203171584 (2406113627103 / 2000) (60156114895431 / 50000) := by
  exact
    packedTile65536 1203106048 1203171584 13 3132 34685 30 _ _ (65338 / 3125) (2090819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203171584 :
    ThetaLowerSegment 1203171584 1203237120 (60156114895431 / 50000) (3007969769679 / 2500) := by
  exact
    packedTile65536 1203171584 1203237120 13 3138 34686 30 _ _ (2090821 / 100000) (261353 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203237120 :
    ThetaLowerSegment 1203237120 1203302656 (3007969769679 / 2500) (30081305542753 / 25000) := by
  exact
    packedTile65536 1203237120 1203302656 13 3076 34687 30 _ _ (2090827 / 100000) (209083 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203302656 :
    ThetaLowerSegment 1203302656 1203368192 (30081305542753 / 25000) (30082924369429 / 25000) := by
  exact
    packedTile65536 1203302656 1203368192 13 3097 34688 30 _ _ (130677 / 6250) (418167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203368192 :
    ThetaLowerSegment 1203368192 1203433728 (30082924369429 / 25000) (60169147035803 / 50000) := by
  exact
    packedTile65536 1203368192 1203433728 13 3155 34689 30 _ _ (1045419 / 50000) (2090841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203433728 :
    ThetaLowerSegment 1203433728 1203499264 (60169147035803 / 50000)
      (120344723413831 / 100000) := by
  exact
    packedTile65536 1203433728 1203499264 13 3075 34690 30 _ _ (2090843 / 100000) (1045423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203499264 :
    ThetaLowerSegment 1203499264 1203564800 (120344723413831 / 100000)
      (120351267768071 / 100000) := by
  exact
    packedTile65536 1203499264 1203564800 13 3130 34691 30 _ _ (65339 / 3125) (2090851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203564800 :
    ThetaLowerSegment 1203564800 1203630336 (120351267768071 / 100000)
      (120357801686821 / 100000) := by
  exact
    packedTile65536 1203564800 1203630336 13 3125 34692 30 _ _ (1045427 / 50000) (2090857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203630336 :
    ThetaLowerSegment 1203630336 1203695872 (120357801686821 / 100000)
      (30091100632171 / 25000) := by
  exact
    packedTile65536 1203630336 1203695872 13 3157 34693 30 _ _ (2090859 / 100000) (1045431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203695872 :
    ThetaLowerSegment 1203695872 1203761408 (30091100632171 / 25000) (60185515285367 / 50000) := by
  exact
    packedTile65536 1203695872 1203761408 13 3170 34694 30 _ _ (418173 / 20000) (522717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203761408 :
    ThetaLowerSegment 1203761408 1203826944 (60185515285367 / 50000) (60188781224307 / 50000) := by
  exact
    packedTile65536 1203761408 1203826944 13 3124 34695 30 _ _ (209087 / 10000) (2090873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203826944 :
    ThetaLowerSegment 1203826944 1203892480 (60188781224307 / 50000) (60192058672437 / 50000) := by
  exact
    packedTile65536 1203826944 1203892480 13 3135 34696 30 _ _ (522719 / 25000) (2090879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203892480 :
    ThetaLowerSegment 1203892480 1203958016 (60192058672437 / 50000) (60195282810939 / 50000) := by
  exact
    packedTile65536 1203892480 1203958016 13 3084 34697 30 _ _ (2090881 / 100000) (522721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1203958016 :
    ThetaLowerSegment 1203958016 1204023552 (60195282810939 / 50000)
      (120397003462951 / 100000) := by
  exact
    packedTile65536 1203958016 1204023552 13 3079 34698 30 _ _ (2090887 / 100000) (209089 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204023552 :
    ThetaLowerSegment 1204023552 1204089088 (120397003462951 / 100000)
      (120403453864771 / 100000) := by
  exact
    packedTile65536 1204023552 1204089088 13 3085 34699 30 _ _ (522723 / 25000) (418179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204089088 :
    ThetaLowerSegment 1204089088 1204154624 (120403453864771 / 100000)
      (120409973281617 / 100000) := by
  exact
    packedTile65536 1204089088 1204154624 13 3118 34699 30 _ _ (2090897 / 100000) (20909 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204154624 :
    ThetaLowerSegment 1204154624 1204220160 (120409973281617 / 100000)
      (30104151929209 / 25000) := by
  exact
    packedTile65536 1204154624 1204220160 13 3173 34700 30 _ _ (2090903 / 100000) (1045453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204220160 :
    ThetaLowerSegment 1204220160 1204285696 (30104151929209 / 25000) (15052882793729 / 12500) := by
  exact
    packedTile65536 1204220160 1204285696 13 3087 34701 30 _ _ (522727 / 25000) (2090911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204285696 :
    ThetaLowerSegment 1204285696 1204351232 (15052882793729 / 12500) (60214819137181 / 50000) := by
  exact
    packedTile65536 1204285696 1204351232 13 3145 34702 30 _ _ (1045457 / 50000) (2090917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204351232 :
    ThetaLowerSegment 1204351232 1204416768 (60214819137181 / 50000) (30109085440169 / 25000) := by
  exact
    packedTile65536 1204351232 1204416768 13 3206 34703 30 _ _ (2090919 / 100000) (1045461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204416768 :
    ThetaLowerSegment 1204416768 1204482304 (30109085440169 / 25000)
      (120442988811251 / 100000) := by
  exact
    packedTile65536 1204416768 1204482304 13 3179 34704 30 _ _ (83637 / 4000) (130683 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204482304 :
    ThetaLowerSegment 1204482304 1204547840 (120442988811251 / 100000)
      (120449617059351 / 100000) := by
  exact
    packedTile65536 1204482304 1204547840 13 3170 34705 30 _ _ (209093 / 10000) (2090933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204547840 :
    ThetaLowerSegment 1204547840 1204613376 (120449617059351 / 100000)
      (24091198464643 / 20000) := by
  exact
    packedTile65536 1204547840 1204613376 13 3049 34706 30 _ _ (261367 / 12500) (2090939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204613376 :
    ThetaLowerSegment 1204613376 1204678912 (24091198464643 / 20000) (60231286257271 / 50000) := by
  exact
    packedTile65536 1204613376 1204678912 13 3147 34707 30 _ _ (2090941 / 100000) (65342 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204678912 :
    ThetaLowerSegment 1204678912 1204744448 (60231286257271 / 50000) (602346035431 / 500) := by
  exact
    packedTile65536 1204678912 1204744448 13 3173 34708 30 _ _ (1045473 / 50000) (2090949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204744448 :
    ThetaLowerSegment 1204744448 1204809984 (602346035431 / 500) (15059485175623 / 12500) := by
  exact
    packedTile65536 1204744448 1204809984 13 3192 34709 30 _ _ (261369 / 12500) (418191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204809984 :
    ThetaLowerSegment 1204809984 1204875520 (15059485175623 / 12500) (6024114823053 / 5000) := by
  exact
    packedTile65536 1204809984 1204875520 13 3068 34710 30 _ _ (2090957 / 100000) (26137 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204875520 :
    ThetaLowerSegment 1204875520 1204941056 (6024114823053 / 5000) (12048879935599 / 10000) := by
  exact
    packedTile65536 1204875520 1204941056 13 3110 34711 30 _ _ (2090963 / 100000) (1045483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1204941056 :
    ThetaLowerSegment 1204941056 1205006592 (12048879935599 / 10000) (60247674133883 / 50000) := by
  exact
    packedTile65536 1204941056 1205006592 13 3132 34712 30 _ _ (261371 / 12500) (2090971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205006592 :
    ThetaLowerSegment 1205006592 1205072128 (60247674133883 / 50000) (60250956963063 / 50000) := by
  exact
    packedTile65536 1205006592 1205072128 13 3140 34713 30 _ _ (1045487 / 50000) (2090977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205072128 :
    ThetaLowerSegment 1205072128 1205137664 (60250956963063 / 50000)
      (120508498418997 / 100000) := by
  exact
    packedTile65536 1205072128 1205137664 13 3149 34714 30 _ _ (2090979 / 100000) (1045491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205137664 :
    ThetaLowerSegment 1205137664 1205203200 (120508498418997 / 100000)
      (120514938649717 / 100000) := by
  exact
    packedTile65536 1205137664 1205203200 13 3080 34715 30 _ _ (261373 / 12500) (2090987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205203200 :
    ThetaLowerSegment 1205203200 1205268736 (120514938649717 / 100000)
      (120521625635737 / 100000) := by
  exact
    packedTile65536 1205203200 1205268736 13 3198 34716 30 _ _ (209099 / 10000) (2090993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205268736 :
    ThetaLowerSegment 1205268736 1205334272 (120521625635737 / 100000)
      (120528191360037 / 100000) := by
  exact
    packedTile65536 1205268736 1205334272 13 3140 34716 30 _ _ (418199 / 20000) (1045499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205334272 :
    ThetaLowerSegment 1205334272 1205399808 (120528191360037 / 100000)
      (60267354505077 / 50000) := by
  exact
    packedTile65536 1205334272 1205399808 13 3117 34717 30 _ _ (2091001 / 100000) (522751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205399808 :
    ThetaLowerSegment 1205399808 1205465344 (60267354505077 / 50000) (12054128731503 / 10000) := by
  exact
    packedTile65536 1205399808 1205465344 13 3146 34718 30 _ _ (1045503 / 50000) (2091009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205465344 :
    ThetaLowerSegment 1205465344 1205530880 (12054128731503 / 10000) (60273920273319 / 50000) := by
  exact
    packedTile65536 1205465344 1205530880 13 3134 34719 30 _ _ (522753 / 25000) (418203 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205530880 :
    ThetaLowerSegment 1205530880 1205596416 (60273920273319 / 50000) (3767331340488 / 3125) := by
  exact
    packedTile65536 1205530880 1205596416 13 3234 34720 30 _ _ (2091017 / 100000) (104551 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205596416 :
    ThetaLowerSegment 1205596416 1205661952 (3767331340488 / 3125) (3767536260742 / 3125) := by
  exact
    packedTile65536 1205596416 1205661952 13 3136 34721 30 _ _ (2091023 / 100000) (1045513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205661952 :
    ThetaLowerSegment 1205661952 1205727488 (3767536260742 / 3125) (3767740135972 / 3125) := by
  exact
    packedTile65536 1205661952 1205727488 13 3120 34722 30 _ _ (522757 / 25000) (2091031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205727488 :
    ThetaLowerSegment 1205727488 1205793024 (3767740135972 / 3125) (120574352655341 / 100000) := by
  exact
    packedTile65536 1205727488 1205793024 13 3189 34723 30 _ _ (2091033 / 100000) (522759 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205793024 :
    ThetaLowerSegment 1205793024 1205858560 (120574352655341 / 100000) (4823229714821 / 4000) := by
  exact
    packedTile65536 1205793024 1205858560 13 3056 34724 30 _ _ (2091039 / 100000) (1045521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205858560 :
    ThetaLowerSegment 1205858560 1205924096 (4823229714821 / 4000) (120587363115829 / 100000) := by
  exact
    packedTile65536 1205858560 1205924096 13 3166 34725 30 _ _ (522761 / 25000) (2091047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205924096 :
    ThetaLowerSegment 1205924096 1205989632 (120587363115829 / 100000)
      (120593887191829 / 100000) := by
  exact
    packedTile65536 1205924096 1205989632 13 3120 34726 30 _ _ (41821 / 2000) (2091053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1205989632 :
    ThetaLowerSegment 1205989632 1206055168 (120593887191829 / 100000)
      (120600361098109 / 100000) := by
  exact
    packedTile65536 1205989632 1206055168 13 3096 34727 30 _ _ (418211 / 20000) (1045529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206055168 :
    ThetaLowerSegment 1206055168 1206120704 (120600361098109 / 100000)
      (120606964668747 / 100000) := by
  exact
    packedTile65536 1206055168 1206120704 13 3158 34728 30 _ _ (2091061 / 100000) (261383 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206120704 :
    ThetaLowerSegment 1206120704 1206186240 (120606964668747 / 100000)
      (120613624713957 / 100000) := by
  exact
    packedTile65536 1206120704 1206186240 13 3185 34729 30 _ _ (1045533 / 50000) (2091069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206186240 :
    ThetaLowerSegment 1206186240 1206251776 (120613624713957 / 100000)
      (120620098669773 / 100000) := by
  exact
    packedTile65536 1206186240 1206251776 13 3096 34730 30 _ _ (2091071 / 100000) (1045537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206251776 :
    ThetaLowerSegment 1206251776 1206317312 (120620098669773 / 100000) (1507832550129 / 1250) := by
  exact
    packedTile65536 1206251776 1206317312 13 3111 34731 30 _ _ (2091077 / 100000) (52277 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206317312 :
    ThetaLowerSegment 1206317312 1206382848 (1507832550129 / 1250) (30158295638573 / 25000) := by
  exact
    packedTile65536 1206317312 1206382848 13 3146 34732 30 _ _ (1045541 / 50000) (418217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206382848 :
    ThetaLowerSegment 1206382848 1206448384 (30158295638573 / 25000) (30159925641669 / 25000) := by
  exact
    packedTile65536 1206382848 1206448384 13 3118 34733 30 _ _ (130693 / 6250) (2091091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206448384 :
    ThetaLowerSegment 1206448384 1206513920 (30159925641669 / 25000)
      (120646245596673 / 100000) := by
  exact
    packedTile65536 1206448384 1206513920 13 3129 34733 30 _ _ (2091093 / 100000) (261387 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206513920 :
    ThetaLowerSegment 1206513920 1206579456 (120646245596673 / 100000)
      (60326404778217 / 50000) := by
  exact
    packedTile65536 1206513920 1206579456 13 3139 34734 30 _ _ (2091099 / 100000) (1045551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206579456 :
    ThetaLowerSegment 1206579456 1206644992 (60326404778217 / 50000) (60329659581593 / 50000) := by
  exact
    packedTile65536 1206579456 1206644992 13 3113 34735 30 _ _ (65347 / 3125) (2091107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206644992 :
    ThetaLowerSegment 1206644992 1206710528 (60329659581593 / 50000)
      (120665958434261 / 100000) := by
  exact
    packedTile65536 1206644992 1206710528 13 3175 34736 30 _ _ (2091109 / 100000) (261389 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206710528 :
    ThetaLowerSegment 1206710528 1206776064 (120665958434261 / 100000) (3771016195688 / 3125) := by
  exact
    packedTile65536 1206710528 1206776064 13 3137 34737 30 _ _ (418223 / 20000) (1045559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206776064 :
    ThetaLowerSegment 1206776064 1206841600 (3771016195688 / 3125) (7542443949931 / 6250) := by
  exact
    packedTile65536 1206776064 1206841600 13 3149 34738 30 _ _ (26139 / 1250) (2091123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206841600 :
    ThetaLowerSegment 1206841600 1206907136 (7542443949931 / 6250) (12068568815467 / 10000) := by
  exact
    packedTile65536 1206841600 1206907136 13 3149 34739 30 _ _ (1045563 / 50000) (2091129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206907136 :
    ThetaLowerSegment 1206907136 1206972672 (12068568815467 / 10000) (3017306880433 / 2500) := by
  exact
    packedTile65536 1206907136 1206972672 13 3150 34740 30 _ _ (2091131 / 100000) (1045567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206972672 :
    ThetaLowerSegment 1206972672 1207038208 (3017306880433 / 2500) (12069886229887 / 10000) := by
  exact
    packedTile65536 1206972672 1207038208 13 3150 34741 30 _ _ (2091137 / 100000) (104557 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207038208 :
    ThetaLowerSegment 1207038208 1207103744 (12069886229887 / 10000) (15088180390343 / 12500) := by
  exact
    packedTile65536 1207038208 1207103744 13 3147 34742 30 _ _ (1045571 / 50000) (418229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207103744 :
    ThetaLowerSegment 1207103744 1207169280 (15088180390343 / 12500)
      (120711957045649 / 100000) := by
  exact
    packedTile65536 1207103744 1207169280 13 3115 34743 30 _ _ (2091147 / 100000) (41823 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207169280 :
    ThetaLowerSegment 1207169280 1207234816 (120711957045649 / 100000)
      (60359254313999 / 50000) := by
  exact
    packedTile65536 1207169280 1207234816 13 3133 34744 30 _ _ (2091153 / 100000) (522789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207234816 :
    ThetaLowerSegment 1207234816 1207300352 (60359254313999 / 50000) (30181271329977 / 25000) := by
  exact
    packedTile65536 1207234816 1207300352 13 3145 34745 30 _ _ (1045579 / 50000) (2091161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207300352 :
    ThetaLowerSegment 1207300352 1207365888 (30181271329977 / 25000) (30182895118823 / 25000) := by
  exact
    packedTile65536 1207300352 1207365888 13 3106 34746 30 _ _ (522791 / 25000) (2091167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207365888 :
    ThetaLowerSegment 1207365888 1207431424 (30182895118823 / 25000)
      (120738261760247 / 100000) := by
  exact
    packedTile65536 1207365888 1207431424 13 3195 34747 30 _ _ (2091169 / 100000) (522793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207431424 :
    ThetaLowerSegment 1207431424 1207496960 (120738261760247 / 100000)
      (60372473623361 / 50000) := by
  exact
    packedTile65536 1207431424 1207496960 13 3197 34748 30 _ _ (83647 / 4000) (1045589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207496960 :
    ThetaLowerSegment 1207496960 1207562496 (60372473623361 / 50000) (60375724362671 / 50000) := by
  exact
    packedTile65536 1207496960 1207562496 13 3109 34749 30 _ _ (104559 / 5000) (2091183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207562496 :
    ThetaLowerSegment 1207562496 1207628032 (60375724362671 / 50000) (30189492260043 / 25000) := by
  exact
    packedTile65536 1207562496 1207628032 13 3118 34749 30 _ _ (418237 / 20000) (522797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207628032 :
    ThetaLowerSegment 1207628032 1207693568 (30189492260043 / 25000)
      (120764554200631 / 100000) := by
  exact
    packedTile65536 1207628032 1207693568 13 3149 34750 30 _ _ (2091191 / 100000) (1045597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207693568 :
    ThetaLowerSegment 1207693568 1207759104 (120764554200631 / 100000)
      (120771114282483 / 100000) := by
  exact
    packedTile65536 1207693568 1207759104 13 3137 34751 30 _ _ (522799 / 25000) (2091199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207759104 :
    ThetaLowerSegment 1207759104 1207824640 (120771114282483 / 100000)
      (24155524002381 / 20000) := by
  exact
    packedTile65536 1207759104 1207824640 13 3111 34752 30 _ _ (1045601 / 50000) (418241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207824640 :
    ThetaLowerSegment 1207824640 1207890176 (24155524002381 / 20000) (60392075425683 / 50000) := by
  exact
    packedTile65536 1207824640 1207890176 13 3123 34753 30 _ _ (2091207 / 100000) (209121 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207890176 :
    ThetaLowerSegment 1207890176 1207955712 (60392075425683 / 50000) (12079069216563 / 10000) := by
  exact
    packedTile65536 1207890176 1207955712 13 3128 34754 30 _ _ (2091213 / 100000) (130701 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1207955712 :
    ThetaLowerSegment 1207955712 1208021248 (12079069216563 / 10000) (60398572832189 / 50000) := by
  exact
    packedTile65536 1207955712 1208021248 13 3086 34755 30 _ _ (1045609 / 50000) (2091221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208021248 :
    ThetaLowerSegment 1208021248 1208086784 (60398572832189 / 50000) (3020093534543 / 2500) := by
  exact
    packedTile65536 1208021248 1208086784 13 3154 34756 30 _ _ (2091223 / 100000) (1045613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208086784 :
    ThetaLowerSegment 1208086784 1208152320 (3020093534543 / 2500) (24162059476927 / 20000) := by
  exact
    packedTile65536 1208086784 1208152320 13 3135 34757 30 _ _ (2091229 / 100000) (65351 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208152320 :
    ThetaLowerSegment 1208152320 1208217856 (24162059476927 / 20000) (24163364406943 / 20000) := by
  exact
    packedTile65536 1208152320 1208217856 13 3120 34758 30 _ _ (1045617 / 50000) (2091237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208217856 :
    ThetaLowerSegment 1208217856 1208283392 (24163364406943 / 20000) (24164695272079 / 20000) := by
  exact
    packedTile65536 1208217856 1208283392 13 3182 34759 30 _ _ (52281 / 2500) (2091243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208283392 :
    ThetaLowerSegment 1208283392 1208348928 (24164695272079 / 20000) (6041505594039 / 5000) := by
  exact
    packedTile65536 1208283392 1208348928 13 3173 34760 30 _ _ (418249 / 20000) (130703 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208348928 :
    ThetaLowerSegment 1208348928 1208414464 (6041505594039 / 5000) (120836559207613 / 100000) := by
  exact
    packedTile65536 1208348928 1208414464 13 3083 34761 30 _ _ (2091251 / 100000) (1045627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208414464 :
    ThetaLowerSegment 1208414464 1208480000 (120836559207613 / 100000)
      (120843190580389 / 100000) := by
  exact
    packedTile65536 1208414464 1208480000 13 3171 34762 30 _ _ (261407 / 12500) (2091259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208480000 :
    ThetaLowerSegment 1208480000 1208545536 (120843190580389 / 100000)
      (60424867068029 / 50000) := by
  exact
    packedTile65536 1208480000 1208545536 13 3129 34763 30 _ _ (2091261 / 100000) (65352 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208545536 :
    ThetaLowerSegment 1208545536 1208611072 (60424867068029 / 50000) (60428121079481 / 50000) := by
  exact
    packedTile65536 1208545536 1208611072 13 3112 34764 30 _ _ (2091267 / 100000) (209127 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208611072 :
    ThetaLowerSegment 1208611072 1208676608 (60428121079481 / 50000) (12086274392361 / 10000) := by
  exact
    packedTile65536 1208611072 1208676608 13 3109 34765 30 _ _ (261409 / 12500) (83651 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208676608 :
    ThetaLowerSegment 1208676608 1208742144 (12086274392361 / 10000) (60434659450821 / 50000) := by
  exact
    packedTile65536 1208676608 1208742144 13 3144 34766 30 _ _ (1045639 / 50000) (2091281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208742144 :
    ThetaLowerSegment 1208742144 1208807680 (60434659450821 / 50000) (30218968245641 / 25000) := by
  exact
    packedTile65536 1208742144 1208807680 13 3134 34766 30 _ _ (2091283 / 100000) (1045643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208807680 :
    ThetaLowerSegment 1208807680 1208873216 (30218968245641 / 25000) (15110292406019 / 12500) := by
  exact
    packedTile65536 1208807680 1208873216 13 3092 34767 30 _ _ (2091289 / 100000) (522823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208873216 :
    ThetaLowerSegment 1208873216 1208938752 (15110292406019 / 12500) (15111112193267 / 12500) := by
  exact
    packedTile65536 1208873216 1208938752 13 3136 34768 30 _ _ (1045647 / 50000) (2091297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1208938752 :
    ThetaLowerSegment 1208938752 1209004288 (15111112193267 / 12500)
      (120895512324873 / 100000) := by
  exact
    packedTile65536 1208938752 1209004288 13 3163 34769 30 _ _ (2091299 / 100000) (1045651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209004288 :
    ThetaLowerSegment 1209004288 1209069824 (120895512324873 / 100000)
      (60451061469989 / 50000) := by
  exact
    packedTile65536 1209004288 1209069824 13 3161 34770 30 _ _ (418261 / 20000) (522827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209069824 :
    ThetaLowerSegment 1209069824 1209135360 (60451061469989 / 50000) (30227169799207 / 25000) := by
  exact
    packedTile65536 1209069824 1209135360 13 3135 34771 30 _ _ (209131 / 10000) (2091313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209135360 :
    ThetaLowerSegment 1209135360 1209200896 (30227169799207 / 25000) (15114399205771 / 12500) := by
  exact
    packedTile65536 1209135360 1209200896 13 3115 34772 30 _ _ (522829 / 25000) (2091319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209200896 :
    ThetaLowerSegment 1209200896 1209266432 (15114399205771 / 12500)
      (120921716476367 / 100000) := by
  exact
    packedTile65536 1209200896 1209266432 13 3119 34773 30 _ _ (2091321 / 100000) (522831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209266432 :
    ThetaLowerSegment 1209266432 1209331968 (120921716476367 / 100000)
      (120928224682879 / 100000) := by
  exact
    packedTile65536 1209266432 1209331968 13 3112 34774 30 _ _ (1045663 / 50000) (2091329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209331968 :
    ThetaLowerSegment 1209331968 1209397504 (120928224682879 / 100000)
      (24186949091211 / 20000) := by
  exact
    packedTile65536 1209331968 1209397504 13 3118 34775 30 _ _ (522833 / 25000) (418267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209397504 :
    ThetaLowerSegment 1209397504 1209463040 (24186949091211 / 20000) (24188258268173 / 20000) := by
  exact
    packedTile65536 1209397504 1209463040 13 3130 34776 30 _ _ (2091337 / 100000) (104567 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209463040 :
    ThetaLowerSegment 1209463040 1209528576 (24188258268173 / 20000)
      (120947787052223 / 100000) := by
  exact
    packedTile65536 1209463040 1209528576 13 3106 34777 30 _ _ (2091343 / 100000) (1045673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209528576 :
    ThetaLowerSegment 1209528576 1209594112 (120947787052223 / 100000)
      (120954433356167 / 100000) := by
  exact
    packedTile65536 1209528576 1209594112 13 3178 34778 30 _ _ (522837 / 25000) (2091351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209594112 :
    ThetaLowerSegment 1209594112 1209659648 (120954433356167 / 100000)
      (120960970928771 / 100000) := by
  exact
    packedTile65536 1209594112 1209659648 13 3126 34779 30 _ _ (1045677 / 50000) (2091357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209659648 :
    ThetaLowerSegment 1209659648 1209725184 (120960970928771 / 100000)
      (30241898565681 / 25000) := by
  exact
    packedTile65536 1209659648 1209725184 13 3167 34780 30 _ _ (2091359 / 100000) (1045681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209725184 :
    ThetaLowerSegment 1209725184 1209790720 (30241898565681 / 25000) (30243562245743 / 25000) := by
  exact
    packedTile65536 1209725184 1209790720 13 3182 34781 30 _ _ (522841 / 25000) (2091367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209790720 :
    ThetaLowerSegment 1209790720 1209856256 (30243562245743 / 25000) (7561298640007 / 6250) := by
  exact
    packedTile65536 1209790720 1209856256 13 3122 34782 30 _ _ (209137 / 10000) (2091373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209856256 :
    ThetaLowerSegment 1209856256 1209921792 (7561298640007 / 6250) (120987292873237 / 100000) := by
  exact
    packedTile65536 1209856256 1209921792 13 3115 34782 30 _ _ (16731 / 800) (1045689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209921792 :
    ThetaLowerSegment 1209921792 1209987328 (120987292873237 / 100000)
      (120993947647579 / 100000) := by
  exact
    packedTile65536 1209921792 1209987328 13 3182 34783 30 _ _ (2091381 / 100000) (261423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1209987328 :
    ThetaLowerSegment 1209987328 1210052864 (120993947647579 / 100000)
      (121000497868531 / 100000) := by
  exact
    packedTile65536 1209987328 1210052864 13 3132 34784 30 _ _ (1045693 / 50000) (2091389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210052864 :
    ThetaLowerSegment 1210052864 1210118400 (121000497868531 / 100000)
      (121007085750181 / 100000) := by
  exact
    packedTile65536 1210052864 1210118400 13 3150 34785 30 _ _ (2091391 / 100000) (1045697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210118400 :
    ThetaLowerSegment 1210118400 1210183936 (121007085750181 / 100000)
      (121013506338971 / 100000) := by
  exact
    packedTile65536 1210118400 1210183936 13 3070 34786 30 _ _ (2091397 / 100000) (10457 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210183936 :
    ThetaLowerSegment 1210183936 1210249472 (121013506338971 / 100000)
      (121020081706859 / 100000) := by
  exact
    packedTile65536 1210183936 1210249472 13 3144 34787 30 _ _ (1045701 / 50000) (418281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210249472 :
    ThetaLowerSegment 1210249472 1210315008 (121020081706859 / 100000)
      (121026596442779 / 100000) := by
  exact
    packedTile65536 1210249472 1210315008 13 3115 34788 30 _ _ (130713 / 6250) (2091411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210315008 :
    ThetaLowerSegment 1210315008 1210380544 (121026596442779 / 100000) (7564568142509 / 6250) := by
  exact
    packedTile65536 1210315008 1210380544 13 3105 34789 30 _ _ (2091413 / 100000) (261427 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210380544 :
    ThetaLowerSegment 1210380544 1210446080 (7564568142509 / 6250) (121039646878709 / 100000) := by
  exact
    packedTile65536 1210380544 1210446080 13 3135 34790 30 _ _ (2091419 / 100000) (1045711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210446080 :
    ThetaLowerSegment 1210446080 1210511616 (121039646878709 / 100000)
      (121046335252661 / 100000) := by
  exact
    packedTile65536 1210446080 1210511616 13 3198 34791 30 _ _ (65357 / 3125) (2091427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210511616 :
    ThetaLowerSegment 1210511616 1210577152 (121046335252661 / 100000)
      (24210562063369 / 20000) := by
  exact
    packedTile65536 1210511616 1210577152 13 3096 34792 30 _ _ (2091429 / 100000) (261429 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210577152 :
    ThetaLowerSegment 1210577152 1210642688 (24210562063369 / 20000) (4842375766169 / 4000) := by
  exact
    packedTile65536 1210577152 1210642688 13 3148 34793 30 _ _ (418287 / 20000) (1045719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210642688 :
    ThetaLowerSegment 1210642688 1210708224 (4842375766169 / 4000) (24213178451661 / 20000) := by
  exact
    packedTile65536 1210642688 1210708224 13 3107 34794 30 _ _ (26143 / 1250) (2091443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210708224 :
    ThetaLowerSegment 1210708224 1210773760 (24213178451661 / 20000) (24214487696857 / 20000) := by
  exact
    packedTile65536 1210708224 1210773760 13 3130 34795 30 _ _ (1045723 / 50000) (2091449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210773760 :
    ThetaLowerSegment 1210773760 1210839296 (24214487696857 / 20000)
      (121078972177209 / 100000) := by
  exact
    packedTile65536 1210773760 1210839296 13 3124 34796 30 _ _ (2091451 / 100000) (1045727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210839296 :
    ThetaLowerSegment 1210839296 1210904832 (121078972177209 / 100000)
      (121085564446521 / 100000) := by
  exact
    packedTile65536 1210839296 1210904832 13 3152 34797 30 _ _ (65358 / 3125) (2091459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210904832 :
    ThetaLowerSegment 1210904832 1210970368 (121085564446521 / 100000) (968737086561 / 800) := by
  exact
    packedTile65536 1210904832 1210970368 13 3142 34798 30 _ _ (1045731 / 50000) (418293 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210970368 :
    ThetaLowerSegment 1210970368 1211035904 (968737086561 / 800) (121098648648363 / 100000) := by
  exact
    packedTile65536 1210970368 1211035904 13 3114 34798 30 _ _ (2091467 / 100000) (209147 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211035904 :
    ThetaLowerSegment 1211035904 1211101440 (121098648648363 / 100000)
      (60552644537569 / 50000) := by
  exact
    packedTile65536 1211035904 1211101440 13 3175 34799 30 _ _ (2091473 / 100000) (522869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211101440 :
    ThetaLowerSegment 1211101440 1211166976 (60552644537569 / 50000) (60555972079067 / 50000) := by
  exact
    packedTile65536 1211101440 1211166976 13 3182 34800 30 _ _ (1045739 / 50000) (2091481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211166976 :
    ThetaLowerSegment 1211166976 1211232512 (60555972079067 / 50000) (60559272440819 / 50000) := by
  exact
    packedTile65536 1211166976 1211232512 13 3156 34801 30 _ _ (522871 / 25000) (2091487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211232512 :
    ThetaLowerSegment 1211232512 1211298048 (60559272440819 / 50000) (30281279085019 / 25000) := by
  exact
    packedTile65536 1211232512 1211298048 13 3142 34802 30 _ _ (2091489 / 100000) (522873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211298048 :
    ThetaLowerSegment 1211298048 1211363584 (30281279085019 / 25000) (3785364721321 / 3125) := by
  exact
    packedTile65536 1211298048 1211363584 13 3134 34803 30 _ _ (1045747 / 50000) (2091497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211363584 :
    ThetaLowerSegment 1211363584 1211429120 (3785364721321 / 3125) (30284551754943 / 25000) := by
  exact
    packedTile65536 1211363584 1211429120 13 3125 34804 30 _ _ (4183 / 200) (2091503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211429120 :
    ThetaLowerSegment 1211429120 1211494656 (30284551754943 / 25000) (60572372532201 / 50000) := by
  exact
    packedTile65536 1211429120 1211494656 13 3126 34805 30 _ _ (418301 / 20000) (522877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211494656 :
    ThetaLowerSegment 1211494656 1211560192 (60572372532201 / 50000)
      (121151247572101 / 100000) := by
  exact
    packedTile65536 1211494656 1211560192 13 3109 34806 30 _ _ (2091511 / 100000) (1045757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211560192 :
    ThetaLowerSegment 1211560192 1211625728 (121151247572101 / 100000)
      (24231543744521 / 20000) := by
  exact
    packedTile65536 1211560192 1211625728 13 3094 34807 30 _ _ (522879 / 25000) (2091519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211625728 :
    ThetaLowerSegment 1211625728 1211691264 (24231543744521 / 20000)
      (121164281915503 / 100000) := by
  exact
    packedTile65536 1211625728 1211691264 13 3138 34808 30 _ _ (2091521 / 100000) (522881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211691264 :
    ThetaLowerSegment 1211691264 1211756800 (121164281915503 / 100000)
      (60585421517851 / 50000) := by
  exact
    packedTile65536 1211691264 1211756800 13 3137 34809 30 _ _ (2091527 / 100000) (209153 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211756800 :
    ThetaLowerSegment 1211756800 1211822336 (60585421517851 / 50000) (60588721955347 / 50000) := by
  exact
    packedTile65536 1211756800 1211822336 13 3156 34810 30 _ _ (522883 / 25000) (418307 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211822336 :
    ThetaLowerSegment 1211822336 1211887872 (60588721955347 / 50000) (30296021135961 / 25000) := by
  exact
    packedTile65536 1211822336 1211887872 13 3175 34811 30 _ _ (1045769 / 50000) (2091541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211887872 :
    ThetaLowerSegment 1211887872 1211953408 (30296021135961 / 25000)
      (121190532770913 / 100000) := by
  exact
    packedTile65536 1211887872 1211953408 13 3083 34812 30 _ _ (2091543 / 100000) (1045773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1211953408 :
    ThetaLowerSegment 1211953408 1212018944 (121190532770913 / 100000)
      (121197083499249 / 100000) := by
  exact
    packedTile65536 1211953408 1212018944 13 3132 34813 30 _ _ (522887 / 25000) (2091551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212018944 :
    ThetaLowerSegment 1212018944 1212084480 (121197083499249 / 100000)
      (24240719319681 / 20000) := by
  exact
    packedTile65536 1212018944 1212084480 13 3114 34814 30 _ _ (1045777 / 50000) (2091557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212084480 :
    ThetaLowerSegment 1212084480 1212150016 (24240719319681 / 20000)
      (121210222657317 / 100000) := by
  exact
    packedTile65536 1212084480 1212150016 13 3168 34815 30 _ _ (2091559 / 100000) (1045781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212150016 :
    ThetaLowerSegment 1212150016 1212215552 (121210222657317 / 100000)
      (121216752523247 / 100000) := by
  exact
    packedTile65536 1212150016 1212215552 13 3122 34815 30 _ _ (418313 / 20000) (130723 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212215552 :
    ThetaLowerSegment 1212215552 1212281088 (121216752523247 / 100000)
      (121223401624277 / 100000) := by
  exact
    packedTile65536 1212215552 1212281088 13 3179 34816 30 _ _ (209157 / 10000) (2091573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212281088 :
    ThetaLowerSegment 1212281088 1212346624 (121223401624277 / 100000)
      (121230006818127 / 100000) := by
  exact
    packedTile65536 1212281088 1212346624 13 3158 34817 30 _ _ (83663 / 4000) (1045789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212346624 :
    ThetaLowerSegment 1212346624 1212412160 (121230006818127 / 100000)
      (60618277779119 / 50000) := by
  exact
    packedTile65536 1212346624 1212412160 13 3131 34818 30 _ _ (2091581 / 100000) (65362 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212412160 :
    ThetaLowerSegment 1212412160 1212477696 (60618277779119 / 50000) (30310771895329 / 25000) := by
  exact
    packedTile65536 1212412160 1212477696 13 3123 34819 30 _ _ (1045793 / 50000) (2091589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212477696 :
    ThetaLowerSegment 1212477696 1212543232 (30310771895329 / 25000) (30312424253009 / 25000) := by
  exact
    packedTile65536 1212477696 1212543232 13 3160 34820 30 _ _ (261449 / 12500) (418319 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212543232 :
    ThetaLowerSegment 1212543232 1212608768 (30312424253009 / 25000) (7578523859753 / 6250) := by
  exact
    packedTile65536 1212543232 1212608768 13 3196 34821 30 _ _ (2091597 / 100000) (5229 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212608768 :
    ThetaLowerSegment 1212608768 1212674304 (7578523859753 / 6250) (7578929630541 / 6250) := by
  exact
    packedTile65536 1212608768 1212674304 13 3104 34822 30 _ _ (1045801 / 50000) (418321 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212674304 :
    ThetaLowerSegment 1212674304 1212739840 (7578929630541 / 6250) (7579342723121 / 6250) := by
  exact
    packedTile65536 1212674304 1212739840 13 3160 34823 30 _ _ (261451 / 12500) (2091611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212739840 :
    ThetaLowerSegment 1212739840 1212805376 (7579342723121 / 6250) (3789875293828 / 3125) := by
  exact
    packedTile65536 1212739840 1212805376 13 3120 34824 30 _ _ (2091613 / 100000) (65363 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212805376 :
    ThetaLowerSegment 1212805376 1212870912 (3789875293828 / 3125) (6064130527603 / 5000) := by
  exact
    packedTile65536 1212805376 1212870912 13 3156 34825 30 _ _ (2091619 / 100000) (1045811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212870912 :
    ThetaLowerSegment 1212870912 1212936448 (6064130527603 / 5000) (30322285673453 / 25000) := by
  exact
    packedTile65536 1212870912 1212936448 13 3123 34826 30 _ _ (261453 / 12500) (2091627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212936448 :
    ThetaLowerSegment 1212936448 1213001984 (30322285673453 / 25000) (60647812327591 / 50000) := by
  exact
    packedTile65536 1212936448 1213001984 13 3099 34827 30 _ _ (209163 / 10000) (2091633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213001984 :
    ThetaLowerSegment 1213001984 1213067520 (60647812327591 / 50000) (30325534501643 / 25000) := by
  exact
    packedTile65536 1213001984 1213067520 13 3114 34828 30 _ _ (418327 / 20000) (1045819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213067520 :
    ThetaLowerSegment 1213067520 1213133056 (30325534501643 / 25000) (30327159705923 / 25000) := by
  exact
    packedTile65536 1213067520 1213133056 13 3108 34829 30 _ _ (52291 / 2500) (2091643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213133056 :
    ThetaLowerSegment 1213133056 1213198592 (30327159705923 / 25000) (758220276511 / 625) := by
  exact
    packedTile65536 1213133056 1213198592 13 3158 34830 30 _ _ (1045823 / 50000) (2091649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213198592 :
    ThetaLowerSegment 1213198592 1213264128 (758220276511 / 625) (24264326847113 / 20000) := by
  exact
    packedTile65536 1213198592 1213264128 13 3055 34831 30 _ _ (2091651 / 100000) (1045827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213264128 :
    ThetaLowerSegment 1213264128 1213329664 (24264326847113 / 20000) (30332018611867 / 25000) := by
  exact
    packedTile65536 1213264128 1213329664 13 3079 34831 30 _ _ (2091657 / 100000) (104583 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213329664 :
    ThetaLowerSegment 1213329664 1213395200 (30332018611867 / 25000) (30333645924903 / 25000) := by
  exact
    packedTile65536 1213329664 1213395200 13 3112 34832 30 _ _ (1045831 / 50000) (418333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213395200 :
    ThetaLowerSegment 1213395200 1213460736 (30333645924903 / 25000) (6067062178367 / 5000) := by
  exact
    packedTile65536 1213395200 1213460736 13 3184 34833 30 _ _ (2091667 / 100000) (209167 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213460736 :
    ThetaLowerSegment 1213460736 1213526272 (6067062178367 / 5000) (12134770683691 / 10000) := by
  exact
    packedTile65536 1213460736 1213526272 13 3090 34834 30 _ _ (2091673 / 100000) (522919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213526272 :
    ThetaLowerSegment 1213526272 1213591808 (12134770683691 / 10000) (60677141536271 / 50000) := by
  exact
    packedTile65536 1213526272 1213591808 13 3144 34835 30 _ _ (1045839 / 50000) (2091681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213591808 :
    ThetaLowerSegment 1213591808 1213657344 (60677141536271 / 50000) (60680489276513 / 50000) := by
  exact
    packedTile65536 1213591808 1213657344 13 3201 34836 30 _ _ (522921 / 25000) (2091687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213657344 :
    ThetaLowerSegment 1213657344 1213722880 (60680489276513 / 50000)
      (121367598748711 / 100000) := by
  exact
    packedTile65536 1213657344 1213722880 13 3165 34837 30 _ _ (2091689 / 100000) (522923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213722880 :
    ThetaLowerSegment 1213722880 1213788416 (121367598748711 / 100000)
      (121374160392789 / 100000) := by
  exact
    packedTile65536 1213722880 1213788416 13 3137 34838 30 _ _ (1045847 / 50000) (2091697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213788416 :
    ThetaLowerSegment 1213788416 1213853952 (121374160392789 / 100000)
      (121380730422489 / 100000) := by
  exact
    packedTile65536 1213788416 1213853952 13 3141 34839 30 _ _ (20917 / 1000) (2091703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213853952 :
    ThetaLowerSegment 1213853952 1213919488 (121380730422489 / 100000)
      (60693625133487 / 50000) := by
  exact
    packedTile65536 1213853952 1213919488 13 3117 34840 30 _ _ (418341 / 20000) (522927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213919488 :
    ThetaLowerSegment 1213919488 1213985024 (60693625133487 / 50000) (15174236169711 / 12500) := by
  exact
    packedTile65536 1213919488 1213985024 13 3174 34841 30 _ _ (2091711 / 100000) (1045857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1213985024 :
    ThetaLowerSegment 1213985024 1214050560 (15174236169711 / 12500) (15175043572087 / 12500) := by
  exact
    packedTile65536 1213985024 1214050560 13 3088 34842 30 _ _ (522929 / 25000) (2091719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214050560 :
    ThetaLowerSegment 1214050560 1214116096 (15175043572087 / 12500)
      (121406881021379 / 100000) := by
  exact
    packedTile65536 1214050560 1214116096 13 3123 34843 30 _ _ (2091721 / 100000) (522931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214116096 :
    ThetaLowerSegment 1214116096 1214181632 (121406881021379 / 100000)
      (121413503429061 / 100000) := by
  exact
    packedTile65536 1214116096 1214181632 13 3166 34844 30 _ _ (2091727 / 100000) (209173 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214181632 :
    ThetaLowerSegment 1214181632 1214247168 (121413503429061 / 100000)
      (24283996304613 / 20000) := by
  exact
    packedTile65536 1214181632 1214247168 13 3097 34845 30 _ _ (522933 / 25000) (418347 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214247168 :
    ThetaLowerSegment 1214247168 1214312704 (24283996304613 / 20000)
      (121426530754743 / 100000) := by
  exact
    packedTile65536 1214247168 1214312704 13 3131 34846 30 _ _ (1045869 / 50000) (2091741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214312704 :
    ThetaLowerSegment 1214312704 1214378240 (121426530754743 / 100000)
      (24286621438947 / 20000) := by
  exact
    packedTile65536 1214312704 1214378240 13 3144 34846 30 _ _ (2091743 / 100000) (1045873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214378240 :
    ThetaLowerSegment 1214378240 1214443776 (24286621438947 / 20000) (4857586174639 / 4000) := by
  exact
    packedTile65536 1214378240 1214443776 13 3130 34847 30 _ _ (522937 / 25000) (2091751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214443776 :
    ThetaLowerSegment 1214443776 1214509312 (4857586174639 / 4000) (24289225668921 / 20000) := by
  exact
    packedTile65536 1214443776 1214509312 13 3095 34848 30 _ _ (1045877 / 50000) (2091757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214509312 :
    ThetaLowerSegment 1214509312 1214574848 (24289225668921 / 20000)
      (121452729936009 / 100000) := by
  exact
    packedTile65536 1214509312 1214574848 13 3156 34849 30 _ _ (2091759 / 100000) (1045881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214574848 :
    ThetaLowerSegment 1214574848 1214640384 (121452729936009 / 100000)
      (121459252056161 / 100000) := by
  exact
    packedTile65536 1214574848 1214640384 13 3118 34850 30 _ _ (522941 / 25000) (2091767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214640384 :
    ThetaLowerSegment 1214640384 1214705920 (121459252056161 / 100000)
      (121465818122191 / 100000) := by
  exact
    packedTile65536 1214640384 1214705920 13 3139 34851 30 _ _ (209177 / 10000) (2091773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214705920 :
    ThetaLowerSegment 1214705920 1214771456 (121465818122191 / 100000)
      (121472411396991 / 100000) := by
  exact
    packedTile65536 1214705920 1214771456 13 3152 34852 30 _ _ (83671 / 4000) (1045889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214771456 :
    ThetaLowerSegment 1214771456 1214836992 (121472411396991 / 100000)
      (30369709860001 / 25000) := by
  exact
    packedTile65536 1214771456 1214836992 13 3073 34853 30 _ _ (2091781 / 100000) (261473 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214836992 :
    ThetaLowerSegment 1214836992 1214902528 (30369709860001 / 25000) (30371354003797 / 25000) := by
  exact
    packedTile65536 1214836992 1214902528 13 3144 34854 30 _ _ (1045893 / 50000) (2091789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214902528 :
    ThetaLowerSegment 1214902528 1214968064 (30371354003797 / 25000) (24298399776293 / 20000) := by
  exact
    packedTile65536 1214902528 1214968064 13 3147 34855 30 _ _ (2091791 / 100000) (1045897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214968064 :
    ThetaLowerSegment 1214968064 1215033600 (24298399776293 / 20000)
      (121498512737323 / 100000) := by
  exact
    packedTile65536 1214968064 1215033600 13 3114 34856 30 _ _ (2091797 / 100000) (10459 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215033600 :
    ThetaLowerSegment 1215033600 1215099136 (121498512737323 / 100000)
      (24300993607659 / 20000) := by
  exact
    packedTile65536 1215033600 1215099136 13 3086 34857 30 _ _ (1045901 / 50000) (418361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215099136 :
    ThetaLowerSegment 1215099136 1215164672 (24300993607659 / 20000)
      (121511511213719 / 100000) := by
  exact
    packedTile65536 1215099136 1215164672 13 3128 34858 30 _ _ (65369 / 3125) (2091811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215164672 :
    ThetaLowerSegment 1215164672 1215230208 (121511511213719 / 100000) (1215180732311 / 1000) := by
  exact
    packedTile65536 1215164672 1215230208 13 3137 34859 30 _ _ (2091813 / 100000) (261477 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215230208 :
    ThetaLowerSegment 1215230208 1215295744 (1215180732311 / 1000) (3797641256693 / 3125) := by
  exact
    packedTile65536 1215230208 1215295744 13 3082 34860 30 _ _ (1045909 / 50000) (2091821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215295744 :
    ThetaLowerSegment 1215295744 1215361280 (3797641256693 / 3125) (7595693687541 / 6250) := by
  exact
    packedTile65536 1215295744 1215361280 13 3145 34861 30 _ _ (130739 / 6250) (2091827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215361280 :
    ThetaLowerSegment 1215361280 1215426816 (7595693687541 / 6250) (24307525519793 / 20000) := by
  exact
    packedTile65536 1215361280 1215426816 13 3121 34862 30 _ _ (2091829 / 100000) (261479 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215426816 :
    ThetaLowerSegment 1215426816 1215492352 (24307525519793 / 20000) (6077211576103 / 5000) := by
  exact
    packedTile65536 1215426816 1215492352 13 3157 34862 30 _ _ (418367 / 20000) (1045919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215492352 :
    ThetaLowerSegment 1215492352 1215557888 (6077211576103 / 5000) (6077541773047 / 5000) := by
  exact
    packedTile65536 1215492352 1215557888 13 3157 34863 30 _ _ (13074 / 625) (2091843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215557888 :
    ThetaLowerSegment 1215557888 1215623424 (6077541773047 / 5000) (6077867264129 / 5000) := by
  exact
    packedTile65536 1215557888 1215623424 13 3112 34864 30 _ _ (418369 / 20000) (261481 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215623424 :
    ThetaLowerSegment 1215623424 1215688960 (6077867264129 / 5000) (15195487119989 / 12500) := by
  exact
    packedTile65536 1215623424 1215688960 13 3132 34865 30 _ _ (2091851 / 100000) (1045927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215688960 :
    ThetaLowerSegment 1215688960 1215754496 (15195487119989 / 12500) (15196322554979 / 12500) := by
  exact
    packedTile65536 1215688960 1215754496 13 3195 34866 30 _ _ (130741 / 6250) (2091859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215754496 :
    ThetaLowerSegment 1215754496 1215820032 (15196322554979 / 12500) (60788642428771 / 50000) := by
  exact
    packedTile65536 1215754496 1215820032 13 3205 34867 30 _ _ (1045931 / 50000) (418373 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215820032 :
    ThetaLowerSegment 1215820032 1215885568 (60788642428771 / 50000)
      (121583796839513 / 100000) := by
  exact
    packedTile65536 1215820032 1215885568 13 3113 34868 30 _ _ (2091867 / 100000) (209187 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215885568 :
    ThetaLowerSegment 1215885568 1215951104 (121583796839513 / 100000)
      (24318040011941 / 20000) := by
  exact
    packedTile65536 1215885568 1215951104 13 3061 34869 30 _ _ (65371 / 3125) (3347 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1215951104 :
    ThetaLowerSegment 1215951104 1216016640 (24318040011941 / 20000) (24319362078837 / 20000) := by
  exact
    packedTile65536 1215951104 1216016640 13 3160 34870 30 _ _ (1045939 / 50000) (2091881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216016640 :
    ThetaLowerSegment 1216016640 1216082176 (24319362078837 / 20000)
      (121603370539273 / 100000) := by
  exact
    packedTile65536 1216016640 1216082176 13 3136 34871 30 _ _ (2091883 / 100000) (1045943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216082176 :
    ThetaLowerSegment 1216082176 1216147712 (121603370539273 / 100000) (7600623676039 / 6250) := by
  exact
    packedTile65536 1216082176 1216147712 13 3159 34872 30 _ _ (2091889 / 100000) (522973 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216147712 :
    ThetaLowerSegment 1216147712 1216213248 (7600623676039 / 6250) (60808266360263 / 50000) := by
  exact
    packedTile65536 1216147712 1216213248 13 3133 34873 30 _ _ (1045947 / 50000) (2091897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216213248 :
    ThetaLowerSegment 1216213248 1216278784 (60808266360263 / 50000)
      (121623132661871 / 100000) := by
  exact
    packedTile65536 1216213248 1216278784 13 3155 34874 30 _ _ (2091899 / 100000) (1045951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216278784 :
    ThetaLowerSegment 1216278784 1216344320 (121623132661871 / 100000)
      (30407409098629 / 25000) := by
  exact
    packedTile65536 1216278784 1216344320 13 3109 34875 30 _ _ (418381 / 20000) (522977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216344320 :
    ThetaLowerSegment 1216344320 1216409856 (30407409098629 / 25000) (30409078442809 / 25000) := by
  exact
    packedTile65536 1216344320 1216409856 13 3192 34876 30 _ _ (209191 / 10000) (2091913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216409856 :
    ThetaLowerSegment 1216409856 1216475392 (30409078442809 / 25000)
      (121642842637951 / 100000) := by
  exact
    packedTile65536 1216409856 1216475392 13 3121 34877 30 _ _ (418383 / 20000) (1045959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216475392 :
    ThetaLowerSegment 1216475392 1216540928 (121642842637951 / 100000)
      (60824671118249 / 50000) := by
  exact
    packedTile65536 1216475392 1216540928 13 3107 34878 30 _ _ (2091921 / 100000) (522981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216540928 :
    ThetaLowerSegment 1216540928 1216606464 (60824671118249 / 50000) (15206985984119 / 12500) := by
  exact
    packedTile65536 1216540928 1216606464 13 3129 34878 30 _ _ (1045963 / 50000) (2091929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216606464 :
    ThetaLowerSegment 1216606464 1216672000 (15206985984119 / 12500) (30415617795739 / 25000) := by
  exact
    packedTile65536 1216606464 1216672000 13 3147 34879 30 _ _ (522983 / 25000) (418387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216672000 :
    ThetaLowerSegment 1216672000 1216737536 (30415617795739 / 25000)
      (121669008486081 / 100000) := by
  exact
    packedTile65536 1216672000 1216737536 13 3125 34880 30 _ _ (2091937 / 100000) (104597 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216737536 :
    ThetaLowerSegment 1216737536 1216803072 (121669008486081 / 100000)
      (121675554172599 / 100000) := by
  exact
    packedTile65536 1216737536 1216803072 13 3129 34881 30 _ _ (1045971 / 50000) (418389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216803072 :
    ThetaLowerSegment 1216803072 1216868608 (121675554172599 / 100000)
      (121682141716851 / 100000) := by
  exact
    packedTile65536 1216803072 1216868608 13 3149 34882 30 _ _ (522987 / 25000) (2091951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216868608 :
    ThetaLowerSegment 1216868608 1216934144 (121682141716851 / 100000)
      (30422155123823 / 25000) := by
  exact
    packedTile65536 1216868608 1216934144 13 3097 34883 30 _ _ (2091953 / 100000) (522989 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216934144 :
    ThetaLowerSegment 1216934144 1216999680 (30422155123823 / 25000) (60847605083071 / 50000) := by
  exact
    packedTile65536 1216934144 1216999680 13 3150 34884 30 _ _ (2091959 / 100000) (1045981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216999680 :
    ThetaLowerSegment 1216999680 1217065216 (60847605083071 / 50000) (12170165759919 / 10000) := by
  exact
    packedTile65536 1216999680 1217065216 13 3082 34885 30 _ _ (522991 / 25000) (2091967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217065216 :
    ThetaLowerSegment 1217065216 1217130752 (12170165759919 / 10000) (60854138294553 / 50000) := by
  exact
    packedTile65536 1217065216 1217130752 13 3164 34886 30 _ _ (2091969 / 100000) (522993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217130752 :
    ThetaLowerSegment 1217130752 1217196288 (60854138294553 / 50000) (3803590879683 / 3125) := by
  exact
    packedTile65536 1217130752 1217196288 13 3170 34887 30 _ _ (83679 / 4000) (1045989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217196288 :
    ThetaLowerSegment 1217196288 1217261824 (3803590879683 / 3125) (30430392776539 / 25000) := by
  exact
    packedTile65536 1217196288 1217261824 13 3185 34888 30 _ _ (104599 / 5000) (2091983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217261824 :
    ThetaLowerSegment 1217261824 1217327360 (30430392776539 / 25000)
      (121728213158531 / 100000) := by
  exact
    packedTile65536 1217261824 1217327360 13 3175 34889 30 _ _ (418397 / 20000) (522997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217327360 :
    ThetaLowerSegment 1217327360 1217392896 (121728213158531 / 100000)
      (121734828034073 / 100000) := by
  exact
    packedTile65536 1217327360 1217392896 13 3162 34890 30 _ _ (2091991 / 100000) (1045997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217392896 :
    ThetaLowerSegment 1217392896 1217458432 (121734828034073 / 100000)
      (121741340417621 / 100000) := by
  exact
    packedTile65536 1217392896 1217458432 13 3113 34891 30 _ _ (522999 / 25000) (2091999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217458432 :
    ThetaLowerSegment 1217458432 1217523968 (121741340417621 / 100000)
      (121747825623821 / 100000) := by
  exact
    packedTile65536 1217458432 1217523968 13 3100 34892 30 _ _ (1046001 / 50000) (418401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217523968 :
    ThetaLowerSegment 1217523968 1217589504 (121747825623821 / 100000) (7609649788613 / 6250) := by
  exact
    packedTile65536 1217523968 1217589504 13 3141 34893 30 _ _ (2092007 / 100000) (209201 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217589504 :
    ThetaLowerSegment 1217589504 1217655040 (7609649788613 / 6250) (30440235630839 / 25000) := by
  exact
    packedTile65536 1217589504 1217655040 13 3129 34893 30 _ _ (523003 / 25000) (418403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217655040 :
    ThetaLowerSegment 1217655040 1217720576 (30440235630839 / 25000) (15220914351273 / 12500) := by
  exact
    packedTile65536 1217655040 1217720576 13 3046 34894 30 _ _ (1046009 / 50000) (2092021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217720576 :
    ThetaLowerSegment 1217720576 1217786112 (15220914351273 / 12500)
      (121773852382059 / 100000) := by
  exact
    packedTile65536 1217720576 1217786112 13 3125 34895 30 _ _ (2092023 / 100000) (1046013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217786112 :
    ThetaLowerSegment 1217786112 1217851648 (121773852382059 / 100000)
      (121780425537177 / 100000) := by
  exact
    packedTile65536 1217786112 1217851648 13 3142 34896 30 _ _ (2092029 / 100000) (65376 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217851648 :
    ThetaLowerSegment 1217851648 1217917184 (121780425537177 / 100000)
      (121786965235461 / 100000) := by
  exact
    packedTile65536 1217851648 1217917184 13 3126 34897 30 _ _ (1046017 / 50000) (2092037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217917184 :
    ThetaLowerSegment 1217917184 1217982720 (121786965235461 / 100000)
      (121793475660829 / 100000) := by
  exact
    packedTile65536 1217917184 1217982720 13 3112 34898 30 _ _ (2092039 / 100000) (1046021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1217982720 :
    ThetaLowerSegment 1217982720 1218048256 (121793475660829 / 100000)
      (60900019202997 / 50000) := by
  exact
    packedTile65536 1217982720 1218048256 13 3137 34899 30 _ _ (418409 / 20000) (130753 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218048256 :
    ThetaLowerSegment 1218048256 1218113792 (60900019202997 / 50000) (15225841359243 / 12500) := by
  exact
    packedTile65536 1218048256 1218113792 13 3199 34900 30 _ _ (41841 / 2000) (2092053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218113792 :
    ThetaLowerSegment 1218113792 1218179328 (15225841359243 / 12500) (3806662746132 / 3125) := by
  exact
    packedTile65536 1218113792 1218179328 13 3096 34901 30 _ _ (418411 / 20000) (1046029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218179328 :
    ThetaLowerSegment 1218179328 1218244864 (3806662746132 / 3125) (30454960973429 / 25000) := by
  exact
    packedTile65536 1218179328 1218244864 13 3172 34902 30 _ _ (2092061 / 100000) (65377 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218244864 :
    ThetaLowerSegment 1218244864 1218310400 (30454960973429 / 25000) (3045658964681 / 2500) := by
  exact
    packedTile65536 1218244864 1218310400 13 3114 34903 30 _ _ (1046033 / 50000) (2092069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218310400 :
    ThetaLowerSegment 1218310400 1218375936 (3045658964681 / 2500) (15229107070359 / 12500) := by
  exact
    packedTile65536 1218310400 1218375936 13 3106 34904 30 _ _ (261509 / 12500) (83683 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218375936 :
    ThetaLowerSegment 1218375936 1218441472 (15229107070359 / 12500)
      (121839302252109 / 100000) := by
  exact
    packedTile65536 1218375936 1218441472 13 3081 34905 30 _ _ (2092077 / 100000) (26151 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218441472 :
    ThetaLowerSegment 1218441472 1218507008 (121839302252109 / 100000)
      (121845904862901 / 100000) := by
  exact
    packedTile65536 1218441472 1218507008 13 3156 34906 30 _ _ (1046041 / 50000) (418417 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218507008 :
    ThetaLowerSegment 1218507008 1218572544 (121845904862901 / 100000) (4874099630237 / 4000) := by
  exact
    packedTile65536 1218507008 1218572544 13 3148 34907 30 _ _ (261511 / 12500) (2092091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218572544 :
    ThetaLowerSegment 1218572544 1218638080 (4874099630237 / 4000) (121859001349341 / 100000) := by
  exact
    packedTile65536 1218572544 1218638080 13 3112 34908 30 _ _ (2092093 / 100000) (65378 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218638080 :
    ThetaLowerSegment 1218638080 1218703616 (121859001349341 / 100000)
      (121865664681471 / 100000) := by
  exact
    packedTile65536 1218638080 1218703616 13 3185 34908 30 _ _ (1046049 / 50000) (2092101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218703616 :
    ThetaLowerSegment 1218703616 1218769152 (121865664681471 / 100000)
      (121872062335503 / 100000) := by
  exact
    packedTile65536 1218703616 1218769152 13 3058 34909 30 _ _ (261513 / 12500) (2092107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218769152 :
    ThetaLowerSegment 1218769152 1218834688 (121872062335503 / 100000)
      (30469673057231 / 25000) := by
  exact
    packedTile65536 1218769152 1218834688 13 3169 34910 30 _ _ (2092109 / 100000) (130757 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218834688 :
    ThetaLowerSegment 1218834688 1218900224 (30469673057231 / 25000)
      (121885363983659 / 100000) := by
  exact
    packedTile65536 1218834688 1218900224 13 3189 34911 30 _ _ (418423 / 20000) (1046059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218900224 :
    ThetaLowerSegment 1218900224 1218965760 (121885363983659 / 100000)
      (121891864200499 / 100000) := by
  exact
    packedTile65536 1218900224 1218965760 13 3107 34912 30 _ _ (52303 / 2500) (2092123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218965760 :
    ThetaLowerSegment 1218965760 1219031296 (121891864200499 / 100000)
      (121898437657249 / 100000) := by
  exact
    packedTile65536 1218965760 1219031296 13 3142 34913 30 _ _ (16737 / 800) (65379 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219031296 :
    ThetaLowerSegment 1219031296 1219096832 (121898437657249 / 100000)
      (15238128222221 / 12500) := by
  exact
    packedTile65536 1219031296 1219096832 13 3149 34914 30 _ _ (2092131 / 100000) (1046067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219096832 :
    ThetaLowerSegment 1219096832 1219162368 (15238128222221 / 12500) (3809737542538 / 3125) := by
  exact
    packedTile65536 1219096832 1219162368 13 3143 34915 30 _ _ (261517 / 12500) (2092139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219162368 :
    ThetaLowerSegment 1219162368 1219227904 (3809737542538 / 3125) (121918235540327 / 100000) := by
  exact
    packedTile65536 1219162368 1219227904 13 3171 34916 30 _ _ (2092141 / 100000) (130759 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219227904 :
    ThetaLowerSegment 1219227904 1219293440 (121918235540327 / 100000)
      (60962399302733 / 50000) := by
  exact
    packedTile65536 1219227904 1219293440 13 3137 34917 30 _ _ (2092147 / 100000) (41843 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219293440 :
    ThetaLowerSegment 1219293440 1219358976 (60962399302733 / 50000) (60965678750993 / 50000) := by
  exact
    packedTile65536 1219293440 1219358976 13 3135 34918 30 _ _ (261519 / 12500) (418431 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219358976 :
    ThetaLowerSegment 1219358976 1219424512 (60965678750993 / 50000) (3810563157038 / 3125) := by
  exact
    packedTile65536 1219358976 1219424512 13 3185 34919 30 _ _ (1046079 / 50000) (2092161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219424512 :
    ThetaLowerSegment 1219424512 1219490048 (3810563157038 / 3125) (121944592509199 / 100000) := by
  exact
    packedTile65536 1219424512 1219490048 13 3141 34920 30 _ _ (2092163 / 100000) (1046083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219490048 :
    ThetaLowerSegment 1219490048 1219555584 (121944592509199 / 100000)
      (121951076137831 / 100000) := by
  exact
    packedTile65536 1219490048 1219555584 13 3099 34921 30 _ _ (261521 / 12500) (2092171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219555584 :
    ThetaLowerSegment 1219555584 1219621120 (121951076137831 / 100000)
      (121957691592019 / 100000) := by
  exact
    packedTile65536 1219555584 1219621120 13 3162 34922 30 _ _ (1046087 / 50000) (2092177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219621120 :
    ThetaLowerSegment 1219621120 1219686656 (121957691592019 / 100000) (3049107519637 / 2500) := by
  exact
    packedTile65536 1219621120 1219686656 13 3159 34923 30 _ _ (2092179 / 100000) (1046091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219686656 :
    ThetaLowerSegment 1219686656 1219752192 (3049107519637 / 2500) (3049269663897 / 2500) := by
  exact
    packedTile65536 1219686656 1219752192 13 3100 34924 30 _ _ (261523 / 12500) (2092187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219752192 :
    ThetaLowerSegment 1219752192 1219817728 (3049269663897 / 2500) (1219773936919 / 1000) := by
  exact
    packedTile65536 1219752192 1219817728 13 3158 34924 30 _ _ (209219 / 10000) (2092193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219817728 :
    ThetaLowerSegment 1219817728 1219883264 (1219773936919 / 1000) (24396779665231 / 20000) := by
  exact
    packedTile65536 1219817728 1219883264 13 3109 34925 30 _ _ (418439 / 20000) (1046099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219883264 :
    ThetaLowerSegment 1219883264 1219948800 (24396779665231 / 20000) (15248812925589 / 12500) := by
  exact
    packedTile65536 1219883264 1219948800 13 3157 34926 30 _ _ (2092201 / 100000) (523051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1219948800 :
    ThetaLowerSegment 1219948800 1220014336 (15248812925589 / 12500) (60998543788497 / 50000) := by
  exact
    packedTile65536 1219948800 1220014336 13 3147 34927 30 _ _ (1046103 / 50000) (2092209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220014336 :
    ThetaLowerSegment 1220014336 1220145408 (60998543788497 / 50000)
      (122010404500009 / 100000) := by
  exact
    packedTile65536 1220014336 1220145408 14 6365 34928 30 _ _ (2092211 / 100000) (1046107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220145408 :
    ThetaLowerSegment 1220145408 1220276480 (122010404500009 / 100000)
      (122023480887509 / 100000) := by
  exact
    packedTile65536 1220145408 1220276480 14 6250 34930 30 _ _ (1046111 / 50000) (83689 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220276480 :
    ThetaLowerSegment 1220276480 1220407552 (122023480887509 / 100000)
      (24407320674577 / 20000) := by
  exact
    packedTile65536 1220276480 1220407552 14 6272 34932 30 _ _ (2092233 / 100000) (523059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220407552 :
    ThetaLowerSegment 1220407552 1220538624 (24407320674577 / 20000)
      (122049740572961 / 100000) := by
  exact
    packedTile65536 1220407552 1220538624 14 6279 34934 30 _ _ (523061 / 25000) (2092247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220538624 :
    ThetaLowerSegment 1220538624 1220669696 (122049740572961 / 100000)
      (122062551444203 / 100000) := by
  exact
    packedTile65536 1220538624 1220669696 14 6123 34936 30 _ _ (1046127 / 50000) (2092257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220669696 :
    ThetaLowerSegment 1220669696 1220735232 (122062551444203 / 100000)
      (122069024912113 / 100000) := by
  exact
    packedTile65536 1220669696 1220735232 13 3094 34938 30 _ _ (418453 / 20000) (523067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220735232 :
    ThetaLowerSegment 1220735232 1220800768 (122069024912113 / 100000)
      (122075621839423 / 100000) := by
  exact
    packedTile65536 1220735232 1220800768 13 3153 34939 30 _ _ (209227 / 10000) (2092273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220800768 :
    ThetaLowerSegment 1220800768 1220866304 (122075621839423 / 100000)
      (122082176940131 / 100000) := by
  exact
    packedTile65536 1220800768 1220866304 13 3133 34939 30 _ _ (523069 / 25000) (2092279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220866304 :
    ThetaLowerSegment 1220866304 1220931840 (122082176940131 / 100000)
      (61044347197723 / 50000) := by
  exact
    packedTile65536 1220866304 1220931840 13 3115 34940 30 _ _ (2092281 / 100000) (523071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220931840 :
    ThetaLowerSegment 1220931840 1220997376 (61044347197723 / 50000)
      (122095241161469 / 100000) := by
  exact
    packedTile65536 1220931840 1220997376 13 3129 34941 30 _ _ (2092287 / 100000) (209229 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220997376 :
    ThetaLowerSegment 1220997376 1221062912 (122095241161469 / 100000)
      (122101844435021 / 100000) := by
  exact
    packedTile65536 1220997376 1221062912 13 3156 34942 30 _ _ (523073 / 25000) (418459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221062912 :
    ThetaLowerSegment 1221062912 1221128448 (122101844435021 / 100000)
      (61054199800761 / 50000) := by
  exact
    packedTile65536 1221062912 1221128448 13 3133 34943 30 _ _ (2092297 / 100000) (20923 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221128448 :
    ThetaLowerSegment 1221128448 1221193984 (61054199800761 / 50000) (3816093710162 / 3125) := by
  exact
    packedTile65536 1221128448 1221193984 13 3154 34944 30 _ _ (2092303 / 100000) (1046153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221193984 :
    ThetaLowerSegment 1221193984 1221259520 (3816093710162 / 3125) (15265189271537 / 12500) := by
  exact
    packedTile65536 1221193984 1221259520 13 3114 34945 30 _ _ (523077 / 25000) (2092311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221259520 :
    ThetaLowerSegment 1221259520 1221325056 (15265189271537 / 12500)
      (122128186558453 / 100000) := by
  exact
    packedTile65536 1221259520 1221325056 13 3189 34946 30 _ _ (2092313 / 100000) (523079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221325056 :
    ThetaLowerSegment 1221325056 1221456128 (122128186558453 / 100000)
      (122141171490167 / 100000) := by
  exact
    packedTile65536 1221325056 1221456128 14 6206 34947 30 _ _ (2092319 / 100000) (1046161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221456128 :
    ThetaLowerSegment 1221456128 1221521664 (122141171490167 / 100000)
      (122147603309513 / 100000) := by
  exact
    packedTile65536 1221456128 1221521664 13 3074 34949 30 _ _ (2092329 / 100000) (523083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221521664 :
    ThetaLowerSegment 1221521664 1221587200 (122147603309513 / 100000)
      (61077110682559 / 50000) := by
  exact
    packedTile65536 1221521664 1221587200 13 3163 34950 30 _ _ (418467 / 20000) (1046169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221587200 :
    ThetaLowerSegment 1221587200 1221652736 (61077110682559 / 50000) (61080396702529 / 50000) := by
  exact
    packedTile65536 1221587200 1221652736 13 3141 34951 30 _ _ (104617 / 5000) (2092343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221652736 :
    ThetaLowerSegment 1221652736 1221718272 (61080396702529 / 50000) (61083702609209 / 50000) := by
  exact
    packedTile65536 1221652736 1221718272 13 3160 34952 30 _ _ (1046173 / 50000) (2092349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221718272 :
    ThetaLowerSegment 1221718272 1221783808 (61083702609209 / 50000) (61086966676769 / 50000) := by
  exact
    packedTile65536 1221718272 1221783808 13 3120 34953 30 _ _ (2092351 / 100000) (1046177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221783808 :
    ThetaLowerSegment 1221783808 1221849344 (61086966676769 / 50000) (12218035060939 / 10000) := by
  exact
    packedTile65536 1221783808 1221849344 13 3067 34954 30 _ _ (523089 / 25000) (2092359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221849344 :
    ThetaLowerSegment 1221849344 1221914880 (12218035060939 / 10000) (30546725448703 / 25000) := by
  exact
    packedTile65536 1221849344 1221914880 13 3131 34954 30 _ _ (1046181 / 50000) (418473 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221914880 :
    ThetaLowerSegment 1221914880 1221980416 (30546725448703 / 25000) (61096796592239 / 50000) := by
  exact
    packedTile65536 1221914880 1221980416 13 3198 34955 30 _ _ (2092367 / 100000) (209237 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1221980416 :
    ThetaLowerSegment 1221980416 1222045952 (61096796592239 / 50000) (61099966535819 / 50000) := by
  exact
    packedTile65536 1221980416 1222045952 13 3030 34956 30 _ _ (523093 / 25000) (16739 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222045952 :
    ThetaLowerSegment 1222045952 1222111488 (61099966535819 / 50000) (61103222275987 / 50000) := by
  exact
    packedTile65536 1222045952 1222111488 13 3112 34957 30 _ _ (1046189 / 50000) (2092381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222111488 :
    ThetaLowerSegment 1222111488 1222177024 (61103222275987 / 50000)
      (122212983248849 / 100000) := by
  exact
    packedTile65536 1222111488 1222177024 13 3125 34958 30 _ _ (2092383 / 100000) (1046193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222177024 :
    ThetaLowerSegment 1222177024 1222242560 (122212983248849 / 100000)
      (24443917783553 / 20000) := by
  exact
    packedTile65536 1222177024 1222242560 13 3157 34959 30 _ _ (523097 / 25000) (2092391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222242560 :
    ThetaLowerSegment 1222242560 1222308096 (24443917783553 / 20000)
      (122226244823079 / 100000) := by
  exact
    packedTile65536 1222242560 1222308096 13 3181 34960 30 _ _ (1046197 / 50000) (2092397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222308096 :
    ThetaLowerSegment 1222308096 1222373632 (122226244823079 / 100000) (763955341947 / 625) := by
  exact
    packedTile65536 1222308096 1222373632 13 3159 34961 30 _ _ (2092399 / 100000) (1046201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222373632 :
    ThetaLowerSegment 1222373632 1222439168 (763955341947 / 625) (24447892923783 / 20000) := by
  exact
    packedTile65536 1222373632 1222439168 13 3159 34962 30 _ _ (418481 / 20000) (261551 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222439168 :
    ThetaLowerSegment 1222439168 1222504704 (24447892923783 / 20000) (24449187288609 / 20000) := by
  exact
    packedTile65536 1222439168 1222504704 13 3093 34963 30 _ _ (209241 / 10000) (2092413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222504704 :
    ThetaLowerSegment 1222504704 1222570240 (24449187288609 / 20000) (12225244594611 / 10000) := by
  exact
    packedTile65536 1222504704 1222570240 13 3111 34964 30 _ _ (418483 / 20000) (1046209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222570240 :
    ThetaLowerSegment 1222570240 1222635776 (12225244594611 / 10000)
      (122259022425313 / 100000) := by
  exact
    packedTile65536 1222570240 1222635776 13 3143 34965 30 _ _ (2092421 / 100000) (261553 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222635776 :
    ThetaLowerSegment 1222635776 1222701312 (122259022425313 / 100000)
      (122265592642953 / 100000) := by
  exact
    packedTile65536 1222635776 1222701312 13 3140 34966 30 _ _ (1046213 / 50000) (2092429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222701312 :
    ThetaLowerSegment 1222701312 1222766848 (122265592642953 / 100000)
      (122272087548777 / 100000) := by
  exact
    packedTile65536 1222701312 1222766848 13 3104 34967 30 _ _ (2092431 / 100000) (1046217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222766848 :
    ThetaLowerSegment 1222766848 1222832384 (122272087548777 / 100000)
      (122278674540453 / 100000) := by
  exact
    packedTile65536 1222766848 1222832384 13 3148 34968 30 _ _ (2092437 / 100000) (52311 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222832384 :
    ThetaLowerSegment 1222832384 1222897920 (122278674540453 / 100000)
      (122285140186233 / 100000) := by
  exact
    packedTile65536 1222832384 1222897920 13 3090 34969 30 _ _ (1046221 / 50000) (418489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222897920 :
    ThetaLowerSegment 1222897920 1222963456 (122285140186233 / 100000)
      (30572936510353 / 25000) := by
  exact
    packedTile65536 1222897920 1222963456 13 3157 34969 30 _ _ (2092447 / 100000) (41849 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222963456 :
    ThetaLowerSegment 1222963456 1223028992 (30572936510353 / 25000) (12229841259667 / 10000) := by
  exact
    packedTile65536 1222963456 1223028992 13 3186 34970 30 _ _ (2092453 / 100000) (261557 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223028992 :
    ThetaLowerSegment 1223028992 1223094528 (12229841259667 / 10000) (1528811894099 / 1250) := by
  exact
    packedTile65536 1223028992 1223094528 13 3125 34971 30 _ _ (1046229 / 50000) (2092461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223094528 :
    ThetaLowerSegment 1223094528 1223160064 (1528811894099 / 1250) (24462293910033 / 20000) := by
  exact
    packedTile65536 1223094528 1223160064 13 3115 34972 30 _ _ (2092463 / 100000) (1046233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223160064 :
    ThetaLowerSegment 1223160064 1223225600 (24462293910033 / 20000) (61159037737399 / 50000) := by
  exact
    packedTile65536 1223160064 1223225600 13 3157 34973 30 _ _ (2092469 / 100000) (261559 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223225600 :
    ThetaLowerSegment 1223225600 1223291136 (61159037737399 / 50000) (61162287349521 / 50000) := by
  exact
    packedTile65536 1223225600 1223291136 13 3106 34974 30 _ _ (1046237 / 50000) (2092477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223291136 :
    ThetaLowerSegment 1223291136 1223356672 (61162287349521 / 50000) (61165550572081 / 50000) := by
  exact
    packedTile65536 1223291136 1223356672 13 3119 34975 30 _ _ (13078 / 625) (2092483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223356672 :
    ThetaLowerSegment 1223356672 1223422208 (61165550572081 / 50000) (61168802293771 / 50000) := by
  exact
    packedTile65536 1223356672 1223422208 13 3108 34976 30 _ _ (418497 / 20000) (261561 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223422208 :
    ThetaLowerSegment 1223422208 1223487744 (61168802293771 / 50000) (15293009582389 / 12500) := by
  exact
    packedTile65536 1223422208 1223487744 13 3093 34977 30 _ _ (209249 / 10000) (2092493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223487744 :
    ThetaLowerSegment 1223487744 1223553280 (15293009582389 / 12500) (3058768688409 / 2500) := by
  exact
    packedTile65536 1223487744 1223553280 13 3188 34978 30 _ _ (130781 / 6250) (2092499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223553280 :
    ThetaLowerSegment 1223553280 1223618816 (3058768688409 / 2500) (122357253121969 / 100000) := by
  exact
    packedTile65536 1223553280 1223618816 13 3109 34979 30 _ _ (2092501 / 100000) (261563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223618816 :
    ThetaLowerSegment 1223618816 1223684352 (122357253121969 / 100000)
      (122363817313291 / 100000) := by
  exact
    packedTile65536 1223618816 1223684352 13 3137 34980 30 _ _ (1046253 / 50000) (2092509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223684352 :
    ThetaLowerSegment 1223684352 1223749888 (122363817313291 / 100000)
      (122370322933099 / 100000) := by
  exact
    packedTile65536 1223684352 1223749888 13 3109 34981 30 _ _ (65391 / 3125) (418503 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223749888 :
    ThetaLowerSegment 1223749888 1223815424 (122370322933099 / 100000)
      (61188462412117 / 50000) := by
  exact
    packedTile65536 1223749888 1223815424 13 3155 34982 30 _ _ (2092517 / 100000) (52313 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223815424 :
    ThetaLowerSegment 1223815424 1223880960 (61188462412117 / 50000) (61191753949223 / 50000) := by
  exact
    packedTile65536 1223815424 1223880960 13 3146 34983 30 _ _ (1046261 / 50000) (83701 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223880960 :
    ThetaLowerSegment 1223880960 1223946496 (61191753949223 / 50000) (12239012656451 / 10000) := by
  exact
    packedTile65536 1223880960 1223946496 13 3163 34984 30 _ _ (130783 / 6250) (2092531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1223946496 :
    ThetaLowerSegment 1223946496 1224012032 (12239012656451 / 10000) (7649790169517 / 6250) := by
  exact
    packedTile65536 1223946496 1224012032 13 3114 34984 30 _ _ (2092533 / 100000) (261567 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224012032 :
    ThetaLowerSegment 1224012032 1224077568 (7649790169517 / 6250) (15300403752737 / 12500) := by
  exact
    packedTile65536 1224012032 1224077568 13 3148 34985 30 _ _ (1046269 / 50000) (2092541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224077568 :
    ThetaLowerSegment 1224077568 1224143104 (15300403752737 / 12500) (15301232923297 / 12500) := by
  exact
    packedTile65536 1224077568 1224143104 13 3170 34986 30 _ _ (65392 / 3125) (2092547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224143104 :
    ThetaLowerSegment 1224143104 1224208640 (15301232923297 / 12500) (765102136988 / 625) := by
  exact
    packedTile65536 1224143104 1224208640 13 3096 34987 30 _ _ (2092549 / 100000) (261569 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224208640 :
    ThetaLowerSegment 1224208640 1224274176 (765102136988 / 625) (2448457162687 / 2000) := by
  exact
    packedTile65536 1224208640 1224274176 13 3114 34988 30 _ _ (418511 / 20000) (1046279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224274176 :
    ThetaLowerSegment 1224274176 1224339712 (2448457162687 / 2000) (2448589203223 / 2000) := by
  exact
    packedTile65536 1224274176 1224339712 13 3155 34989 30 _ _ (26157 / 1250) (2092563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224339712 :
    ThetaLowerSegment 1224339712 1224405248 (2448589203223 / 2000) (12243604755577 / 10000) := by
  exact
    packedTile65536 1224339712 1224405248 13 3148 34990 30 _ _ (418513 / 20000) (261571 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224405248 :
    ThetaLowerSegment 1224405248 1224470784 (12243604755577 / 10000)
      (122442557544151 / 100000) := by
  exact
    packedTile65536 1224405248 1224470784 13 3111 34991 30 _ _ (2092571 / 100000) (1046287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224470784 :
    ThetaLowerSegment 1224470784 1224536320 (122442557544151 / 100000)
      (24489810580011 / 20000) := by
  exact
    packedTile65536 1224470784 1224536320 13 3104 34992 30 _ _ (65393 / 3125) (2092579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224536320 :
    ThetaLowerSegment 1224536320 1224601856 (24489810580011 / 20000) (61227789830097 / 50000) := by
  exact
    packedTile65536 1224536320 1224601856 13 3119 34993 30 _ _ (2092581 / 100000) (261573 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224601856 :
    ThetaLowerSegment 1224601856 1224667392 (61227789830097 / 50000)
      (122462206883223 / 100000) := by
  exact
    packedTile65536 1224601856 1224667392 13 3167 34994 30 _ _ (2092587 / 100000) (209259 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224667392 :
    ThetaLowerSegment 1224667392 1224732928 (122462206883223 / 100000)
      (122468823659127 / 100000) := by
  exact
    packedTile65536 1224667392 1224732928 13 3162 34995 30 _ _ (130787 / 6250) (418519 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224732928 :
    ThetaLowerSegment 1224732928 1224798464 (122468823659127 / 100000)
      (12247530861723 / 10000) := by
  exact
    packedTile65536 1224732928 1224798464 13 3099 34996 30 _ _ (2092597 / 100000) (10463 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224798464 :
    ThetaLowerSegment 1224798464 1224864000 (12247530861723 / 10000)
      (122481860557223 / 100000) := by
  exact
    packedTile65536 1224798464 1224864000 13 3131 34997 30 _ _ (2092603 / 100000) (1046303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224864000 :
    ThetaLowerSegment 1224864000 1224929536 (122481860557223 / 100000)
      (24497654461627 / 20000) := by
  exact
    packedTile65536 1224864000 1224929536 13 3064 34998 30 _ _ (65394 / 3125) (2092611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224929536 :
    ThetaLowerSegment 1224929536 1224995072 (24497654461627 / 20000) (61247382843137 / 50000) := by
  exact
    packedTile65536 1224929536 1224995072 13 3103 34998 30 _ _ (2092613 / 100000) (261577 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224995072 :
    ThetaLowerSegment 1224995072 1225060608 (61247382843137 / 50000)
      (122501359528743 / 100000) := by
  exact
    packedTile65536 1224995072 1225060608 13 3151 34999 30 _ _ (2092619 / 100000) (1046311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225060608 :
    ThetaLowerSegment 1225060608 1225126144 (122501359528743 / 100000)
      (122507861311511 / 100000) := by
  exact
    packedTile65536 1225060608 1225126144 13 3107 35000 30 _ _ (130789 / 6250) (2092627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225126144 :
    ThetaLowerSegment 1225126144 1225191680 (122507861311511 / 100000)
      (122514310794089 / 100000) := by
  exact
    packedTile65536 1225126144 1225191680 13 3082 35001 30 _ _ (2092629 / 100000) (261579 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225191680 :
    ThetaLowerSegment 1225191680 1225257216 (122514310794089 / 100000)
      (61260469084567 / 50000) := by
  exact
    packedTile65536 1225191680 1225257216 13 3167 35002 30 _ _ (418527 / 20000) (1046319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225257216 :
    ThetaLowerSegment 1225257216 1225322752 (61260469084567 / 50000) (61263762899927 / 50000) := by
  exact
    packedTile65536 1225257216 1225322752 13 3148 35003 30 _ _ (13079 / 625) (2092643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225322752 :
    ThetaLowerSegment 1225322752 1225339136 (61263762899927 / 50000) (61264604143619 / 50000) := by
  exact
    packedTile65536 1225322752 1225339136 11 804 35004 30 _ _ (1046323 / 50000) (2092649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225339136 :
    ThetaLowerSegment 1225339136 1225341184 (61264604143619 / 50000)
      (122529402903409 / 100000) := by
  exact
    packedTile65536 1225339136 1225341184 8 93 35004 30 _ _ (2092647 / 100000) (41853 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1193341184_1225341184 :
    ThetaLowerSegment 1193341184 1225341184 (3729049404488 / 3125) (122529402903409 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1193341184 cell1193406720)
                    (ThetaLowerSegment.join cell1193472256 cell1193537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1193603328 cell1193668864)
                    (ThetaLowerSegment.join cell1193734400 cell1193799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1193865472 cell1193931008)
                    (ThetaLowerSegment.join cell1193996544 cell1194062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1194127616 cell1194193152)
                    (ThetaLowerSegment.join cell1194258688 cell1194324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1194389760 cell1194455296)
                    (ThetaLowerSegment.join cell1194520832 cell1194586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1194651904 cell1194717440)
                    (ThetaLowerSegment.join cell1194782976 cell1194848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1194914048 cell1194979584)
                    (ThetaLowerSegment.join cell1195045120 cell1195110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1195176192 cell1195241728)
                    (ThetaLowerSegment.join cell1195307264 cell1195372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1195438336 cell1195503872)
                    (ThetaLowerSegment.join cell1195569408 cell1195634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1195700480 cell1195766016)
                    (ThetaLowerSegment.join cell1195831552 cell1195897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1195962624 cell1196028160)
                    (ThetaLowerSegment.join cell1196093696 cell1196159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1196224768 cell1196290304)
                    (ThetaLowerSegment.join cell1196355840 cell1196421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1196486912 cell1196552448)
                    (ThetaLowerSegment.join cell1196617984 cell1196683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1196749056 cell1196814592)
                    (ThetaLowerSegment.join cell1196880128 cell1196945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1197011200 cell1197076736)
                    (ThetaLowerSegment.join cell1197142272 cell1197207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1197273344 cell1197338880)
                    (ThetaLowerSegment.join cell1197404416 cell1197469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1197535488 cell1197601024)
                    (ThetaLowerSegment.join cell1197666560 cell1197732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1197797632 cell1197863168)
                    (ThetaLowerSegment.join cell1197928704 cell1197994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1198059776 cell1198125312)
                    (ThetaLowerSegment.join cell1198190848 cell1198256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1198321920 cell1198387456)
                    (ThetaLowerSegment.join cell1198452992 cell1198518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1198584064 cell1198649600)
                    (ThetaLowerSegment.join cell1198715136 cell1198846208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1198911744 cell1198977280)
                    (ThetaLowerSegment.join cell1199042816 cell1199108352)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1199173888 cell1199304960)
                    (ThetaLowerSegment.join cell1199370496 cell1199436032))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1199501568 cell1199567104)
                    (ThetaLowerSegment.join cell1199632640 cell1199698176)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1199763712 cell1199829248)
                    (ThetaLowerSegment.join cell1199894784 cell1199960320))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1200025856 cell1200091392)
                    (ThetaLowerSegment.join cell1200156928 cell1200222464)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1200288000 cell1200353536)
                    (ThetaLowerSegment.join cell1200419072 cell1200484608))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1200550144 cell1200615680)
                    (ThetaLowerSegment.join cell1200681216 cell1200746752))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1200812288 cell1200877824)
                    (ThetaLowerSegment.join cell1200943360 cell1201008896))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1201074432 cell1201139968)
                    (ThetaLowerSegment.join cell1201205504 cell1201271040)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1201336576 cell1201402112)
                    (ThetaLowerSegment.join cell1201467648 cell1201533184))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1201598720 cell1201664256)
                    (ThetaLowerSegment.join cell1201729792 cell1201795328)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1201860864 cell1201926400)
                    (ThetaLowerSegment.join cell1201991936 cell1202057472))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1202123008 cell1202188544)
                    (ThetaLowerSegment.join cell1202254080 cell1202319616)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1202385152 cell1202450688)
                    (ThetaLowerSegment.join cell1202516224 cell1202581760))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1202647296 cell1202712832)
                    (ThetaLowerSegment.join cell1202778368 cell1202843904))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1202909440 cell1202974976)
                    (ThetaLowerSegment.join cell1203040512 cell1203106048))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1203171584 cell1203237120)
                    (ThetaLowerSegment.join cell1203302656 cell1203368192)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1203433728 cell1203499264)
                    (ThetaLowerSegment.join cell1203564800 cell1203630336))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1203695872 cell1203761408)
                    (ThetaLowerSegment.join cell1203826944 cell1203892480)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1203958016 cell1204023552)
                    (ThetaLowerSegment.join cell1204089088 cell1204154624))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1204220160 cell1204285696)
                    (ThetaLowerSegment.join cell1204351232 cell1204416768)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1204482304 cell1204547840)
                    (ThetaLowerSegment.join cell1204613376 cell1204678912))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1204744448 cell1204809984)
                    (ThetaLowerSegment.join cell1204875520 cell1204941056))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1205006592 cell1205072128)
                    (ThetaLowerSegment.join cell1205137664 cell1205203200))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1205268736 cell1205334272)
                    (ThetaLowerSegment.join cell1205399808 cell1205465344)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1205530880 cell1205596416)
                    (ThetaLowerSegment.join cell1205661952 cell1205727488))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1205793024 cell1205858560)
                    (ThetaLowerSegment.join cell1205924096 cell1205989632))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1206055168 cell1206120704)
                    (ThetaLowerSegment.join cell1206186240 cell1206251776))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1206317312 cell1206382848)
                    (ThetaLowerSegment.join cell1206448384 cell1206513920)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1206579456 cell1206644992)
                    (ThetaLowerSegment.join cell1206710528 cell1206776064))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1206841600 cell1206907136)
                    (ThetaLowerSegment.join cell1206972672 cell1207038208))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1207103744 cell1207169280)
                    (ThetaLowerSegment.join cell1207234816 cell1207300352))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1207365888 cell1207431424)
                    (ThetaLowerSegment.join cell1207496960 cell1207562496)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1207628032 cell1207693568)
                    (ThetaLowerSegment.join cell1207759104 cell1207824640))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1207890176 cell1207955712)
                    (ThetaLowerSegment.join cell1208021248 cell1208086784)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1208152320 cell1208217856)
                    (ThetaLowerSegment.join cell1208283392 cell1208348928))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1208414464 cell1208480000)
                    (ThetaLowerSegment.join cell1208545536 cell1208611072)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1208676608 cell1208742144)
                    (ThetaLowerSegment.join cell1208807680 cell1208873216))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1208938752 cell1209004288)
                    (ThetaLowerSegment.join cell1209069824 cell1209135360))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1209200896 cell1209266432)
                    (ThetaLowerSegment.join cell1209331968 cell1209397504))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1209463040 cell1209528576)
                    (ThetaLowerSegment.join cell1209594112 cell1209659648)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1209725184 cell1209790720)
                    (ThetaLowerSegment.join cell1209856256 cell1209921792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1209987328 cell1210052864)
                    (ThetaLowerSegment.join cell1210118400 cell1210183936))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1210249472 cell1210315008)
                    (ThetaLowerSegment.join cell1210380544 cell1210446080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1210511616 cell1210577152)
                    (ThetaLowerSegment.join cell1210642688 cell1210708224)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1210773760 cell1210839296)
                    (ThetaLowerSegment.join cell1210904832 cell1210970368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1211035904 cell1211101440)
                    (ThetaLowerSegment.join cell1211166976 cell1211232512))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1211298048 cell1211363584)
                    (ThetaLowerSegment.join cell1211429120 cell1211494656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1211560192 cell1211625728)
                    (ThetaLowerSegment.join cell1211691264 cell1211756800)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1211822336 cell1211887872)
                    (ThetaLowerSegment.join cell1211953408 cell1212018944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1212084480 cell1212150016)
                    (ThetaLowerSegment.join cell1212215552 cell1212281088)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1212346624 cell1212412160)
                    (ThetaLowerSegment.join cell1212477696 cell1212543232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1212608768 cell1212674304)
                    (ThetaLowerSegment.join cell1212739840 cell1212805376)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1212870912 cell1212936448)
                    (ThetaLowerSegment.join cell1213001984 cell1213067520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1213133056 cell1213198592)
                    (ThetaLowerSegment.join cell1213264128 cell1213329664))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1213395200 cell1213460736)
                    (ThetaLowerSegment.join cell1213526272 cell1213591808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1213657344 cell1213722880)
                    (ThetaLowerSegment.join cell1213788416 cell1213853952)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1213919488 cell1213985024)
                    (ThetaLowerSegment.join cell1214050560 cell1214116096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1214181632 cell1214247168)
                    (ThetaLowerSegment.join cell1214312704 cell1214378240))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1214443776 cell1214509312)
                    (ThetaLowerSegment.join cell1214574848 cell1214640384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1214705920 cell1214771456)
                    (ThetaLowerSegment.join cell1214836992 cell1214902528)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1214968064 cell1215033600)
                    (ThetaLowerSegment.join cell1215099136 cell1215164672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1215230208 cell1215295744)
                    (ThetaLowerSegment.join cell1215361280 cell1215426816))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1215492352 cell1215557888)
                    (ThetaLowerSegment.join cell1215623424 cell1215688960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1215754496 cell1215820032)
                    (ThetaLowerSegment.join cell1215885568 cell1215951104)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1216016640 cell1216082176)
                    (ThetaLowerSegment.join cell1216147712 cell1216213248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1216278784 cell1216344320)
                    (ThetaLowerSegment.join cell1216409856 cell1216475392)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1216540928 cell1216606464)
                    (ThetaLowerSegment.join cell1216672000 cell1216737536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1216803072 cell1216868608)
                    (ThetaLowerSegment.join cell1216934144 cell1216999680)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1217065216 cell1217130752)
                    (ThetaLowerSegment.join cell1217196288 cell1217261824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1217327360 cell1217392896)
                    (ThetaLowerSegment.join cell1217458432 cell1217523968))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1217589504 cell1217655040)
                    (ThetaLowerSegment.join cell1217720576 cell1217786112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1217851648 cell1217917184)
                    (ThetaLowerSegment.join cell1217982720 cell1218048256)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1218113792 cell1218179328)
                    (ThetaLowerSegment.join cell1218244864 cell1218310400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1218375936 cell1218441472)
                    (ThetaLowerSegment.join cell1218507008 cell1218572544)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1218638080 cell1218703616)
                    (ThetaLowerSegment.join cell1218769152 cell1218834688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1218900224 cell1218965760)
                    (ThetaLowerSegment.join cell1219031296 cell1219096832)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1219162368 cell1219227904)
                    (ThetaLowerSegment.join cell1219293440 cell1219358976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1219424512 cell1219490048)
                    (ThetaLowerSegment.join cell1219555584 cell1219621120))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1219686656 cell1219752192)
                    (ThetaLowerSegment.join cell1219817728 cell1219883264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1219948800 cell1220014336)
                    (ThetaLowerSegment.join cell1220145408 cell1220276480)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1220407552 cell1220538624)
                    (ThetaLowerSegment.join cell1220669696 cell1220735232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1220800768 cell1220866304)
                    (ThetaLowerSegment.join cell1220931840 cell1220997376)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1221062912 cell1221128448)
                    (ThetaLowerSegment.join cell1221193984 cell1221259520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1221325056 cell1221456128)
                    (ThetaLowerSegment.join cell1221521664 cell1221587200)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1221652736 cell1221718272)
                    (ThetaLowerSegment.join cell1221783808 cell1221849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1221914880 cell1221980416)
                    (ThetaLowerSegment.join cell1222045952 cell1222111488))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1222177024 cell1222242560)
                    (ThetaLowerSegment.join cell1222308096 cell1222373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1222439168 cell1222504704)
                    (ThetaLowerSegment.join cell1222570240 cell1222635776)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1222701312 cell1222766848)
                    (ThetaLowerSegment.join cell1222832384 cell1222897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1222963456 cell1223028992)
                    (ThetaLowerSegment.join cell1223094528 cell1223160064))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1223225600 cell1223291136)
                    (ThetaLowerSegment.join cell1223356672 cell1223422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1223487744 cell1223553280)
                    (ThetaLowerSegment.join cell1223618816 cell1223684352)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1223749888 cell1223815424)
                    (ThetaLowerSegment.join cell1223880960 cell1223946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1224012032 cell1224077568)
                    (ThetaLowerSegment.join cell1224143104 cell1224208640))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1224274176 cell1224339712)
                    (ThetaLowerSegment.join cell1224405248 cell1224470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1224536320 cell1224601856)
                    (ThetaLowerSegment.join cell1224667392 cell1224732928)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1224798464 cell1224864000)
                    (ThetaLowerSegment.join cell1224929536 cell1224995072))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1225060608 cell1225126144)
                    (ThetaLowerSegment.join cell1225191680 cell1225257216)))))
            (ThetaLowerSegment.join cell1225322752 cell1225339136)))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
