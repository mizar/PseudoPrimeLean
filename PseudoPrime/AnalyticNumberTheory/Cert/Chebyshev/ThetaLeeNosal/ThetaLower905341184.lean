/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 905341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell873341184 :
    ThetaLowerSegment 873341184 873406720 (87330957008989 / 100000) (87337487465493 / 100000) := by
  exact
    packedTile32768 873341184 873406720 13 3172 29552 30 _ _ (1029391 / 50000) (411757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873406720 :
    ThetaLowerSegment 873406720 873472256 (87337487465493 / 100000) (87344007653423 / 100000) := by
  exact
    packedTile32768 873406720 873472256 13 3167 29553 30 _ _ (205879 / 10000) (2058793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873472256 :
    ThetaLowerSegment 873472256 873537792 (87344007653423 / 100000) (4367529893131 / 5000) := by
  exact
    packedTile32768 873472256 873537792 13 3201 29554 30 _ _ (2058797 / 100000) (5147 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873537792 :
    ThetaLowerSegment 873537792 873603328 (4367529893131 / 5000) (3494287523897 / 4000) := by
  exact
    packedTile32768 873537792 873603328 13 3201 29555 30 _ _ (411761 / 20000) (257351 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873603328 :
    ThetaLowerSegment 873603328 873668864 (3494287523897 / 4000) (87363741296021 / 100000) := by
  exact
    packedTile32768 873603328 873668864 13 3183 29556 30 _ _ (514703 / 25000) (411763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873668864 :
    ThetaLowerSegment 873668864 873734400 (87363741296021 / 100000) (87370150402681 / 100000) := by
  exact
    packedTile32768 873668864 873734400 13 3113 29557 30 _ _ (102941 / 5000) (2058823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873734400 :
    ThetaLowerSegment 873734400 873799936 (87370150402681 / 100000) (87376697472541 / 100000) := by
  exact
    packedTile32768 873734400 873799936 13 3180 29558 30 _ _ (2058827 / 100000) (205883 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873799936 :
    ThetaLowerSegment 873799936 873865472 (87376697472541 / 100000) (21845811656669 / 25000) := by
  exact
    packedTile32768 873799936 873865472 13 3181 29560 30 _ _ (411767 / 20000) (1029419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873865472 :
    ThetaLowerSegment 873865472 873931008 (21845811656669 / 25000) (4369492981359 / 5000) := by
  exact
    packedTile32768 873865472 873931008 13 3212 29561 30 _ _ (1029421 / 50000) (411769 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873931008 :
    ThetaLowerSegment 873931008 873996544 (4369492981359 / 5000) (4369817867889 / 5000) := by
  exact
    packedTile32768 873931008 873996544 13 3156 29562 30 _ _ (41177 / 2000) (2058853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873996544 :
    ThetaLowerSegment 873996544 874062080 (4369817867889 / 5000) (10925356888809 / 12500) := by
  exact
    packedTile32768 873996544 874062080 13 3156 29563 30 _ _ (2058857 / 100000) (102943 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874062080 :
    ThetaLowerSegment 874062080 874127616 (10925356888809 / 12500) (43704719680371 / 50000) := by
  exact
    packedTile32768 874062080 874127616 13 3198 29564 30 _ _ (411773 / 20000) (514717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874127616 :
    ThetaLowerSegment 874127616 874193152 (43704719680371 / 50000) (8741601539791 / 10000) := by
  exact
    packedTile32768 874127616 874193152 13 3194 29565 30 _ _ (257359 / 12500) (16471 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874193152 :
    ThetaLowerSegment 874193152 874258688 (8741601539791 / 10000) (8742248028111 / 10000) := by
  exact
    packedTile32768 874193152 874258688 13 3140 29566 30 _ _ (12868 / 625) (2058883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874258688 :
    ThetaLowerSegment 874258688 874324224 (8742248028111 / 10000) (87429070778397 / 100000) := by
  exact
    packedTile32768 874258688 874324224 13 3201 29567 30 _ _ (2058887 / 100000) (205889 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874324224 :
    ThetaLowerSegment 874324224 874389760 (87429070778397 / 100000) (21858907089743 / 25000) := by
  exact
    packedTile32768 874324224 874389760 13 3185 29568 30 _ _ (411779 / 20000) (1029449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874389760 :
    ThetaLowerSegment 874389760 874455296 (21858907089743 / 25000) (5465134177669 / 6250) := by
  exact
    packedTile32768 874389760 874455296 13 3166 29570 30 _ _ (1029451 / 50000) (411781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874455296 :
    ThetaLowerSegment 874455296 874520832 (5465134177669 / 6250) (2732773494562 / 3125) := by
  exact
    packedTile32768 874455296 874520832 13 3208 29571 30 _ _ (205891 / 10000) (2058913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874520832 :
    ThetaLowerSegment 874520832 874586368 (2732773494562 / 3125) (87455288887459 / 100000) := by
  exact
    packedTile32768 874520832 874586368 13 3175 29572 30 _ _ (2058917 / 100000) (51473 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874586368 :
    ThetaLowerSegment 874586368 874651904 (87455288887459 / 100000) (87461893918859 / 100000) := by
  exact
    packedTile32768 874586368 874651904 13 3208 29573 30 _ _ (82357 / 4000) (128683 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874651904 :
    ThetaLowerSegment 874651904 874717440 (87461893918859 / 100000) (87468358965339 / 100000) := by
  exact
    packedTile32768 874651904 874717440 13 3140 29574 30 _ _ (514733 / 25000) (411787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874717440 :
    ThetaLowerSegment 874717440 874782976 (87468358965339 / 100000) (87475013459419 / 100000) := by
  exact
    packedTile32768 874717440 874782976 13 3232 29575 30 _ _ (102947 / 5000) (2058943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874782976 :
    ThetaLowerSegment 874782976 874848512 (87475013459419 / 100000) (43740867960687 / 50000) := by
  exact
    packedTile32768 874782976 874848512 13 3265 29576 30 _ _ (2058947 / 100000) (41179 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874848512 :
    ThetaLowerSegment 874848512 874914048 (43740867960687 / 50000) (87488297810959 / 100000) := by
  exact
    packedTile32768 874848512 874914048 13 3187 29577 30 _ _ (411791 / 20000) (1029479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874914048 :
    ThetaLowerSegment 874914048 874979584 (87488297810959 / 100000) (87494863840777 / 100000) := by
  exact
    packedTile32768 874914048 874979584 13 3189 29578 30 _ _ (1029481 / 50000) (411793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell874979584 :
    ThetaLowerSegment 874979584 875045120 (87494863840777 / 100000) (87501359891127 / 100000) := by
  exact
    packedTile32768 874979584 875045120 13 3155 29580 30 _ _ (205897 / 10000) (2058973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875045120 :
    ThetaLowerSegment 875045120 875110656 (87501359891127 / 100000) (87507907437987 / 100000) := by
  exact
    packedTile32768 875045120 875110656 13 3180 29581 30 _ _ (2058977 / 100000) (102949 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875110656 :
    ThetaLowerSegment 875110656 875176192 (87507907437987 / 100000) (87514455010287 / 100000) := by
  exact
    packedTile32768 875110656 875176192 13 3180 29582 30 _ _ (411797 / 20000) (514747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875176192 :
    ThetaLowerSegment 875176192 875241728 (87514455010287 / 100000) (87520924363151 / 100000) := by
  exact
    packedTile32768 875176192 875241728 13 3142 29583 30 _ _ (128687 / 6250) (411799 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875241728 :
    ThetaLowerSegment 875241728 875307264 (87520924363151 / 100000) (87527490514151 / 100000) := by
  exact
    packedTile32768 875241728 875307264 13 3189 29584 30 _ _ (2059 / 100) (2059003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875307264 :
    ThetaLowerSegment 875307264 875372800 (87527490514151 / 100000) (87534046392439 / 100000) := by
  exact
    packedTile32768 875307264 875372800 13 3184 29585 30 _ _ (2059007 / 100000) (205901 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875372800 :
    ThetaLowerSegment 875372800 875438336 (87534046392439 / 100000) (21885131528161 / 25000) := by
  exact
    packedTile32768 875372800 875438336 13 3147 29586 30 _ _ (411803 / 20000) (1029509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875438336 :
    ThetaLowerSegment 875438336 875503872 (21885131528161 / 25000) (8754714175033 / 10000) := by
  exact
    packedTile32768 875438336 875503872 13 3213 29587 30 _ _ (1029511 / 50000) (82361 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875503872 :
    ThetaLowerSegment 875503872 875569408 (8754714175033 / 10000) (2188839405477 / 2500) := by
  exact
    packedTile32768 875503872 875569408 13 3125 29588 30 _ _ (205903 / 10000) (2059033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875569408 :
    ThetaLowerSegment 875569408 875634944 (2188839405477 / 2500) (10945004169889 / 12500) := by
  exact
    packedTile32768 875569408 875634944 13 3136 29590 30 _ _ (2059037 / 100000) (12869 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875634944 :
    ThetaLowerSegment 875634944 875700480 (10945004169889 / 12500) (4378326688051 / 5000) := by
  exact
    packedTile32768 875634944 875700480 13 3157 29591 30 _ _ (514761 / 25000) (2059047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875700480 :
    ThetaLowerSegment 875700480 875766016 (4378326688051 / 5000) (21893258032283 / 25000) := by
  exact
    packedTile32768 875700480 875766016 13 3156 29592 30 _ _ (514763 / 25000) (411811 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875766016 :
    ThetaLowerSegment 875766016 875831552 (21893258032283 / 25000) (2736862902553 / 3125) := by
  exact
    packedTile32768 875766016 875831552 13 3196 29593 30 _ _ (2059059 / 100000) (1029531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875831552 :
    ThetaLowerSegment 875831552 875897088 (2736862902553 / 3125) (87586311026647 / 100000) := by
  exact
    packedTile32768 875831552 875897088 13 3253 29594 30 _ _ (2059067 / 100000) (205907 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875897088 :
    ThetaLowerSegment 875897088 875962624 (87586311026647 / 100000) (17518560245579 / 20000) := by
  exact
    packedTile32768 875897088 875962624 13 3152 29595 30 _ _ (1029537 / 50000) (2059077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell875962624 :
    ThetaLowerSegment 875962624 876028160 (17518560245579 / 20000) (87599371758557 / 100000) := by
  exact
    packedTile32768 875962624 876028160 13 3191 29596 30 _ _ (1029541 / 50000) (411817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876028160 :
    ThetaLowerSegment 876028160 876093696 (87599371758557 / 100000) (10950723227599 / 12500) := by
  exact
    packedTile32768 876028160 876093696 13 3115 29597 30 _ _ (2059089 / 100000) (514773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876093696 :
    ThetaLowerSegment 876093696 876159232 (10950723227599 / 12500) (43806164815529 / 50000) := by
  exact
    packedTile32768 876093696 876159232 13 3178 29598 30 _ _ (2059097 / 100000) (20591 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876159232 :
    ThetaLowerSegment 876159232 876224768 (43806164815529 / 50000) (43809422318057 / 50000) := by
  exact
    packedTile32768 876159232 876224768 13 3164 29599 30 _ _ (64347 / 3125) (2059107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876224768 :
    ThetaLowerSegment 876224768 876290304 (43809422318057 / 50000) (43812666449013 / 50000) := by
  exact
    packedTile32768 876224768 876290304 13 3151 29601 30 _ _ (257389 / 12500) (411823 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876290304 :
    ThetaLowerSegment 876290304 876355840 (43812666449013 / 50000) (4381588485201 / 5000) := by
  exact
    packedTile32768 876290304 876355840 13 3126 29602 30 _ _ (2059119 / 100000) (1029561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876355840 :
    ThetaLowerSegment 876355840 876421376 (4381588485201 / 5000) (17527682077719 / 20000) := by
  exact
    packedTile32768 876355840 876421376 13 3225 29603 30 _ _ (2059127 / 100000) (205913 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876421376 :
    ThetaLowerSegment 876421376 876486912 (17527682077719 / 20000) (87644991380859 / 100000) := by
  exact
    packedTile32768 876421376 876486912 13 3196 29604 30 _ _ (1029567 / 50000) (2059137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876486912 :
    ThetaLowerSegment 876486912 876552448 (87644991380859 / 100000) (87651584753543 / 100000) := by
  exact
    packedTile32768 876486912 876552448 13 3202 29605 30 _ _ (1029571 / 50000) (411829 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876552448 :
    ThetaLowerSegment 876552448 876617984 (87651584753543 / 100000) (43829044802617 / 50000) := by
  exact
    packedTile32768 876552448 876617984 13 3159 29606 30 _ _ (2059149 / 100000) (128697 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876617984 :
    ThetaLowerSegment 876617984 876683520 (43829044802617 / 50000) (8766469538089 / 10000) := by
  exact
    packedTile32768 876617984 876683520 13 3208 29607 30 _ _ (2059157 / 100000) (51479 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876683520 :
    ThetaLowerSegment 876683520 876749056 (8766469538089 / 10000) (43835587784999 / 50000) := by
  exact
    packedTile32768 876683520 876749056 13 3147 29608 30 _ _ (514791 / 25000) (2059167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876749056 :
    ThetaLowerSegment 876749056 876814592 (43835587784999 / 50000) (8767772579613 / 10000) := by
  exact
    packedTile32768 876749056 876814592 13 3181 29609 30 _ _ (514793 / 25000) (82367 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876814592 :
    ThetaLowerSegment 876814592 876880128 (8767772579613 / 10000) (21921057170853 / 25000) := by
  exact
    packedTile32768 876814592 876880128 13 3158 29611 30 _ _ (2059179 / 100000) (1029591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876880128 :
    ThetaLowerSegment 876880128 876945664 (21921057170853 / 25000) (43845431691963 / 50000) := by
  exact
    packedTile32768 876880128 876945664 13 3222 29612 30 _ _ (2059187 / 100000) (205919 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell876945664 :
    ThetaLowerSegment 876945664 877011200 (43845431691963 / 50000) (350789366433 / 400) := by
  exact
    packedTile32768 876945664 877011200 13 3146 29613 30 _ _ (1029597 / 50000) (2059197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877011200 :
    ThetaLowerSegment 877011200 877076736 (350789366433 / 400) (43851926402487 / 50000) := by
  exact
    packedTile32768 877011200 877076736 13 3162 29614 30 _ _ (1029601 / 50000) (411841 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877076736 :
    ThetaLowerSegment 877076736 877142272 (43851926402487 / 50000) (43855155242199 / 50000) := by
  exact
    packedTile32768 877076736 877142272 13 3136 29615 30 _ _ (2059209 / 100000) (514803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877142272 :
    ThetaLowerSegment 877142272 877207808 (43855155242199 / 50000) (43858447928583 / 50000) := by
  exact
    packedTile32768 877142272 877207808 13 3198 29616 30 _ _ (128701 / 6250) (2059219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877207808 :
    ThetaLowerSegment 877207808 877273344 (43858447928583 / 50000) (43861724153967 / 50000) := by
  exact
    packedTile32768 877207808 877273344 13 3182 29617 30 _ _ (257403 / 12500) (2059227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877273344 :
    ThetaLowerSegment 877273344 877338880 (43861724153967 / 50000) (21932489899089 / 25000) := by
  exact
    packedTile32768 877273344 877338880 13 3162 29618 30 _ _ (2059231 / 100000) (1029617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877338880 :
    ThetaLowerSegment 877338880 877404416 (21932489899089 / 25000) (21934129053333 / 25000) := by
  exact
    packedTile32768 877338880 877404416 13 3184 29619 30 _ _ (2059239 / 100000) (1029621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877404416 :
    ThetaLowerSegment 877404416 877469952 (21934129053333 / 25000) (43871467441557 / 50000) := by
  exact
    packedTile32768 877404416 877469952 13 3117 29621 30 _ _ (1029623 / 50000) (2059249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877469952 :
    ThetaLowerSegment 877469952 877535488 (43871467441557 / 50000) (10968689789769 / 12500) := by
  exact
    packedTile32768 877469952 877535488 13 3197 29622 30 _ _ (1029627 / 50000) (2059257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877535488 :
    ThetaLowerSegment 877535488 877601024 (10968689789769 / 12500) (10969509375647 / 12500) := by
  exact
    packedTile32768 877535488 877601024 13 3184 29623 30 _ _ (2059261 / 100000) (64352 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877601024 :
    ThetaLowerSegment 877601024 877666560 (10969509375647 / 12500) (21940680581377 / 25000) := by
  exact
    packedTile32768 877601024 877666560 13 3228 29624 30 _ _ (2059269 / 100000) (257409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877666560 :
    ThetaLowerSegment 877666560 877732096 (21940680581377 / 25000) (21942306379779 / 25000) := by
  exact
    packedTile32768 877666560 877732096 13 3158 29625 30 _ _ (514819 / 25000) (2059279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877732096 :
    ThetaLowerSegment 877732096 877797632 (21942306379779 / 25000) (21943938362349 / 25000) := by
  exact
    packedTile32768 877732096 877797632 13 3170 29626 30 _ _ (514821 / 25000) (2059287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877797632 :
    ThetaLowerSegment 877797632 877863168 (21943938362349 / 25000) (87782337002723 / 100000) := by
  exact
    packedTile32768 877797632 877863168 13 3197 29627 30 _ _ (2059291 / 100000) (1029647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877863168 :
    ThetaLowerSegment 877863168 877928704 (87782337002723 / 100000) (10973605291033 / 12500) := by
  exact
    packedTile32768 877863168 877928704 13 3159 29628 30 _ _ (2059299 / 100000) (1029651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877928704 :
    ThetaLowerSegment 877928704 877994240 (10973605291033 / 12500) (43897684134489 / 50000) := by
  exact
    packedTile32768 877928704 877994240 13 3169 29629 30 _ _ (1029653 / 50000) (2059309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell877994240 :
    ThetaLowerSegment 877994240 878059776 (43897684134489 / 50000) (8780197454829 / 10000) := by
  exact
    packedTile32768 877994240 878059776 13 3208 29630 30 _ _ (1029657 / 50000) (2059317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878059776 :
    ThetaLowerSegment 878059776 878125312 (8780197454829 / 10000) (87808566434811 / 100000) := by
  exact
    packedTile32768 878059776 878125312 13 3201 29632 30 _ _ (2059321 / 100000) (514831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878125312 :
    ThetaLowerSegment 878125312 878190848 (87808566434811 / 100000) (87815135691131 / 100000) := by
  exact
    packedTile32768 878125312 878190848 13 3190 29633 30 _ _ (64354 / 3125) (2059331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878190848 :
    ThetaLowerSegment 878190848 878256384 (87815135691131 / 100000) (87821680260939 / 100000) := by
  exact
    packedTile32768 878190848 878256384 13 3178 29634 30 _ _ (257417 / 12500) (2059339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878256384 :
    ThetaLowerSegment 878256384 878321920 (87821680260939 / 100000) (17565646618073 / 20000) := by
  exact
    packedTile32768 878256384 878321920 13 3182 29635 30 _ _ (2059343 / 100000) (1029673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878321920 :
    ThetaLowerSegment 878321920 878387456 (17565646618073 / 20000) (43917418714511 / 50000) := by
  exact
    packedTile32768 878321920 878387456 13 3207 29636 30 _ _ (2059351 / 100000) (1029677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878387456 :
    ThetaLowerSegment 878387456 878452992 (43917418714511 / 50000) (8784131616929 / 10000) := by
  exact
    packedTile32768 878387456 878452992 13 3146 29637 30 _ _ (1029679 / 50000) (2059361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878452992 :
    ThetaLowerSegment 878452992 878518528 (8784131616929 / 10000) (43923944832781 / 50000) := by
  exact
    packedTile32768 878452992 878518528 13 3192 29638 30 _ _ (1029683 / 50000) (2059369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878518528 :
    ThetaLowerSegment 878518528 878584064 (43923944832781 / 50000) (87854457006059 / 100000) := by
  exact
    packedTile32768 878518528 878584064 13 3189 29639 30 _ _ (2059373 / 100000) (128711 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878584064 :
    ThetaLowerSegment 878584064 878649600 (87854457006059 / 100000) (87861030550211 / 100000) := by
  exact
    packedTile32768 878584064 878649600 13 3192 29640 30 _ _ (2059381 / 100000) (257423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878649600 :
    ThetaLowerSegment 878649600 878715136 (87861030550211 / 100000) (87867519681799 / 100000) := by
  exact
    packedTile32768 878649600 878715136 13 3151 29642 30 _ _ (514847 / 25000) (2059391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878715136 :
    ThetaLowerSegment 878715136 878780672 (87867519681799 / 100000) (87874206540611 / 100000) := by
  exact
    packedTile32768 878715136 878780672 13 3247 29643 30 _ _ (514849 / 25000) (2059399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878780672 :
    ThetaLowerSegment 878780672 878846208 (87874206540611 / 100000) (87880808986629 / 100000) := by
  exact
    packedTile32768 878780672 878846208 13 3206 29644 30 _ _ (2059403 / 100000) (1029703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878846208 :
    ThetaLowerSegment 878846208 878911744 (87880808986629 / 100000) (87887324963033 / 100000) := by
  exact
    packedTile32768 878846208 878911744 13 3164 29645 30 _ _ (2059411 / 100000) (1029707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878911744 :
    ThetaLowerSegment 878911744 878977280 (87887324963033 / 100000) (17578805261841 / 20000) := by
  exact
    packedTile32768 878911744 878977280 13 3254 29646 30 _ _ (1029709 / 50000) (2059421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell878977280 :
    ThetaLowerSegment 878977280 879042816 (17578805261841 / 20000) (8790057734013 / 10000) := by
  exact
    packedTile32768 878977280 879042816 13 3181 29647 30 _ _ (82377 / 4000) (514857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879042816 :
    ThetaLowerSegment 879042816 879108352 (8790057734013 / 10000) (2747097826748 / 3125) := by
  exact
    packedTile32768 879042816 879108352 13 3182 29648 30 _ _ (2059433 / 100000) (514859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879108352 :
    ThetaLowerSegment 879108352 879173888 (2747097826748 / 3125) (5494601234461 / 6250) := by
  exact
    packedTile32768 879108352 879173888 13 3151 29649 30 _ _ (25743 / 1250) (2059443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879173888 :
    ThetaLowerSegment 879173888 879239424 (5494601234461 / 6250) (10990013119141 / 12500) := by
  exact
    packedTile32768 879173888 879239424 13 3149 29650 30 _ _ (257431 / 12500) (2059451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879239424 :
    ThetaLowerSegment 879239424 879304960 (10990013119141 / 12500) (43963411447669 / 50000) := by
  exact
    packedTile32768 879239424 879304960 13 3262 29651 30 _ _ (411891 / 20000) (1029729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879304960 :
    ThetaLowerSegment 879304960 879370496 (43963411447669 / 50000) (43966677755987 / 50000) := by
  exact
    packedTile32768 879304960 879370496 13 3172 29653 30 _ _ (2059463 / 100000) (1029733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879370496 :
    ThetaLowerSegment 879370496 879436032 (43966677755987 / 50000) (43969935837527 / 50000) := by
  exact
    packedTile32768 879370496 879436032 13 3164 29654 30 _ _ (205947 / 10000) (2059473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879436032 :
    ThetaLowerSegment 879436032 879501568 (43969935837527 / 50000) (43973189812767 / 50000) := by
  exact
    packedTile32768 879436032 879501568 13 3160 29655 30 _ _ (1029739 / 50000) (2059481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879501568 :
    ThetaLowerSegment 879501568 879567104 (43973189812767 / 50000) (43976443799067 / 50000) := by
  exact
    packedTile32768 879501568 879567104 13 3160 29656 30 _ _ (411897 / 20000) (64359 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879567104 :
    ThetaLowerSegment 879567104 879632640 (43976443799067 / 50000) (8795946149979 / 10000) := by
  exact
    packedTile32768 879567104 879632640 13 3192 29657 30 _ _ (2059493 / 100000) (257437 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879632640 :
    ThetaLowerSegment 879632640 879698176 (8795946149979 / 10000) (8796608897079 / 10000) := by
  exact
    packedTile32768 879632640 879698176 13 3218 29658 30 _ _ (4119 / 200) (2059503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879698176 :
    ThetaLowerSegment 879698176 879763712 (8796608897079 / 10000) (43986314982511 / 50000) := by
  exact
    packedTile32768 879698176 879763712 13 3176 29659 30 _ _ (2059507 / 100000) (205951 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879763712 :
    ThetaLowerSegment 879763712 879829248 (43986314982511 / 50000) (87979238948657 / 100000) := by
  exact
    packedTile32768 879763712 879829248 13 3209 29660 30 _ _ (411903 / 20000) (1029759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879829248 :
    ThetaLowerSegment 879829248 879894784 (87979238948657 / 100000) (3519432682477 / 4000) := by
  exact
    packedTile32768 879829248 879894784 13 3194 29661 30 _ _ (1029761 / 50000) (82381 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879894784 :
    ThetaLowerSegment 879894784 879960320 (3519432682477 / 4000) (17598466271063 / 20000) := by
  exact
    packedTile32768 879894784 879960320 13 3163 29663 30 _ _ (205953 / 10000) (2059533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell879960320 :
    ThetaLowerSegment 879960320 880025856 (17598466271063 / 20000) (87998888921123 / 100000) := by
  exact
    packedTile32768 879960320 880025856 13 3184 29664 30 _ _ (2059537 / 100000) (102977 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880025856 :
    ThetaLowerSegment 880025856 880091392 (87998888921123 / 100000) (11000671803541 / 12500) := by
  exact
    packedTile32768 880025856 880091392 13 3149 29665 30 _ _ (411909 / 20000) (514887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880091392 :
    ThetaLowerSegment 880091392 880156928 (11000671803541 / 12500) (11001496654117 / 12500) := by
  exact
    packedTile32768 880091392 880156928 13 3204 29666 30 _ _ (64361 / 3125) (411911 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880156928 :
    ThetaLowerSegment 880156928 880222464 (11001496654117 / 12500) (11002314814327 / 12500) := by
  exact
    packedTile32768 880156928 880222464 13 3178 29667 30 _ _ (51489 / 2500) (2059563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880222464 :
    ThetaLowerSegment 880222464 880288000 (11002314814327 / 12500) (88025008210233 / 100000) := by
  exact
    packedTile32768 880222464 880288000 13 3151 29668 30 _ _ (2059567 / 100000) (205957 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880288000 :
    ThetaLowerSegment 880288000 880353536 (88025008210233 / 100000) (17606290111541 / 20000) := by
  exact
    packedTile32768 880288000 880353536 13 3128 29669 30 _ _ (1029787 / 50000) (2059577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880353536 :
    ThetaLowerSegment 880353536 880419072 (17606290111541 / 20000) (17607597946111 / 20000) := by
  exact
    packedTile32768 880353536 880419072 13 3175 29670 30 _ _ (1029791 / 50000) (411917 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880419072 :
    ThetaLowerSegment 880419072 880484608 (17607597946111 / 20000) (2751393202342 / 3125) := by
  exact
    packedTile32768 880419072 880484608 13 3201 29671 30 _ _ (2059589 / 100000) (257449 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880484608 :
    ThetaLowerSegment 880484608 880550144 (2751393202342 / 3125) (88050961046853 / 100000) := by
  exact
    packedTile32768 880484608 880550144 13 3097 29672 30 _ _ (2059597 / 100000) (5149 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880550144 :
    ThetaLowerSegment 880550144 880615680 (88050961046853 / 100000) (17611495114861 / 20000) := by
  exact
    packedTile32768 880550144 880615680 13 3163 29674 30 _ _ (514901 / 25000) (2059607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880615680 :
    ThetaLowerSegment 880615680 880681216 (17611495114861 / 20000) (3522563477153 / 4000) := by
  exact
    packedTile32768 880615680 880681216 13 3210 29675 30 _ _ (514903 / 25000) (411923 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880681216 :
    ThetaLowerSegment 880681216 880746752 (3522563477153 / 4000) (44035300751861 / 50000) := by
  exact
    packedTile32768 880681216 880746752 13 3163 29676 30 _ _ (2059619 / 100000) (1029811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880746752 :
    ThetaLowerSegment 880746752 880812288 (44035300751861 / 50000) (704616533383 / 800) := by
  exact
    packedTile32768 880746752 880812288 13 3139 29677 30 _ _ (2059627 / 100000) (205963 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880812288 :
    ThetaLowerSegment 880812288 880877824 (704616533383 / 800) (17616698546191 / 20000) := by
  exact
    packedTile32768 880812288 880877824 13 3120 29678 30 _ _ (1029817 / 50000) (2059637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880877824 :
    ThetaLowerSegment 880877824 880943360 (17616698546191 / 20000) (88090153609949 / 100000) := by
  exact
    packedTile32768 880877824 880943360 13 3234 29679 30 _ _ (2059641 / 100000) (514911 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell880943360 :
    ThetaLowerSegment 880943360 881008896 (88090153609949 / 100000) (17619346425771 / 20000) := by
  exact
    packedTile32768 880943360 881008896 13 3194 29680 30 _ _ (2059649 / 100000) (514913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881008896 :
    ThetaLowerSegment 881008896 881074432 (17619346425771 / 20000) (17620654307331 / 20000) := by
  exact
    packedTile32768 881008896 881074432 13 3175 29681 30 _ _ (257457 / 12500) (2059659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881074432 :
    ThetaLowerSegment 881074432 881139968 (17620654307331 / 20000) (88109817148847 / 100000) := by
  exact
    packedTile32768 881074432 881139968 13 3178 29682 30 _ _ (128729 / 6250) (2059667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881139968 :
    ThetaLowerSegment 881139968 881205504 (88109817148847 / 100000) (22029091210739 / 25000) := by
  exact
    packedTile32768 881139968 881205504 13 3179 29684 30 _ _ (2059671 / 100000) (1029837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881205504 :
    ThetaLowerSegment 881205504 881271040 (22029091210739 / 25000) (2753843141622 / 3125) := by
  exact
    packedTile32768 881205504 881271040 13 3212 29685 30 _ _ (2059679 / 100000) (1029841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881271040 :
    ThetaLowerSegment 881271040 881336576 (2753843141622 / 3125) (44064741480303 / 50000) := by
  exact
    packedTile32768 881271040 881336576 13 3157 29686 30 _ _ (1029843 / 50000) (2059689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881336576 :
    ThetaLowerSegment 881336576 881402112 (44064741480303 / 50000) (44068016393763 / 50000) := by
  exact
    packedTile32768 881336576 881402112 13 3180 29687 30 _ _ (1029847 / 50000) (2059697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881402112 :
    ThetaLowerSegment 881402112 881467648 (44068016393763 / 50000) (44071311915363 / 50000) := by
  exact
    packedTile32768 881402112 881467648 13 3200 29688 30 _ _ (2059701 / 100000) (257463 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881467648 :
    ThetaLowerSegment 881467648 881533184 (44071311915363 / 50000) (8814923137399 / 10000) := by
  exact
    packedTile32768 881467648 881533184 13 3208 29689 30 _ _ (514927 / 25000) (2059711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881533184 :
    ThetaLowerSegment 881533184 881598720 (8814923137399 / 10000) (8815582246519 / 10000) := by
  exact
    packedTile32768 881533184 881598720 13 3200 29690 30 _ _ (514929 / 25000) (2059719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881598720 :
    ThetaLowerSegment 881598720 881664256 (8815582246519 / 10000) (44081210908841 / 50000) := by
  exact
    packedTile32768 881598720 881664256 13 3204 29691 30 _ _ (2059723 / 100000) (1029863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881664256 :
    ThetaLowerSegment 881664256 881729792 (44081210908841 / 50000) (17633787349367 / 20000) := by
  exact
    packedTile32768 881664256 881729792 13 3163 29692 30 _ _ (2059731 / 100000) (1029867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881729792 :
    ThetaLowerSegment 881729792 881795328 (17633787349367 / 20000) (88175523788959 / 100000) := by
  exact
    packedTile32768 881729792 881795328 13 3198 29693 30 _ _ (1029869 / 50000) (2059741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881795328 :
    ThetaLowerSegment 881795328 881860864 (88175523788959 / 100000) (88182028466827 / 100000) := by
  exact
    packedTile32768 881795328 881860864 13 3158 29695 30 _ _ (1029873 / 50000) (2059749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881860864 :
    ThetaLowerSegment 881860864 881926400 (88182028466827 / 100000) (88188498151 / 100) := by
  exact
    packedTile32768 881860864 881926400 13 3141 29696 30 _ _ (2059753 / 100000) (514939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881926400 :
    ThetaLowerSegment 881926400 881991936 (88188498151 / 100) (2204877183081 / 2500) := by
  exact
    packedTile32768 881926400 881991936 13 3199 29697 30 _ _ (25747 / 1250) (2059763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell881991936 :
    ThetaLowerSegment 881991936 882057472 (2204877183081 / 2500) (2205039904753 / 2500) := by
  exact
    packedTile32768 881991936 882057472 13 3160 29698 30 _ _ (257471 / 12500) (2059771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882057472 :
    ThetaLowerSegment 882057472 882123008 (2205039904753 / 2500) (17641656031999 / 20000) := by
  exact
    packedTile32768 882057472 882123008 13 3245 29699 30 _ _ (82391 / 4000) (1029889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882123008 :
    ThetaLowerSegment 882123008 882188544 (17641656031999 / 20000) (551342367346 / 625) := by
  exact
    packedTile32768 882123008 882188544 13 3155 29700 30 _ _ (2059783 / 100000) (1029893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882188544 :
    ThetaLowerSegment 882188544 882254080 (551342367346 / 625) (4411063355693 / 5000) := by
  exact
    packedTile32768 882188544 882254080 13 3150 29701 30 _ _ (205979 / 10000) (2059793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882254080 :
    ThetaLowerSegment 882254080 882319616 (4411063355693 / 5000) (8822784816847 / 10000) := by
  exact
    packedTile32768 882254080 882319616 13 3195 29702 30 _ _ (1029899 / 50000) (2059801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882319616 :
    ThetaLowerSegment 882319616 882385152 (8822784816847 / 10000) (17646890792621 / 20000) := by
  exact
    packedTile32768 882319616 882385152 13 3207 29703 30 _ _ (411961 / 20000) (64369 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882385152 :
    ThetaLowerSegment 882385152 882450688 (17646890792621 / 20000) (88241041241881 / 100000) := by
  exact
    packedTile32768 882385152 882450688 13 3198 29704 30 _ _ (514953 / 25000) (411963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882450688 :
    ThetaLowerSegment 882450688 882516224 (88241041241881 / 100000) (88247574990921 / 100000) := by
  exact
    packedTile32768 882450688 882516224 13 3172 29706 30 _ _ (102991 / 5000) (2059823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882516224 :
    ThetaLowerSegment 882516224 882581760 (88247574990921 / 100000) (88254100522857 / 100000) := by
  exact
    packedTile32768 882516224 882581760 13 3168 29707 30 _ _ (2059827 / 100000) (205983 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882581760 :
    ThetaLowerSegment 882581760 882647296 (88254100522857 / 100000) (88260724952217 / 100000) := by
  exact
    packedTile32768 882581760 882647296 13 3216 29708 30 _ _ (411967 / 20000) (1029919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882647296 :
    ThetaLowerSegment 882647296 882712832 (88260724952217 / 100000) (88267372062351 / 100000) := by
  exact
    packedTile32768 882647296 882712832 13 3227 29709 30 _ _ (1029921 / 50000) (411969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882712832 :
    ThetaLowerSegment 882712832 882778368 (88267372062351 / 100000) (88274004779351 / 100000) := by
  exact
    packedTile32768 882712832 882778368 13 3220 29710 30 _ _ (41197 / 2000) (2059853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882778368 :
    ThetaLowerSegment 882778368 882843904 (88274004779351 / 100000) (22070131056689 / 25000) := by
  exact
    packedTile32768 882778368 882843904 13 3165 29711 30 _ _ (2059857 / 100000) (102993 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882843904 :
    ThetaLowerSegment 882843904 882909440 (22070131056689 / 25000) (22071773283263 / 25000) := by
  exact
    packedTile32768 882843904 882909440 13 3189 29712 30 _ _ (257483 / 12500) (2059867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882909440 :
    ThetaLowerSegment 882909440 882974976 (22071773283263 / 25000) (22073413456343 / 25000) := by
  exact
    packedTile32768 882909440 882974976 13 3185 29713 30 _ _ (64371 / 3125) (16479 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell882974976 :
    ThetaLowerSegment 882974976 883040512 (22073413456343 / 25000) (5518762765037 / 6250) := by
  exact
    packedTile32768 882974976 883040512 13 3180 29714 30 _ _ (2059879 / 100000) (1029941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883040512 :
    ThetaLowerSegment 883040512 883106048 (5518762765037 / 6250) (3532272576719 / 4000) := by
  exact
    packedTile32768 883040512 883106048 13 3209 29715 30 _ _ (2059887 / 100000) (205989 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883106048 :
    ThetaLowerSegment 883106048 883171584 (3532272576719 / 4000) (17662662676709 / 20000) := by
  exact
    packedTile32768 883106048 883171584 13 3155 29717 30 _ _ (1029947 / 50000) (2059897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883171584 :
    ThetaLowerSegment 883171584 883237120 (17662662676709 / 20000) (88319717618863 / 100000) := by
  exact
    packedTile32768 883171584 883237120 13 3109 29718 30 _ _ (1029951 / 50000) (411981 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883237120 :
    ThetaLowerSegment 883237120 883302656 (88319717618863 / 100000) (88326338166389 / 100000) := by
  exact
    packedTile32768 883237120 883302656 13 3214 29719 30 _ _ (2059909 / 100000) (257489 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883302656 :
    ThetaLowerSegment 883302656 883368192 (88326338166389 / 100000) (88332824841873 / 100000) := by
  exact
    packedTile32768 883302656 883368192 13 3149 29720 30 _ _ (514979 / 25000) (2059919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883368192 :
    ThetaLowerSegment 883368192 883433728 (88332824841873 / 100000) (88339420718521 / 100000) := by
  exact
    packedTile32768 883368192 883433728 13 3202 29721 30 _ _ (514981 / 25000) (2059927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883433728 :
    ThetaLowerSegment 883433728 883499264 (88339420718521 / 100000) (88345934220343 / 100000) := by
  exact
    packedTile32768 883433728 883499264 13 3162 29722 30 _ _ (2059931 / 100000) (1029967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883499264 :
    ThetaLowerSegment 883499264 883564800 (88345934220343 / 100000) (1104404592623 / 1250) := by
  exact
    packedTile32768 883499264 883564800 13 3123 29723 30 _ _ (2059939 / 100000) (1029971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883564800 :
    ThetaLowerSegment 883564800 883630336 (1104404592623 / 1250) (2208972950953 / 2500) := by
  exact
    packedTile32768 883564800 883630336 13 3180 29724 30 _ _ (1029973 / 50000) (2059949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883630336 :
    ThetaLowerSegment 883630336 883695872 (2208972950953 / 2500) (3534619159537 / 4000) := by
  exact
    packedTile32768 883630336 883695872 13 3185 29725 30 _ _ (2059953 / 100000) (514989 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883695872 :
    ThetaLowerSegment 883695872 883761408 (3534619159537 / 4000) (5523254300229 / 6250) := by
  exact
    packedTile32768 883695872 883761408 13 3199 29727 30 _ _ (2059961 / 100000) (514991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883761408 :
    ThetaLowerSegment 883761408 883826944 (5523254300229 / 6250) (5523663590121 / 6250) := by
  exact
    packedTile32768 883761408 883826944 13 3179 29728 30 _ _ (64374 / 3125) (2059971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883826944 :
    ThetaLowerSegment 883826944 883892480 (5523663590121 / 6250) (2762040753876 / 3125) := by
  exact
    packedTile32768 883826944 883892480 13 3246 29729 30 _ _ (257497 / 12500) (2059979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883892480 :
    ThetaLowerSegment 883892480 883958016 (2762040753876 / 3125) (88391770410669 / 100000) := by
  exact
    packedTile32768 883892480 883958016 13 3139 29730 30 _ _ (2059983 / 100000) (1029993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell883958016 :
    ThetaLowerSegment 883958016 884023552 (88391770410669 / 100000) (5524896232623 / 6250) := by
  exact
    packedTile32768 883958016 884023552 13 3189 29731 30 _ _ (2059991 / 100000) (1029997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884023552 :
    ThetaLowerSegment 884023552 884089088 (5524896232623 / 6250) (8840490905559 / 10000) := by
  exact
    packedTile32768 884023552 884089088 13 3189 29732 30 _ _ (1029999 / 50000) (2060001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884089088 :
    ThetaLowerSegment 884089088 884154624 (8840490905559 / 10000) (17682284970281 / 20000) := by
  exact
    packedTile32768 884089088 884154624 13 3163 29733 30 _ _ (412001 / 20000) (257501 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884154624 :
    ThetaLowerSegment 884154624 884220160 (17682284970281 / 20000) (44208947676119 / 50000) := by
  exact
    packedTile32768 884154624 884220160 13 3141 29734 30 _ _ (2060013 / 100000) (128751 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884220160 :
    ThetaLowerSegment 884220160 884285696 (44208947676119 / 50000) (44212236498049 / 50000) := by
  exact
    packedTile32768 884220160 884285696 13 3193 29735 30 _ _ (103001 / 5000) (2060023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884285696 :
    ThetaLowerSegment 884285696 884351232 (44212236498049 / 50000) (44215525332751 / 50000) := by
  exact
    packedTile32768 884285696 884351232 13 3193 29736 30 _ _ (515007 / 25000) (2060031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884351232 :
    ThetaLowerSegment 884351232 884416768 (44215525332751 / 50000) (11054713072319 / 12500) := by
  exact
    packedTile32768 884351232 884416768 13 3230 29738 30 _ _ (412007 / 20000) (1030019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884416768 :
    ThetaLowerSegment 884416768 884482304 (11054713072319 / 12500) (44222163806791 / 50000) := by
  exact
    packedTile32768 884416768 884482304 13 3215 29739 30 _ _ (1030021 / 50000) (412009 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884482304 :
    ThetaLowerSegment 884482304 884547840 (44222163806791 / 50000) (44225412505641 / 50000) := by
  exact
    packedTile32768 884482304 884547840 13 3154 29740 30 _ _ (41201 / 2000) (2060053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884547840 :
    ThetaLowerSegment 884547840 884613376 (44225412505641 / 50000) (442286818161 / 500) := by
  exact
    packedTile32768 884547840 884613376 13 3174 29741 30 _ _ (2060057 / 100000) (103003 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884613376 :
    ThetaLowerSegment 884613376 884678912 (442286818161 / 500) (2211598071979 / 2500) := by
  exact
    packedTile32768 884613376 884678912 13 3184 29742 30 _ _ (412013 / 20000) (515017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884678912 :
    ThetaLowerSegment 884678912 884744448 (2211598071979 / 2500) (11058806148407 / 12500) := by
  exact
    packedTile32768 884678912 884744448 13 3168 29743 30 _ _ (257509 / 12500) (82403 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884744448 :
    ThetaLowerSegment 884744448 884809984 (11058806148407 / 12500) (22119254179777 / 25000) := by
  exact
    packedTile32768 884744448 884809984 13 3188 29744 30 _ _ (2060079 / 100000) (1030041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884809984 :
    ThetaLowerSegment 884809984 884875520 (22119254179777 / 25000) (88483409169069 / 100000) := by
  exact
    packedTile32768 884809984 884875520 13 3103 29745 30 _ _ (2060087 / 100000) (206009 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884875520 :
    ThetaLowerSegment 884875520 884941056 (88483409169069 / 100000) (88489898465169 / 100000) := by
  exact
    packedTile32768 884875520 884941056 13 3150 29746 30 _ _ (1030047 / 50000) (2060097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell884941056 :
    ThetaLowerSegment 884941056 885006592 (88489898465169 / 100000) (88496478430957 / 100000) := by
  exact
    packedTile32768 884941056 885006592 13 3194 29747 30 _ _ (1030051 / 50000) (412021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885006592 :
    ThetaLowerSegment 885006592 885072128 (88496478430957 / 100000) (88502934812563 / 100000) := by
  exact
    packedTile32768 885006592 885072128 13 3134 29749 30 _ _ (2060109 / 100000) (128757 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885072128 :
    ThetaLowerSegment 885072128 885137664 (88502934812563 / 100000) (88509504522487 / 100000) := by
  exact
    packedTile32768 885072128 885137664 13 3189 29750 30 _ _ (515029 / 25000) (2060119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885137664 :
    ThetaLowerSegment 885137664 885203200 (88509504522487 / 100000) (88516086618667 / 100000) := by
  exact
    packedTile32768 885137664 885203200 13 3195 29751 30 _ _ (515031 / 25000) (2060127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885203200 :
    ThetaLowerSegment 885203200 885268736 (88516086618667 / 100000) (44261286985593 / 50000) := by
  exact
    packedTile32768 885203200 885268736 13 3149 29752 30 _ _ (2060131 / 100000) (1030067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885268736 :
    ThetaLowerSegment 885268736 885334272 (44261286985593 / 50000) (44264587328271 / 50000) := by
  exact
    packedTile32768 885268736 885334272 13 3204 29753 30 _ _ (2060139 / 100000) (1030071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885334272 :
    ThetaLowerSegment 885334272 885399808 (44264587328271 / 50000) (44267780554571 / 50000) := by
  exact
    packedTile32768 885334272 885399808 13 3100 29754 30 _ _ (1030073 / 50000) (2060149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885399808 :
    ThetaLowerSegment 885399808 885465344 (44267780554571 / 50000) (22135512647773 / 25000) := by
  exact
    packedTile32768 885399808 885465344 13 3150 29755 30 _ _ (2060153 / 100000) (515039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885465344 :
    ThetaLowerSegment 885465344 885530880 (22135512647773 / 25000) (88548562760013 / 100000) := by
  exact
    packedTile32768 885465344 885530880 13 3161 29756 30 _ _ (2060161 / 100000) (515041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885530880 :
    ThetaLowerSegment 885530880 885596416 (88548562760013 / 100000) (88555175899293 / 100000) := by
  exact
    packedTile32768 885530880 885596416 13 3210 29757 30 _ _ (257521 / 12500) (2060171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885596416 :
    ThetaLowerSegment 885596416 885661952 (88555175899293 / 100000) (88561760221789 / 100000) := by
  exact
    packedTile32768 885596416 885661952 13 3196 29758 30 _ _ (128761 / 6250) (2060179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885661952 :
    ThetaLowerSegment 885661952 885727488 (88561760221789 / 100000) (88568237437141 / 100000) := by
  exact
    packedTile32768 885661952 885727488 13 3144 29760 30 _ _ (2060183 / 100000) (1030093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885727488 :
    ThetaLowerSegment 885727488 885793024 (88568237437141 / 100000) (88574778540391 / 100000) := by
  exact
    packedTile32768 885727488 885793024 13 3175 29761 30 _ _ (206019 / 10000) (2060193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885793024 :
    ThetaLowerSegment 885793024 885858560 (88574778540391 / 100000) (88581348511813 / 100000) := by
  exact
    packedTile32768 885793024 885858560 13 3189 29762 30 _ _ (1030099 / 50000) (2060201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885858560 :
    ThetaLowerSegment 885858560 885924096 (88581348511813 / 100000) (22146970355467 / 25000) := by
  exact
    packedTile32768 885858560 885924096 13 3171 29763 30 _ _ (412041 / 20000) (128763 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885924096 :
    ThetaLowerSegment 885924096 885989632 (22146970355467 / 25000) (4429722057003 / 5000) := by
  exact
    packedTile32768 885924096 885989632 13 3184 29764 30 _ _ (2060213 / 100000) (257527 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell885989632 :
    ThetaLowerSegment 885989632 886055168 (4429722057003 / 5000) (4430053134357 / 5000) := by
  exact
    packedTile32768 885989632 886055168 13 3214 29765 30 _ _ (103011 / 5000) (2060223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886055168 :
    ThetaLowerSegment 886055168 886120704 (4430053134357 / 5000) (88607591546503 / 100000) := by
  exact
    packedTile32768 886055168 886120704 13 3169 29766 30 _ _ (2060227 / 100000) (206023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886120704 :
    ThetaLowerSegment 886120704 886186240 (88607591546503 / 100000) (44307047854199 / 50000) := by
  exact
    packedTile32768 886120704 886186240 13 3157 29767 30 _ _ (412047 / 20000) (1030119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886186240 :
    ThetaLowerSegment 886186240 886251776 (44307047854199 / 50000) (44310352482367 / 50000) := by
  exact
    packedTile32768 886186240 886251776 13 3208 29768 30 _ _ (1030121 / 50000) (412049 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886251776 :
    ThetaLowerSegment 886251776 886317312 (44310352482367 / 50000) (44313622099117 / 50000) := by
  exact
    packedTile32768 886251776 886317312 13 3174 29769 30 _ _ (8241 / 400) (2060253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886317312 :
    ThetaLowerSegment 886317312 886382848 (44313622099117 / 50000) (8863377109241 / 10000) := by
  exact
    packedTile32768 886317312 886382848 13 3168 29771 30 _ _ (2060257 / 100000) (103013 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886382848 :
    ThetaLowerSegment 886382848 886448384 (8863377109241 / 10000) (44320231414941 / 50000) := by
  exact
    packedTile32768 886382848 886448384 13 3248 29772 30 _ _ (257533 / 12500) (2060267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886448384 :
    ThetaLowerSegment 886448384 886513920 (44320231414941 / 50000) (44323496946061 / 50000) := by
  exact
    packedTile32768 886448384 886513920 13 3170 29773 30 _ _ (128767 / 6250) (82411 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886513920 :
    ThetaLowerSegment 886513920 886579456 (44323496946061 / 50000) (88653576483527 / 100000) := by
  exact
    packedTile32768 886513920 886579456 13 3195 29774 30 _ _ (2060279 / 100000) (1030141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886579456 :
    ThetaLowerSegment 886579456 886644992 (88653576483527 / 100000) (88660194125371 / 100000) := by
  exact
    packedTile32768 886579456 886644992 13 3212 29775 30 _ _ (2060287 / 100000) (206029 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886644992 :
    ThetaLowerSegment 886644992 886710528 (88660194125371 / 100000) (88666681991177 / 100000) := by
  exact
    packedTile32768 886644992 886710528 13 3149 29776 30 _ _ (1030147 / 50000) (2060297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886710528 :
    ThetaLowerSegment 886710528 886776064 (88666681991177 / 100000) (88673241989561 / 100000) := by
  exact
    packedTile32768 886710528 886776064 13 3184 29777 30 _ _ (2060301 / 100000) (128769 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886776064 :
    ThetaLowerSegment 886776064 886841600 (88673241989561 / 100000) (8867979583249 / 10000) := by
  exact
    packedTile32768 886776064 886841600 13 3181 29778 30 _ _ (2060309 / 100000) (257539 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886841600 :
    ThetaLowerSegment 886841600 886907136 (8867979583249 / 10000) (44343162486947 / 50000) := by
  exact
    packedTile32768 886841600 886907136 13 3169 29779 30 _ _ (515079 / 25000) (2060319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886907136 :
    ThetaLowerSegment 886907136 886972672 (44343162486947 / 50000) (44346431190973 / 50000) := by
  exact
    packedTile32768 886907136 886972672 13 3173 29780 30 _ _ (515081 / 25000) (2060327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell886972672 :
    ThetaLowerSegment 886972672 887038208 (44346431190973 / 50000) (5543707981289 / 6250) := by
  exact
    packedTile32768 886972672 887038208 13 3138 29782 30 _ _ (2060331 / 100000) (1030167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887038208 :
    ThetaLowerSegment 887038208 887103744 (5543707981289 / 6250) (8870595580797 / 10000) := by
  exact
    packedTile32768 887038208 887103744 13 3217 29783 30 _ _ (1030169 / 50000) (2060341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887103744 :
    ThetaLowerSegment 887103744 887169280 (8870595580797 / 10000) (22178121261111 / 25000) := by
  exact
    packedTile32768 887103744 887169280 13 3169 29784 30 _ _ (1030173 / 50000) (2060349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887169280 :
    ThetaLowerSegment 887169280 887234816 (22178121261111 / 25000) (88719034906631 / 100000) := by
  exact
    packedTile32768 887169280 887234816 13 3179 29785 30 _ _ (2060353 / 100000) (515089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887234816 :
    ThetaLowerSegment 887234816 887300352 (88719034906631 / 100000) (88725562130279 / 100000) := by
  exact
    packedTile32768 887234816 887300352 13 3168 29786 30 _ _ (2060361 / 100000) (515091 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887300352 :
    ThetaLowerSegment 887300352 887365888 (88725562130279 / 100000) (709856368867 / 800) := by
  exact
    packedTile32768 887300352 887365888 13 3147 29787 30 _ _ (128773 / 6250) (2060371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887365888 :
    ThetaLowerSegment 887365888 887431424 (709856368867 / 800) (709910301243 / 800) := by
  exact
    packedTile32768 887365888 887431424 13 3272 29788 30 _ _ (16483 / 800) (1030189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887431424 :
    ThetaLowerSegment 887431424 887496960 (709910301243 / 800) (22186326161701 / 25000) := by
  exact
    packedTile32768 887431424 887496960 13 3163 29789 30 _ _ (2060383 / 100000) (1030193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887496960 :
    ThetaLowerSegment 887496960 887562496 (22186326161701 / 25000) (44375933494477 / 50000) := by
  exact
    packedTile32768 887496960 887562496 13 3185 29790 30 _ _ (206039 / 10000) (2060393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887562496 :
    ThetaLowerSegment 887562496 887628032 (44375933494477 / 50000) (44379205404913 / 50000) := by
  exact
    packedTile32768 887562496 887628032 13 3176 29791 30 _ _ (2060397 / 100000) (5151 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887628032 :
    ThetaLowerSegment 887628032 887693568 (44379205404913 / 50000) (88765018528661 / 100000) := by
  exact
    packedTile32768 887628032 887693568 13 3207 29793 30 _ _ (412081 / 20000) (257551 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887693568 :
    ThetaLowerSegment 887693568 887759104 (88765018528661 / 100000) (17754325253989 / 20000) := by
  exact
    packedTile32768 887693568 887759104 13 3207 29794 30 _ _ (515103 / 25000) (412083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887759104 :
    ThetaLowerSegment 887759104 887824640 (17754325253989 / 20000) (17755650516133 / 20000) := by
  exact
    packedTile32768 887759104 887824640 13 3216 29795 30 _ _ (103021 / 5000) (2060423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887824640 :
    ThetaLowerSegment 887824640 887890176 (17755650516133 / 20000) (17756977431121 / 20000) := by
  exact
    packedTile32768 887824640 887890176 13 3220 29796 30 _ _ (2060427 / 100000) (206043 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887890176 :
    ThetaLowerSegment 887890176 887955712 (17756977431121 / 20000) (88791424912687 / 100000) := by
  exact
    packedTile32768 887890176 887955712 13 3173 29797 30 _ _ (1030217 / 50000) (2060437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell887955712 :
    ThetaLowerSegment 887955712 888021248 (88791424912687 / 100000) (17759590890677 / 20000) := by
  exact
    packedTile32768 887955712 888021248 13 3169 29798 30 _ _ (1030221 / 50000) (412089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888021248 :
    ThetaLowerSegment 888021248 888086784 (17759590890677 / 20000) (8880459940141 / 10000) := by
  exact
    packedTile32768 888021248 888086784 13 3225 29799 30 _ _ (2060449 / 100000) (515113 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888086784 :
    ThetaLowerSegment 888086784 888152320 (8880459940141 / 10000) (44405546980937 / 50000) := by
  exact
    packedTile32768 888086784 888152320 13 3152 29800 30 _ _ (2060457 / 100000) (103023 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888152320 :
    ThetaLowerSegment 888152320 888217856 (44405546980937 / 50000) (44408864327977 / 50000) := by
  exact
    packedTile32768 888152320 888217856 13 3220 29801 30 _ _ (128779 / 6250) (2060467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888217856 :
    ThetaLowerSegment 888217856 888283392 (44408864327977 / 50000) (2220605272443 / 2500) := by
  exact
    packedTile32768 888217856 888283392 13 3146 29802 30 _ _ (2060471 / 100000) (1030237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888283392 :
    ThetaLowerSegment 888283392 888348928 (2220605272443 / 2500) (5551918065231 / 6250) := by
  exact
    packedTile32768 888283392 888348928 13 3144 29804 30 _ _ (2060479 / 100000) (1030241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888348928 :
    ThetaLowerSegment 888348928 888414464 (5551918065231 / 6250) (44418648511149 / 50000) := by
  exact
    packedTile32768 888348928 888414464 13 3207 29805 30 _ _ (1030243 / 50000) (2060489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888414464 :
    ThetaLowerSegment 888414464 888480000 (44418648511149 / 50000) (44421904090089 / 50000) := by
  exact
    packedTile32768 888414464 888480000 13 3160 29806 30 _ _ (2060493 / 100000) (128781 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888480000 :
    ThetaLowerSegment 888480000 888545536 (44421904090089 / 50000) (44425147318663 / 50000) := by
  exact
    packedTile32768 888480000 888545536 13 3148 29807 30 _ _ (2060501 / 100000) (257563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888545536 :
    ThetaLowerSegment 888545536 888611072 (44425147318663 / 50000) (44428438980193 / 50000) := by
  exact
    packedTile32768 888545536 888611072 13 3195 29808 30 _ _ (515127 / 25000) (2060511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888611072 :
    ThetaLowerSegment 888611072 888676608 (44428438980193 / 50000) (44431732715019 / 50000) := by
  exact
    packedTile32768 888611072 888676608 13 3197 29809 30 _ _ (515129 / 25000) (2060519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888676608 :
    ThetaLowerSegment 888676608 888742144 (44431732715019 / 50000) (11108754812301 / 12500) := by
  exact
    packedTile32768 888676608 888742144 13 3190 29810 30 _ _ (2060523 / 100000) (1030263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888742144 :
    ThetaLowerSegment 888742144 888807680 (11108754812301 / 12500) (11109566661121 / 12500) := by
  exact
    packedTile32768 888742144 888807680 13 3152 29811 30 _ _ (206053 / 10000) (2060533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888807680 :
    ThetaLowerSegment 888807680 888873216 (11109566661121 / 12500) (44441601625237 / 50000) := by
  exact
    packedTile32768 888807680 888873216 13 3237 29812 30 _ _ (1030269 / 50000) (2060541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888873216 :
    ThetaLowerSegment 888873216 888938752 (44441601625237 / 50000) (88889683664499 / 100000) := by
  exact
    packedTile32768 888873216 888938752 13 3145 29813 30 _ _ (412109 / 20000) (515137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell888938752 :
    ThetaLowerSegment 888938752 889004288 (88889683664499 / 100000) (88896225917099 / 100000) := by
  exact
    packedTile32768 888938752 889004288 13 3175 29815 30 _ _ (257569 / 12500) (412111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889004288 :
    ThetaLowerSegment 889004288 889069824 (88896225917099 / 100000) (88902733165579 / 100000) := by
  exact
    packedTile32768 889004288 889069824 13 3158 29816 30 _ _ (25757 / 1250) (2060563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889069824 :
    ThetaLowerSegment 889069824 889135360 (88902733165579 / 100000) (88909252799567 / 100000) := by
  exact
    packedTile32768 889069824 889135360 13 3164 29817 30 _ _ (2060567 / 100000) (206057 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889135360 :
    ThetaLowerSegment 889135360 889200896 (88909252799567 / 100000) (88915817791517 / 100000) := by
  exact
    packedTile32768 889135360 889200896 13 3186 29818 30 _ _ (82423 / 4000) (1030289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889200896 :
    ThetaLowerSegment 889200896 889266432 (88915817791517 / 100000) (88922456986721 / 100000) := by
  exact
    packedTile32768 889200896 889266432 13 3222 29819 30 _ _ (1030291 / 50000) (412117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889266432 :
    ThetaLowerSegment 889266432 889331968 (88922456986721 / 100000) (88928968447961 / 100000) := by
  exact
    packedTile32768 889266432 889331968 13 3160 29820 30 _ _ (2060589 / 100000) (128787 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889331968 :
    ThetaLowerSegment 889331968 889397504 (88928968447961 / 100000) (44467765724703 / 50000) := by
  exact
    packedTile32768 889331968 889397504 13 3185 29821 30 _ _ (2060597 / 100000) (10303 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889397504 :
    ThetaLowerSegment 889397504 889463040 (44467765724703 / 50000) (8894197289751 / 10000) := by
  exact
    packedTile32768 889397504 889463040 13 3126 29822 30 _ _ (515151 / 25000) (2060607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889463040 :
    ThetaLowerSegment 889463040 889528576 (8894197289751 / 10000) (44474238092913 / 50000) := by
  exact
    packedTile32768 889463040 889528576 13 3156 29823 30 _ _ (2060611 / 100000) (1030307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889528576 :
    ThetaLowerSegment 889528576 889594112 (44474238092913 / 50000) (88954940347629 / 100000) := by
  exact
    packedTile32768 889528576 889594112 13 3137 29824 30 _ _ (2060619 / 100000) (1030311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889594112 :
    ThetaLowerSegment 889594112 889659648 (88954940347629 / 100000) (3558458983707 / 4000) := by
  exact
    packedTile32768 889594112 889659648 13 3171 29826 30 _ _ (1030313 / 50000) (2060629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889659648 :
    ThetaLowerSegment 889659648 889725184 (3558458983707 / 4000) (88968052133211 / 100000) := by
  exact
    packedTile32768 889659648 889725184 13 3192 29827 30 _ _ (2060633 / 100000) (515159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889725184 :
    ThetaLowerSegment 889725184 889790720 (88968052133211 / 100000) (1112182793967 / 1250) := by
  exact
    packedTile32768 889725184 889790720 13 3189 29828 30 _ _ (2060641 / 100000) (515161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889790720 :
    ThetaLowerSegment 889790720 889856256 (1112182793967 / 1250) (11122647819993 / 12500) := by
  exact
    packedTile32768 889790720 889856256 13 3183 29829 30 _ _ (257581 / 12500) (2060651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889856256 :
    ThetaLowerSegment 889856256 889921792 (11122647819993 / 12500) (11123458945711 / 12500) := by
  exact
    packedTile32768 889856256 889921792 13 3149 29830 30 _ _ (128791 / 6250) (2060659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889921792 :
    ThetaLowerSegment 889921792 889987328 (11123458945711 / 12500) (11124287332237 / 12500) := by
  exact
    packedTile32768 889921792 889987328 13 3216 29831 30 _ _ (2060663 / 100000) (1030333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell889987328 :
    ThetaLowerSegment 889987328 890052864 (11124287332237 / 12500) (44500478341333 / 50000) := by
  exact
    packedTile32768 889987328 890052864 13 3231 29832 30 _ _ (206067 / 10000) (2060673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890052864 :
    ThetaLowerSegment 890052864 890118400 (44500478341333 / 50000) (44503765122743 / 50000) := by
  exact
    packedTile32768 890052864 890118400 13 3190 29833 30 _ _ (1030339 / 50000) (2060681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890118400 :
    ThetaLowerSegment 890118400 890183936 (44503765122743 / 50000) (44507025126413 / 50000) := by
  exact
    packedTile32768 890118400 890183936 13 3164 29834 30 _ _ (412137 / 20000) (128793 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890183936 :
    ThetaLowerSegment 890183936 890249472 (44507025126413 / 50000) (44510325324651 / 50000) := by
  exact
    packedTile32768 890183936 890249472 13 3203 29835 30 _ _ (515173 / 25000) (412139 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890249472 :
    ThetaLowerSegment 890249472 890315008 (44510325324651 / 50000) (44513619353601 / 50000) := by
  exact
    packedTile32768 890249472 890315008 13 3197 29837 30 _ _ (20607 / 1000) (2060703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890315008 :
    ThetaLowerSegment 890315008 890380544 (44513619353601 / 50000) (22258440726391 / 25000) := by
  exact
    packedTile32768 890315008 890380544 13 3166 29838 30 _ _ (2060707 / 100000) (206071 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890380544 :
    ThetaLowerSegment 890380544 890446080 (22258440726391 / 25000) (44520154896971 / 50000) := by
  exact
    packedTile32768 890380544 890446080 13 3177 29839 30 _ _ (1030357 / 50000) (2060717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890446080 :
    ThetaLowerSegment 890446080 890511616 (44520154896971 / 50000) (11130863270633 / 12500) := by
  exact
    packedTile32768 890446080 890511616 13 3201 29840 30 _ _ (1030361 / 50000) (82429 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890511616 :
    ThetaLowerSegment 890511616 890577152 (11130863270633 / 12500) (89053494315677 / 100000) := by
  exact
    packedTile32768 890511616 890577152 13 3197 29841 30 _ _ (2060729 / 100000) (515183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890577152 :
    ThetaLowerSegment 890577152 890642688 (89053494315677 / 100000) (89059985637227 / 100000) := by
  exact
    packedTile32768 890577152 890642688 13 3150 29842 30 _ _ (2060737 / 100000) (103037 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890642688 :
    ThetaLowerSegment 890642688 890708224 (89059985637227 / 100000) (3562662541283 / 4000) := by
  exact
    packedTile32768 890642688 890708224 13 3192 29843 30 _ _ (257593 / 12500) (2060747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890708224 :
    ThetaLowerSegment 890708224 890773760 (3562662541283 / 4000) (89072976589187 / 100000) := by
  exact
    packedTile32768 890708224 890773760 13 3112 29844 30 _ _ (2060751 / 100000) (1030377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890773760 :
    ThetaLowerSegment 890773760 890839296 (89072976589187 / 100000) (89079496830663 / 100000) := by
  exact
    packedTile32768 890773760 890839296 13 3164 29845 30 _ _ (2060759 / 100000) (1030381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890839296 :
    ThetaLowerSegment 890839296 890904832 (89079496830663 / 100000) (89085986182797 / 100000) := by
  exact
    packedTile32768 890839296 890904832 13 3149 29846 30 _ _ (1030383 / 50000) (2060769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890904832 :
    ThetaLowerSegment 890904832 890970368 (89085986182797 / 100000) (89092671330409 / 100000) := by
  exact
    packedTile32768 890904832 890970368 13 3244 29848 30 _ _ (2060773 / 100000) (257597 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell890970368 :
    ThetaLowerSegment 890970368 891035904 (89092671330409 / 100000) (2784347098421 / 3125) := by
  exact
    packedTile32768 890970368 891035904 13 3123 29849 30 _ _ (2060781 / 100000) (128799 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891035904 :
    ThetaLowerSegment 891035904 891101440 (2784347098421 / 3125) (1113822198243 / 1250) := by
  exact
    packedTile32768 891035904 891101440 13 3236 29850 30 _ _ (515197 / 25000) (2060791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891101440 :
    ThetaLowerSegment 891101440 891166976 (1113822198243 / 1250) (8911220966143 / 10000) := by
  exact
    packedTile32768 891101440 891166976 13 3122 29851 30 _ _ (412159 / 20000) (1030399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891166976 :
    ThetaLowerSegment 891166976 891232512 (8911220966143 / 10000) (89118769197379 / 100000) := by
  exact
    packedTile32768 891166976 891232512 13 3183 29852 30 _ _ (2060803 / 100000) (1030403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891232512 :
    ThetaLowerSegment 891232512 891298048 (89118769197379 / 100000) (89125233958349 / 100000) := by
  exact
    packedTile32768 891232512 891298048 13 3137 29853 30 _ _ (206081 / 10000) (2060813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891298048 :
    ThetaLowerSegment 891298048 891363584 (89125233958349 / 100000) (2228293808063 / 2500) := by
  exact
    packedTile32768 891298048 891363584 13 3163 29854 30 _ _ (2060817 / 100000) (103041 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891363584 :
    ThetaLowerSegment 891363584 891429120 (2228293808063 / 2500) (8913833459757 / 10000) := by
  exact
    packedTile32768 891363584 891429120 13 3194 29855 30 _ _ (82433 / 4000) (515207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891429120 :
    ThetaLowerSegment 891429120 891494656 (8913833459757 / 10000) (44572406926689 / 50000) := by
  exact
    packedTile32768 891429120 891494656 13 3144 29856 30 _ _ (64401 / 3125) (412167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891494656 :
    ThetaLowerSegment 891494656 891560192 (44572406926689 / 50000) (44575634202129 / 50000) := by
  exact
    packedTile32768 891494656 891560192 13 3132 29857 30 _ _ (51521 / 2500) (2060843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891560192 :
    ThetaLowerSegment 891560192 891625728 (44575634202129 / 50000) (89157729159603 / 100000) := by
  exact
    packedTile32768 891560192 891625728 13 3135 29859 30 _ _ (2060847 / 100000) (41217 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891625728 :
    ThetaLowerSegment 891625728 891691264 (89157729159603 / 100000) (89164447543643 / 100000) := by
  exact
    packedTile32768 891625728 891691264 13 3260 29860 30 _ _ (1030427 / 50000) (2060857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891691264 :
    ThetaLowerSegment 891691264 891756800 (89164447543643 / 100000) (89170852702739 / 100000) := by
  exact
    packedTile32768 891691264 891756800 13 3108 29861 30 _ _ (1030431 / 50000) (412173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891756800 :
    ThetaLowerSegment 891756800 891822336 (89170852702739 / 100000) (44588665007003 / 50000) := by
  exact
    packedTile32768 891756800 891822336 13 3143 29862 30 _ _ (2060869 / 100000) (257609 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891822336 :
    ThetaLowerSegment 891822336 891887872 (44588665007003 / 50000) (44591893369257 / 50000) := by
  exact
    packedTile32768 891822336 891887872 13 3133 29863 30 _ _ (515219 / 25000) (2060879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891887872 :
    ThetaLowerSegment 891887872 891953408 (44591893369257 / 50000) (44595226849127 / 50000) := by
  exact
    packedTile32768 891887872 891953408 13 3235 29864 30 _ _ (515221 / 25000) (2060887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell891953408 :
    ThetaLowerSegment 891953408 892018944 (44595226849127 / 50000) (44598528396509 / 50000) := by
  exact
    packedTile32768 891953408 892018944 13 3204 29865 30 _ _ (2060891 / 100000) (1030447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892018944 :
    ThetaLowerSegment 892018944 892084480 (44598528396509 / 50000) (22300925797267 / 25000) := by
  exact
    packedTile32768 892018944 892084480 13 3225 29866 30 _ _ (1030449 / 50000) (2060901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892084480 :
    ThetaLowerSegment 892084480 892150016 (22300925797267 / 25000) (44605100612843 / 50000) := by
  exact
    packedTile32768 892084480 892150016 13 3153 29867 30 _ _ (1030453 / 50000) (2060909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892150016 :
    ThetaLowerSegment 892150016 892215552 (44605100612843 / 50000) (89216670431593 / 100000) := by
  exact
    packedTile32768 892150016 892215552 13 3139 29868 30 _ _ (2060913 / 100000) (515229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892215552 :
    ThetaLowerSegment 892215552 892281088 (89216670431593 / 100000) (89223131415793 / 100000) := by
  exact
    packedTile32768 892215552 892281088 13 3135 29869 30 _ _ (51523 / 2500) (2060923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892281088 :
    ThetaLowerSegment 892281088 892346624 (89223131415793 / 100000) (17845928377469 / 20000) := by
  exact
    packedTile32768 892281088 892346624 13 3159 29871 30 _ _ (64404 / 3125) (2060931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892346624 :
    ThetaLowerSegment 892346624 892412160 (17845928377469 / 20000) (3569449310299 / 4000) := by
  exact
    packedTile32768 892346624 892412160 13 3198 29872 30 _ _ (412187 / 20000) (1030469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892412160 :
    ThetaLowerSegment 892412160 892477696 (3569449310299 / 4000) (17848563493433 / 20000) := by
  exact
    packedTile32768 892412160 892477696 13 3195 29873 30 _ _ (1030471 / 50000) (412189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892477696 :
    ThetaLowerSegment 892477696 892543232 (17848563493433 / 20000) (17849889096473 / 20000) := by
  exact
    packedTile32768 892477696 892543232 13 3216 29874 30 _ _ (41219 / 2000) (2060953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892543232 :
    ThetaLowerSegment 892543232 892608768 (17849889096473 / 20000) (89256106495389 / 100000) := by
  exact
    packedTile32768 892543232 892608768 13 3232 29875 30 _ _ (2060957 / 100000) (12881 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892608768 :
    ThetaLowerSegment 892608768 892674304 (89256106495389 / 100000) (89262695397297 / 100000) := by
  exact
    packedTile32768 892608768 892674304 13 3197 29876 30 _ _ (515241 / 25000) (2060967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892674304 :
    ThetaLowerSegment 892674304 892739840 (89262695397297 / 100000) (89269306995473 / 100000) := by
  exact
    packedTile32768 892674304 892739840 13 3208 29877 30 _ _ (515243 / 25000) (82439 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892739840 :
    ThetaLowerSegment 892739840 892805376 (89269306995473 / 100000) (89275935103937 / 100000) := by
  exact
    packedTile32768 892739840 892805376 13 3216 29878 30 _ _ (2060979 / 100000) (1030491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892805376 :
    ThetaLowerSegment 892805376 892870912 (89275935103937 / 100000) (89282573539843 / 100000) := by
  exact
    packedTile32768 892805376 892870912 13 3221 29879 30 _ _ (1030493 / 50000) (2060989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892870912 :
    ThetaLowerSegment 892870912 892936448 (89282573539843 / 100000) (89289104829829 / 100000) := by
  exact
    packedTile32768 892870912 892936448 13 3169 29880 30 _ _ (1030497 / 50000) (2060997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell892936448 :
    ThetaLowerSegment 892936448 893001984 (89289104829829 / 100000) (3571827671561 / 4000) := by
  exact
    packedTile32768 892936448 893001984 13 3196 29882 30 _ _ (2061001 / 100000) (515251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893001984 :
    ThetaLowerSegment 893001984 893067520 (3571827671561 / 4000) (17860451219901 / 20000) := by
  exact
    packedTile32768 893001984 893067520 13 3185 29883 30 _ _ (128813 / 6250) (2061011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893067520 :
    ThetaLowerSegment 893067520 893133056 (17860451219901 / 20000) (89308909059153 / 100000) := by
  exact
    packedTile32768 893067520 893133056 13 3228 29884 30 _ _ (257627 / 12500) (2061019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893133056 :
    ThetaLowerSegment 893133056 893198592 (89308909059153 / 100000) (44657718159497 / 50000) := by
  exact
    packedTile32768 893133056 893198592 13 3167 29885 30 _ _ (2061023 / 100000) (1030513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893198592 :
    ThetaLowerSegment 893198592 893264128 (44657718159497 / 50000) (22330513571581 / 25000) := by
  exact
    packedTile32768 893198592 893264128 13 3211 29886 30 _ _ (206103 / 10000) (2061033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893264128 :
    ThetaLowerSegment 893264128 893329664 (22330513571581 / 25000) (8932856098329 / 10000) := by
  exact
    packedTile32768 893264128 893329664 13 3157 29887 30 _ _ (1030519 / 50000) (2061041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893329664 :
    ThetaLowerSegment 893329664 893395200 (8932856098329 / 10000) (8933519754819 / 10000) := by
  exact
    packedTile32768 893329664 893395200 13 3220 29888 30 _ _ (412209 / 20000) (257631 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893395200 :
    ThetaLowerSegment 893395200 893460736 (8933519754819 / 10000) (44670887182561 / 50000) := by
  exact
    packedTile32768 893395200 893460736 13 3191 29889 30 _ _ (515263 / 25000) (412211 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893460736 :
    ThetaLowerSegment 893460736 893526272 (44670887182561 / 50000) (44674149840541 / 50000) := by
  exact
    packedTile32768 893460736 893526272 13 3166 29890 30 _ _ (103053 / 5000) (2061063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893526272 :
    ThetaLowerSegment 893526272 893591808 (44674149840541 / 50000) (89354814713869 / 100000) := by
  exact
    packedTile32768 893526272 893591808 13 3161 29891 30 _ _ (2061067 / 100000) (206107 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893591808 :
    ThetaLowerSegment 893591808 893657344 (89354814713869 / 100000) (89361360684893 / 100000) := by
  exact
    packedTile32768 893591808 893657344 13 3176 29893 30 _ _ (1030537 / 50000) (2061077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893657344 :
    ThetaLowerSegment 893657344 893722880 (89361360684893 / 100000) (89367925231063 / 100000) := by
  exact
    packedTile32768 893657344 893722880 13 3185 29894 30 _ _ (1030541 / 50000) (412217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893722880 :
    ThetaLowerSegment 893722880 893788416 (89367925231063 / 100000) (44687246960853 / 50000) := by
  exact
    packedTile32768 893722880 893788416 13 3187 29895 30 _ _ (2061089 / 100000) (515273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893788416 :
    ThetaLowerSegment 893788416 893853952 (44687246960853 / 50000) (44690500400889 / 50000) := by
  exact
    packedTile32768 893788416 893853952 13 3157 29896 30 _ _ (257637 / 12500) (2061099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893853952 :
    ThetaLowerSegment 893853952 893919488 (44690500400889 / 50000) (44693787861769 / 50000) := by
  exact
    packedTile32768 893853952 893919488 13 3190 29897 30 _ _ (128819 / 6250) (2061107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893919488 :
    ThetaLowerSegment 893919488 893985024 (44693787861769 / 50000) (8939407234541 / 10000) := by
  exact
    packedTile32768 893919488 893985024 13 3152 29898 30 _ _ (2061111 / 100000) (1030557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell893985024 :
    ThetaLowerSegment 893985024 894050560 (8939407234541 / 10000) (44700309228089 / 50000) := by
  exact
    packedTile32768 893985024 894050560 13 3176 29899 30 _ _ (1030559 / 50000) (2061121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894050560 :
    ThetaLowerSegment 894050560 894116096 (44700309228089 / 50000) (8940728001541 / 10000) := by
  exact
    packedTile32768 894050560 894116096 13 3232 29900 30 _ _ (1030563 / 50000) (2061129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894116096 :
    ThetaLowerSegment 894116096 894181632 (8940728001541 / 10000) (89413758156429 / 100000) := by
  exact
    packedTile32768 894116096 894181632 13 3143 29901 30 _ _ (2061133 / 100000) (128821 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894181632 :
    ThetaLowerSegment 894181632 894247168 (89413758156429 / 100000) (89420390904949 / 100000) := by
  exact
    packedTile32768 894181632 894247168 13 3218 29902 30 _ _ (103057 / 5000) (2061143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894247168 :
    ThetaLowerSegment 894247168 894312704 (89420390904949 / 100000) (89426924744109 / 100000) := by
  exact
    packedTile32768 894247168 894312704 13 3170 29903 30 _ _ (515287 / 25000) (2061151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894312704 :
    ThetaLowerSegment 894312704 894378240 (89426924744109 / 100000) (5589586911709 / 6250) := by
  exact
    packedTile32768 894312704 894378240 13 3137 29905 30 _ _ (412231 / 20000) (1030579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894378240 :
    ThetaLowerSegment 894378240 894443776 (5589586911709 / 6250) (44719967388347 / 50000) := by
  exact
    packedTile32768 894378240 894443776 13 3175 29906 30 _ _ (1030581 / 50000) (412233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894443776 :
    ThetaLowerSegment 894443776 894509312 (44719967388347 / 50000) (44723252893327 / 50000) := by
  exact
    packedTile32768 894443776 894509312 13 3188 29907 30 _ _ (206117 / 10000) (2061173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894509312 :
    ThetaLowerSegment 894509312 894574848 (44723252893327 / 50000) (17890621547317 / 20000) := by
  exact
    packedTile32768 894509312 894574848 13 3203 29908 30 _ _ (2061177 / 100000) (103059 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894574848 :
    ThetaLowerSegment 894574848 894640384 (17890621547317 / 20000) (89459544814217 / 100000) := by
  exact
    packedTile32768 894574848 894640384 13 3123 29909 30 _ _ (64412 / 3125) (2061187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894640384 :
    ThetaLowerSegment 894640384 894705920 (89459544814217 / 100000) (89466136506233 / 100000) := by
  exact
    packedTile32768 894640384 894705920 13 3198 29910 30 _ _ (257649 / 12500) (412239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894705920 :
    ThetaLowerSegment 894705920 894771456 (89466136506233 / 100000) (2796021404233 / 3125) := by
  exact
    packedTile32768 894705920 894771456 13 3177 29911 30 _ _ (2061199 / 100000) (1030601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894771456 :
    ThetaLowerSegment 894771456 894836992 (2796021404233 / 3125) (44739651733961 / 50000) := by
  exact
    packedTile32768 894771456 894836992 13 3211 29912 30 _ _ (1030603 / 50000) (2061209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894836992 :
    ThetaLowerSegment 894836992 894902528 (44739651733961 / 50000) (44742898146011 / 50000) := by
  exact
    packedTile32768 894836992 894902528 13 3150 29913 30 _ _ (1030607 / 50000) (2061217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894902528 :
    ThetaLowerSegment 894902528 894968064 (44742898146011 / 50000) (44746167242517 / 50000) := by
  exact
    packedTile32768 894902528 894968064 13 3172 29914 30 _ _ (2061221 / 100000) (257653 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell894968064 :
    ThetaLowerSegment 894968064 895033600 (44746167242517 / 50000) (8949881086341 / 10000) := by
  exact
    packedTile32768 894968064 895033600 13 3142 29916 30 _ _ (515307 / 25000) (2061231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895033600 :
    ThetaLowerSegment 895033600 895099136 (8949881086341 / 10000) (8950521100119 / 10000) := by
  exact
    packedTile32768 895033600 895099136 13 3105 29917 30 _ _ (515309 / 25000) (2061239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895099136 :
    ThetaLowerSegment 895099136 895164672 (8950521100119 / 10000) (89511850264893 / 100000) := by
  exact
    packedTile32768 895099136 895164672 13 3221 29918 30 _ _ (2061243 / 100000) (1030623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895164672 :
    ThetaLowerSegment 895164672 895230208 (89511850264893 / 100000) (89518433897393 / 100000) := by
  exact
    packedTile32768 895164672 895230208 13 3194 29919 30 _ _ (1649 / 80) (2061253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895230208 :
    ThetaLowerSegment 895230208 895295744 (89518433897393 / 100000) (89525025800477 / 100000) := by
  exact
    packedTile32768 895230208 895295744 13 3198 29920 30 _ _ (1030629 / 50000) (2061261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895295744 :
    ThetaLowerSegment 895295744 895361280 (89525025800477 / 100000) (89531584745707 / 100000) := by
  exact
    packedTile32768 895295744 895361280 13 3182 29921 30 _ _ (412253 / 20000) (515317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895361280 :
    ThetaLowerSegment 895361280 895426816 (89531584745707 / 100000) (89537991179083 / 100000) := by
  exact
    packedTile32768 895361280 895426816 13 3108 29922 30 _ _ (257659 / 12500) (82451 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895426816 :
    ThetaLowerSegment 895426816 895492352 (89537991179083 / 100000) (89544566662283 / 100000) := by
  exact
    packedTile32768 895426816 895492352 13 3190 29923 30 _ _ (12883 / 625) (2061283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895492352 :
    ThetaLowerSegment 895492352 895557888 (89544566662283 / 100000) (44775574175837 / 50000) := by
  exact
    packedTile32768 895492352 895557888 13 3193 29924 30 _ _ (2061287 / 100000) (206129 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895557888 :
    ThetaLowerSegment 895557888 895623424 (44775574175837 / 50000) (8955767028589 / 10000) := by
  exact
    packedTile32768 895557888 895623424 13 3164 29925 30 _ _ (1030647 / 50000) (2061297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895623424 :
    ThetaLowerSegment 895623424 895688960 (8955767028589 / 10000) (895641736937 / 1000) := by
  exact
    packedTile32768 895623424 895688960 13 3155 29926 30 _ _ (1030651 / 50000) (412261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895688960 :
    ThetaLowerSegment 895688960 895754496 (895641736937 / 1000) (89570710104539 / 100000) := by
  exact
    packedTile32768 895688960 895754496 13 3171 29928 30 _ _ (2061309 / 100000) (64416 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895754496 :
    ThetaLowerSegment 895754496 895820032 (89570710104539 / 100000) (89577314561003 / 100000) := by
  exact
    packedTile32768 895754496 895820032 13 3204 29929 30 _ _ (515329 / 25000) (2061319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895820032 :
    ThetaLowerSegment 895820032 895885568 (89577314561003 / 100000) (89583873693971 / 100000) := by
  exact
    packedTile32768 895820032 895885568 13 3182 29930 30 _ _ (515331 / 25000) (2061327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895885568 :
    ThetaLowerSegment 895885568 895951104 (89583873693971 / 100000) (89590502934467 / 100000) := by
  exact
    packedTile32768 895885568 895951104 13 3216 29931 30 _ _ (2061331 / 100000) (1030667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell895951104 :
    ThetaLowerSegment 895951104 896016640 (89590502934467 / 100000) (89597072418673 / 100000) := by
  exact
    packedTile32768 895951104 896016640 13 3187 29932 30 _ _ (1030669 / 50000) (2061341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896016640 :
    ThetaLowerSegment 896016640 896082176 (89597072418673 / 100000) (44801748815519 / 50000) := by
  exact
    packedTile32768 896016640 896082176 13 3117 29933 30 _ _ (412269 / 20000) (515337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896082176 :
    ThetaLowerSegment 896082176 896147712 (44801748815519 / 50000) (17922014257151 / 20000) := by
  exact
    packedTile32768 896082176 896147712 13 3189 29934 30 _ _ (2061353 / 100000) (515339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896147712 :
    ThetaLowerSegment 896147712 896213248 (17922014257151 / 20000) (17923324457567 / 20000) := by
  exact
    packedTile32768 896147712 896213248 13 3178 29935 30 _ _ (25767 / 1250) (2061363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896213248 :
    ThetaLowerSegment 896213248 896278784 (17923324457567 / 20000) (89623193925831 / 100000) := by
  exact
    packedTile32768 896213248 896278784 13 3188 29936 30 _ _ (2061367 / 100000) (206137 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896278784 :
    ThetaLowerSegment 896278784 896344320 (89623193925831 / 100000) (22407412022739 / 25000) := by
  exact
    packedTile32768 896278784 896344320 13 3131 29937 30 _ _ (16491 / 800) (1030689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896344320 :
    ThetaLowerSegment 896344320 896409856 (22407412022739 / 25000) (44818106796313 / 50000) := by
  exact
    packedTile32768 896344320 896409856 13 3185 29939 30 _ _ (1030691 / 50000) (412277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896409856 :
    ThetaLowerSegment 896409856 896475392 (44818106796313 / 50000) (22410682926161 / 25000) := by
  exact
    packedTile32768 896409856 896475392 13 3162 29940 30 _ _ (2061389 / 100000) (128837 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896475392 :
    ThetaLowerSegment 896475392 896540928 (22410682926161 / 25000) (44824699131271 / 50000) := by
  exact
    packedTile32768 896475392 896540928 13 3234 29941 30 _ _ (2061397 / 100000) (10307 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896540928 :
    ThetaLowerSegment 896540928 896606464 (44824699131271 / 50000) (8965587519391 / 10000) := by
  exact
    packedTile32768 896540928 896606464 13 3142 29942 30 _ _ (515351 / 25000) (2061407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896606464 :
    ThetaLowerSegment 896606464 896672000 (8965587519391 / 10000) (89662341840217 / 100000) := by
  exact
    packedTile32768 896606464 896672000 13 3137 29943 30 _ _ (2061411 / 100000) (1030707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896672000 :
    ThetaLowerSegment 896672000 896737536 (89662341840217 / 100000) (17933796746447 / 20000) := by
  exact
    packedTile32768 896672000 896737536 13 3222 29944 30 _ _ (2061419 / 100000) (1030711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896737536 :
    ThetaLowerSegment 896737536 896803072 (17933796746447 / 20000) (89675473101283 / 100000) := by
  exact
    packedTile32768 896737536 896803072 13 3148 29945 30 _ _ (1030713 / 50000) (2061429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896803072 :
    ThetaLowerSegment 896803072 896868608 (89675473101283 / 100000) (89682049072553 / 100000) := by
  exact
    packedTile32768 896803072 896868608 13 3190 29946 30 _ _ (2061433 / 100000) (515359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896868608 :
    ThetaLowerSegment 896868608 896934144 (89682049072553 / 100000) (89688600328873 / 100000) := by
  exact
    packedTile32768 896868608 896934144 13 3178 29947 30 _ _ (12884 / 625) (2061443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896934144 :
    ThetaLowerSegment 896934144 896999680 (89688600328873 / 100000) (89695089767177 / 100000) := by
  exact
    packedTile32768 896934144 896999680 13 3148 29948 30 _ _ (257681 / 12500) (2061451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell896999680 :
    ThetaLowerSegment 896999680 897065216 (89695089767177 / 100000) (44850858672501 / 50000) := by
  exact
    packedTile32768 896999680 897065216 13 3215 29949 30 _ _ (412291 / 20000) (1030729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897065216 :
    ThetaLowerSegment 897065216 897130752 (44850858672501 / 50000) (22427069744637 / 25000) := by
  exact
    packedTile32768 897065216 897130752 13 3183 29951 30 _ _ (1030731 / 50000) (412293 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897130752 :
    ThetaLowerSegment 897130752 897196288 (22427069744637 / 25000) (44857405888489 / 50000) := by
  exact
    packedTile32768 897130752 897196288 13 3169 29952 30 _ _ (206147 / 10000) (2061473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897196288 :
    ThetaLowerSegment 897196288 897261824 (44857405888489 / 50000) (89721406441901 / 100000) := by
  exact
    packedTile32768 897196288 897261824 13 3199 29953 30 _ _ (2061477 / 100000) (51537 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897261824 :
    ThetaLowerSegment 897261824 897327360 (89721406441901 / 100000) (89727918669857 / 100000) := by
  exact
    packedTile32768 897261824 897327360 13 3159 29954 30 _ _ (515371 / 25000) (2061487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897327360 :
    ThetaLowerSegment 897327360 897392896 (89727918669857 / 100000) (17946890307601 / 20000) := by
  exact
    packedTile32768 897327360 897392896 13 3169 29955 30 _ _ (515373 / 25000) (412299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897392896 :
    ThetaLowerSegment 897392896 897458432 (17946890307601 / 20000) (17948184928973 / 20000) := by
  exact
    packedTile32768 897392896 897458432 13 3140 29956 30 _ _ (2061499 / 100000) (1030751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897458432 :
    ThetaLowerSegment 897458432 897523968 (17948184928973 / 20000) (89747443126837 / 100000) := by
  exact
    packedTile32768 897458432 897523968 13 3162 29957 30 _ _ (1030753 / 50000) (2061509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897523968 :
    ThetaLowerSegment 897523968 897589504 (89747443126837 / 100000) (89754027602553 / 100000) := by
  exact
    packedTile32768 897523968 897589504 13 3194 29958 30 _ _ (1030757 / 50000) (2061517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897589504 :
    ThetaLowerSegment 897589504 897655040 (89754027602553 / 100000) (4488029883499 / 5000) := by
  exact
    packedTile32768 897589504 897655040 13 3187 29959 30 _ _ (2061521 / 100000) (515381 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897655040 :
    ThetaLowerSegment 897655040 897720576 (4488029883499 / 5000) (22441788847637 / 25000) := by
  exact
    packedTile32768 897655040 897720576 13 3181 29960 30 _ _ (257691 / 12500) (2061531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897720576 :
    ThetaLowerSegment 897720576 897786112 (22441788847637 / 25000) (44886898828159 / 50000) := by
  exact
    packedTile32768 897720576 897786112 13 3222 29961 30 _ _ (412307 / 20000) (1030769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897786112 :
    ThetaLowerSegment 897786112 897851648 (44886898828159 / 50000) (448901704969 / 500) := by
  exact
    packedTile32768 897786112 897851648 13 3174 29963 30 _ _ (2061543 / 100000) (1030773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897851648 :
    ThetaLowerSegment 897851648 897917184 (448901704969 / 500) (897868266301 / 1000) := by
  exact
    packedTile32768 897851648 897917184 13 3146 29964 30 _ _ (41231 / 2000) (2061553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897917184 :
    ThetaLowerSegment 897917184 897982720 (897868266301 / 1000) (8979336176579 / 10000) := by
  exact
    packedTile32768 897917184 897982720 13 3170 29965 30 _ _ (2061557 / 100000) (51539 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell897982720 :
    ThetaLowerSegment 897982720 898048256 (8979336176579 / 10000) (4489994434029 / 5000) := by
  exact
    packedTile32768 897982720 898048256 13 3166 29966 30 _ _ (412313 / 20000) (64424 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898048256 :
    ThetaLowerSegment 898048256 898113792 (4489994434029 / 5000) (11225809940783 / 12500) := by
  exact
    packedTile32768 898048256 898113792 13 3197 29967 30 _ _ (515393 / 25000) (82463 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898113792 :
    ThetaLowerSegment 898113792 898179328 (11225809940783 / 12500) (44906507365847 / 50000) := by
  exact
    packedTile32768 898113792 898179328 13 3170 29968 30 _ _ (2061579 / 100000) (1030791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898179328 :
    ThetaLowerSegment 898179328 898244864 (44906507365847 / 50000) (17963911229449 / 20000) := by
  exact
    packedTile32768 898179328 898244864 13 3173 29969 30 _ _ (2061587 / 100000) (206159 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898244864 :
    ThetaLowerSegment 898244864 898310400 (17963911229449 / 20000) (3593043656009 / 4000) := by
  exact
    packedTile32768 898244864 898310400 13 3170 29970 30 _ _ (1030797 / 50000) (2061597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898310400 :
    ThetaLowerSegment 898310400 898375936 (3593043656009 / 4000) (44916374154927 / 50000) := by
  exact
    packedTile32768 898310400 898375936 13 3229 29971 30 _ _ (2061601 / 100000) (515401 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898375936 :
    ThetaLowerSegment 898375936 898441472 (44916374154927 / 50000) (8983941142691 / 10000) := by
  exact
    packedTile32768 898375936 898441472 13 3232 29972 30 _ _ (257701 / 12500) (2061611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898441472 :
    ThetaLowerSegment 898441472 898507008 (8983941142691 / 10000) (44922974405623 / 50000) := by
  exact
    packedTile32768 898441472 898507008 13 3171 29974 30 _ _ (128851 / 6250) (2061619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898507008 :
    ThetaLowerSegment 898507008 898572544 (44922974405623 / 50000) (8985248003291 / 10000) := by
  exact
    packedTile32768 898507008 898572544 13 3168 29975 30 _ _ (2061623 / 100000) (1030813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898572544 :
    ThetaLowerSegment 898572544 898638080 (8985248003291 / 10000) (1123237202863 / 1250) := by
  exact
    packedTile32768 898572544 898638080 13 3151 29976 30 _ _ (206163 / 10000) (2061633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898638080 :
    ThetaLowerSegment 898638080 898703616 (1123237202863 / 1250) (5616594218639 / 6250) := by
  exact
    packedTile32768 898638080 898703616 13 3168 29977 30 _ _ (1030819 / 50000) (2061641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898703616 :
    ThetaLowerSegment 898703616 898769152 (5616594218639 / 6250) (22467991142591 / 25000) := by
  exact
    packedTile32768 898703616 898769152 13 3132 29978 30 _ _ (412329 / 20000) (128853 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898769152 :
    ThetaLowerSegment 898769152 898834688 (22467991142591 / 25000) (5617405090771 / 6250) := by
  exact
    packedTile32768 898769152 898834688 13 3161 29979 30 _ _ (515413 / 25000) (412331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898834688 :
    ThetaLowerSegment 898834688 898900224 (5617405090771 / 6250) (22471242888717 / 25000) := by
  exact
    packedTile32768 898834688 898900224 13 3148 29980 30 _ _ (2061659 / 100000) (1030831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898900224 :
    ThetaLowerSegment 898900224 898965760 (22471242888717 / 25000) (22472896345651 / 25000) := by
  exact
    packedTile32768 898900224 898965760 13 3208 29981 30 _ _ (2061667 / 100000) (206167 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell898965760 :
    ThetaLowerSegment 898965760 899031296 (22472896345651 / 25000) (44949115078953 / 50000) := by
  exact
    packedTile32768 898965760 899031296 13 3223 29982 30 _ _ (1030837 / 50000) (2061677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899031296 :
    ThetaLowerSegment 899031296 899096832 (44949115078953 / 50000) (89904697651203 / 100000) := by
  exact
    packedTile32768 899031296 899096832 13 3137 29983 30 _ _ (2061681 / 100000) (515421 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899096832 :
    ThetaLowerSegment 899096832 899162368 (89904697651203 / 100000) (44955634127023 / 50000) := by
  exact
    packedTile32768 899096832 899162368 13 3187 29984 30 _ _ (2061689 / 100000) (515423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899162368 :
    ThetaLowerSegment 899162368 899227904 (44955634127023 / 50000) (8991783269411 / 10000) := by
  exact
    packedTile32768 899162368 899227904 13 3184 29986 30 _ _ (64428 / 3125) (2061699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899227904 :
    ThetaLowerSegment 899227904 899293440 (8991783269411 / 10000) (89924374477729 / 100000) := by
  exact
    packedTile32768 899227904 899293440 13 3173 29987 30 _ _ (2061703 / 100000) (1030853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899293440 :
    ThetaLowerSegment 899293440 899358976 (89924374477729 / 100000) (89930965764599 / 100000) := by
  exact
    packedTile32768 899293440 899358976 13 3197 29988 30 _ _ (206171 / 10000) (2061713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899358976 :
    ThetaLowerSegment 899358976 899424512 (89930965764599 / 100000) (89937534398147 / 100000) := by
  exact
    packedTile32768 899358976 899424512 13 3186 29989 30 _ _ (1030859 / 50000) (2061721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899424512 :
    ThetaLowerSegment 899424512 899490048 (89937534398147 / 100000) (44972015446811 / 50000) := by
  exact
    packedTile32768 899424512 899490048 13 3151 29990 30 _ _ (82469 / 4000) (64429 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899490048 :
    ThetaLowerSegment 899490048 899555584 (44972015446811 / 50000) (44975268859907 / 50000) := by
  exact
    packedTile32768 899490048 899555584 13 3156 29991 30 _ _ (515433 / 25000) (412347 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899555584 :
    ThetaLowerSegment 899555584 899621120 (44975268859907 / 50000) (44978564551297 / 50000) := by
  exact
    packedTile32768 899555584 899621120 13 3197 29992 30 _ _ (103087 / 5000) (2061743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899621120 :
    ThetaLowerSegment 899621120 899686656 (44978564551297 / 50000) (44981826235051 / 50000) := by
  exact
    packedTile32768 899621120 899686656 13 3164 29993 30 _ _ (2061747 / 100000) (8247 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899686656 :
    ThetaLowerSegment 899686656 899752192 (44981826235051 / 50000) (44985050818307 / 50000) := by
  exact
    packedTile32768 899686656 899752192 13 3128 29994 30 _ _ (1030877 / 50000) (2061757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899752192 :
    ThetaLowerSegment 899752192 899817728 (44985050818307 / 50000) (8997669102477 / 10000) := by
  exact
    packedTile32768 899752192 899817728 13 3196 29995 30 _ _ (2061761 / 100000) (515441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899817728 :
    ThetaLowerSegment 899817728 899883264 (8997669102477 / 10000) (89983043335059 / 100000) := by
  exact
    packedTile32768 899817728 899883264 13 3081 29996 30 _ _ (2061769 / 100000) (515443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899883264 :
    ThetaLowerSegment 899883264 899948800 (89983043335059 / 100000) (89989583288531 / 100000) := by
  exact
    packedTile32768 899883264 899948800 13 3172 29998 30 _ _ (128861 / 6250) (2061779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell899948800 :
    ThetaLowerSegment 899948800 900014336 (89989583288531 / 100000) (11249535768133 / 12500) := by
  exact
    packedTile32768 899948800 900014336 13 3251 29999 30 _ _ (2061783 / 100000) (1030893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900014336 :
    ThetaLowerSegment 900014336 900079872 (11249535768133 / 12500) (4500139657873 / 5000) := by
  exact
    packedTile32768 900014336 900079872 13 3156 30000 30 _ _ (2061791 / 100000) (1030897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900079872 :
    ThetaLowerSegment 900079872 900145408 (4500139657873 / 5000) (900093496751 / 1000) := by
  exact
    packedTile32768 900079872 900145408 13 3180 30001 30 _ _ (1030899 / 50000) (2061801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900145408 :
    ThetaLowerSegment 900145408 900210944 (900093496751 / 1000) (18003180830639 / 20000) := by
  exact
    packedTile32768 900145408 900210944 13 3179 30002 30 _ _ (412361 / 20000) (128863 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900210944 :
    ThetaLowerSegment 900210944 900276480 (18003180830639 / 20000) (90022446282671 / 100000) := by
  exact
    packedTile32768 900210944 900276480 13 3173 30003 30 _ _ (515453 / 25000) (412363 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900276480 :
    ThetaLowerSegment 900276480 900342016 (90022446282671 / 100000) (90029077095791 / 100000) := by
  exact
    packedTile32768 900276480 900342016 13 3216 30004 30 _ _ (103091 / 5000) (2061823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900342016 :
    ThetaLowerSegment 900342016 900407552 (90029077095791 / 100000) (3601426337903 / 4000) := by
  exact
    packedTile32768 900342016 900407552 13 3192 30005 30 _ _ (2061827 / 100000) (206183 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900407552 :
    ThetaLowerSegment 900407552 900473088 (3601426337903 / 4000) (90042353222573 / 100000) := by
  exact
    packedTile32768 900407552 900473088 13 3247 30006 30 _ _ (1030917 / 50000) (2061837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900473088 :
    ThetaLowerSegment 900473088 900538624 (90042353222573 / 100000) (90048924313027 / 100000) := by
  exact
    packedTile32768 900473088 900538624 13 3187 30007 30 _ _ (1030921 / 50000) (412369 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900538624 :
    ThetaLowerSegment 900538624 900604160 (90048924313027 / 100000) (11256927134441 / 12500) := by
  exact
    packedTile32768 900538624 900604160 13 3149 30008 30 _ _ (2061849 / 100000) (515463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900604160 :
    ThetaLowerSegment 900604160 900669696 (11256927134441 / 12500) (11257762959317 / 12500) := by
  exact
    packedTile32768 900604160 900669696 13 3243 30010 30 _ _ (64433 / 3125) (2061859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900669696 :
    ThetaLowerSegment 900669696 900735232 (11257762959317 / 12500) (90068596481123 / 100000) := by
  exact
    packedTile32768 900669696 900735232 13 3149 30011 30 _ _ (2061863 / 100000) (1030933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900735232 :
    ThetaLowerSegment 900735232 900800768 (90068596481123 / 100000) (22518791916 / 25) := by
  exact
    packedTile32768 900735232 900800768 13 3187 30012 30 _ _ (2061871 / 100000) (1030937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900800768 :
    ThetaLowerSegment 900800768 900866304 (22518791916 / 25) (45040861187081 / 50000) := by
  exact
    packedTile32768 900800768 900866304 13 3179 30013 30 _ _ (1030939 / 50000) (2061881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900866304 :
    ThetaLowerSegment 900866304 900931840 (45040861187081 / 50000) (45044118965381 / 50000) := by
  exact
    packedTile32768 900866304 900931840 13 3160 30014 30 _ _ (412377 / 20000) (64434 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900931840 :
    ThetaLowerSegment 900931840 900997376 (45044118965381 / 50000) (45047467479613 / 50000) := by
  exact
    packedTile32768 900931840 900997376 13 3248 30015 30 _ _ (2061893 / 100000) (257737 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell900997376 :
    ThetaLowerSegment 900997376 901062912 (45047467479613 / 50000) (45050778891013 / 50000) := by
  exact
    packedTile32768 900997376 901062912 13 3212 30016 30 _ _ (20619 / 1000) (2061903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901062912 :
    ThetaLowerSegment 901062912 901128448 (45050778891013 / 50000) (45054044951701 / 50000) := by
  exact
    packedTile32768 901062912 901128448 13 3168 30017 30 _ _ (2061907 / 100000) (206191 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901128448 :
    ThetaLowerSegment 901128448 901193984 (45054044951701 / 50000) (22528651903389 / 25000) := by
  exact
    packedTile32768 901128448 901193984 13 3161 30018 30 _ _ (1030957 / 50000) (2061917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901193984 :
    ThetaLowerSegment 901193984 901259520 (22528651903389 / 25000) (450606049439 / 500) := by
  exact
    packedTile32768 901193984 901259520 13 3202 30019 30 _ _ (1030961 / 50000) (82477 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901259520 :
    ThetaLowerSegment 901259520 901325056 (450606049439 / 500) (2816492455447 / 3125) := by
  exact
    packedTile32768 901259520 901325056 13 3176 30020 30 _ _ (2061929 / 100000) (515483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901325056 :
    ThetaLowerSegment 901325056 901390592 (2816492455447 / 3125) (2816696329369 / 3125) := by
  exact
    packedTile32768 901325056 901390592 13 3164 30022 30 _ _ (128871 / 6250) (2061939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901390592 :
    ThetaLowerSegment 901390592 901456128 (2816696329369 / 3125) (90140886943237 / 100000) := by
  exact
    packedTile32768 901390592 901456128 13 3203 30023 30 _ _ (2061943 / 100000) (1030973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901456128 :
    ThetaLowerSegment 901456128 901521664 (90140886943237 / 100000) (90147369717181 / 100000) := by
  exact
    packedTile32768 901456128 901521664 13 3144 30024 30 _ _ (2061951 / 100000) (1030977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901521664 :
    ThetaLowerSegment 901521664 901587200 (90147369717181 / 100000) (90153885504461 / 100000) := by
  exact
    packedTile32768 901521664 901587200 13 3160 30025 30 _ _ (1030979 / 50000) (2061961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901587200 :
    ThetaLowerSegment 901587200 901652736 (90153885504461 / 100000) (90160512659971 / 100000) := by
  exact
    packedTile32768 901587200 901652736 13 3214 30026 30 _ _ (412393 / 20000) (128873 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901652736 :
    ThetaLowerSegment 901652736 901718272 (90160512659971 / 100000) (90167090353841 / 100000) := by
  exact
    packedTile32768 901652736 901718272 13 3190 30027 30 _ _ (2061973 / 100000) (257747 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901718272 :
    ThetaLowerSegment 901718272 901783808 (90167090353841 / 100000) (90173688689841 / 100000) := by
  exact
    packedTile32768 901718272 901783808 13 3200 30028 30 _ _ (103099 / 5000) (2061983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901783808 :
    ThetaLowerSegment 901783808 901849344 (90173688689841 / 100000) (45090105377361 / 50000) := by
  exact
    packedTile32768 901783808 901849344 13 3163 30029 30 _ _ (2061987 / 100000) (206199 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901849344 :
    ThetaLowerSegment 901849344 901914880 (45090105377361 / 50000) (11273359132167 / 12500) := by
  exact
    packedTile32768 901849344 901914880 13 3231 30030 30 _ _ (1030997 / 50000) (2061997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901914880 :
    ThetaLowerSegment 901914880 901980416 (11273359132167 / 12500) (45096666654801 / 50000) := by
  exact
    packedTile32768 901914880 901980416 13 3133 30031 30 _ _ (1031001 / 50000) (412401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell901980416 :
    ThetaLowerSegment 901980416 902045952 (45096666654801 / 50000) (90199830699961 / 100000) := by
  exact
    packedTile32768 901980416 902045952 13 3151 30032 30 _ _ (2062009 / 100000) (515503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902045952 :
    ThetaLowerSegment 902045952 902111488 (90199830699961 / 100000) (90206309554233 / 100000) := by
  exact
    packedTile32768 902045952 902111488 13 3142 30034 30 _ _ (64438 / 3125) (2062019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902111488 :
    ThetaLowerSegment 902111488 902177024 (90206309554233 / 100000) (90212920399971 / 100000) := by
  exact
    packedTile32768 902111488 902177024 13 3206 30035 30 _ _ (2062023 / 100000) (1031013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902177024 :
    ThetaLowerSegment 902177024 902242560 (90212920399971 / 100000) (90219271455451 / 100000) := by
  exact
    packedTile32768 902177024 902242560 13 3080 30036 30 _ _ (2062031 / 100000) (1031017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902242560 :
    ThetaLowerSegment 902242560 902308096 (90219271455451 / 100000) (90225812239987 / 100000) := by
  exact
    packedTile32768 902242560 902308096 13 3172 30037 30 _ _ (1031019 / 50000) (2062041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902308096 :
    ThetaLowerSegment 902308096 902373632 (90225812239987 / 100000) (45116179616431 / 50000) := by
  exact
    packedTile32768 902308096 902373632 13 3175 30038 30 _ _ (412409 / 20000) (64439 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902373632 :
    ThetaLowerSegment 902373632 902439168 (45116179616431 / 50000) (45119456217059 / 50000) := by
  exact
    packedTile32768 902373632 902439168 13 3178 30039 30 _ _ (515513 / 25000) (412411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902439168 :
    ThetaLowerSegment 902439168 902504704 (45119456217059 / 50000) (45122669937569 / 50000) := by
  exact
    packedTile32768 902439168 902504704 13 3117 30040 30 _ _ (103103 / 5000) (2062063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902504704 :
    ThetaLowerSegment 902504704 902570240 (45122669937569 / 50000) (5640745382321 / 6250) := by
  exact
    packedTile32768 902504704 902570240 13 3194 30041 30 _ _ (2062067 / 100000) (206207 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902570240 :
    ThetaLowerSegment 902570240 902635776 (5640745382321 / 6250) (45129236601043 / 50000) := by
  exact
    packedTile32768 902570240 902635776 13 3175 30042 30 _ _ (1031037 / 50000) (2062077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902635776 :
    ThetaLowerSegment 902635776 902701312 (45129236601043 / 50000) (90264921329373 / 100000) := by
  exact
    packedTile32768 902635776 902701312 13 3127 30043 30 _ _ (2062081 / 100000) (515521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902701312 :
    ThetaLowerSegment 902701312 902766848 (90264921329373 / 100000) (90271322053629 / 100000) := by
  exact
    packedTile32768 902701312 902766848 13 3104 30044 30 _ _ (2062089 / 100000) (515523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902766848 :
    ThetaLowerSegment 902766848 902832384 (90271322053629 / 100000) (90277962002749 / 100000) := by
  exact
    packedTile32768 902766848 902832384 13 3220 30046 30 _ _ (128881 / 6250) (2062099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902832384 :
    ThetaLowerSegment 902832384 902897920 (90277962002749 / 100000) (22571115953377 / 25000) := by
  exact
    packedTile32768 902832384 902897920 13 3153 30047 30 _ _ (2062103 / 100000) (1031053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902897920 :
    ThetaLowerSegment 902897920 902963456 (22571115953377 / 25000) (90290978022157 / 100000) := by
  exact
    packedTile32768 902897920 902963456 13 3159 30048 30 _ _ (2062111 / 100000) (1031057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell902963456 :
    ThetaLowerSegment 902963456 903028992 (90290978022157 / 100000) (90297541743751 / 100000) := by
  exact
    packedTile32768 902963456 903028992 13 3183 30049 30 _ _ (1031059 / 50000) (2062121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903028992 :
    ThetaLowerSegment 903028992 903094528 (90297541743751 / 100000) (90304095177001 / 100000) := by
  exact
    packedTile32768 903028992 903094528 13 3178 30050 30 _ _ (16497 / 800) (128883 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903094528 :
    ThetaLowerSegment 903094528 903160064 (90304095177001 / 100000) (90310726993513 / 100000) := by
  exact
    packedTile32768 903094528 903160064 13 3216 30051 30 _ _ (515533 / 25000) (412427 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903160064 :
    ThetaLowerSegment 903160064 903225600 (90310726993513 / 100000) (90317220672373 / 100000) := by
  exact
    packedTile32768 903160064 903225600 13 3149 30052 30 _ _ (103107 / 5000) (2062143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903225600 :
    ThetaLowerSegment 903225600 903291136 (90317220672373 / 100000) (90323963893063 / 100000) := by
  exact
    packedTile32768 903225600 903291136 13 3270 30053 30 _ _ (2062147 / 100000) (41243 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903291136 :
    ThetaLowerSegment 903291136 903356672 (90323963893063 / 100000) (90330583407403 / 100000) := by
  exact
    packedTile32768 903291136 903356672 13 3210 30054 30 _ _ (1031077 / 50000) (2062157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903356672 :
    ThetaLowerSegment 903356672 903422208 (90330583407403 / 100000) (45168623124797 / 50000) := by
  exact
    packedTile32768 903356672 903422208 13 3231 30055 30 _ _ (2062161 / 100000) (515541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903422208 :
    ThetaLowerSegment 903422208 903487744 (45168623124797 / 50000) (90343744144113 / 100000) := by
  exact
    packedTile32768 903422208 903487744 13 3151 30056 30 _ _ (2062169 / 100000) (515543 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903487744 :
    ThetaLowerSegment 903487744 903553280 (90343744144113 / 100000) (90350237936337 / 100000) := by
  exact
    packedTile32768 903487744 903553280 13 3149 30058 30 _ _ (64443 / 3125) (2062179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903553280 :
    ThetaLowerSegment 903553280 903618816 (90350237936337 / 100000) (90356820424473 / 100000) := by
  exact
    packedTile32768 903553280 903618816 13 3192 30059 30 _ _ (2062183 / 100000) (1031093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903618816 :
    ThetaLowerSegment 903618816 903684352 (90356820424473 / 100000) (90363349318013 / 100000) := by
  exact
    packedTile32768 903618816 903684352 13 3166 30060 30 _ _ (206219 / 10000) (2062193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903684352 :
    ThetaLowerSegment 903684352 903749888 (90363349318013 / 100000) (18073985133487 / 20000) := by
  exact
    packedTile32768 903684352 903749888 13 3189 30061 30 _ _ (1031099 / 50000) (2062201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903749888 :
    ThetaLowerSegment 903749888 903815424 (18073985133487 / 20000) (18075302470041 / 20000) := by
  exact
    packedTile32768 903749888 903815424 13 3194 30062 30 _ _ (412441 / 20000) (64444 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903815424 :
    ThetaLowerSegment 903815424 903880960 (18075302470041 / 20000) (90383037188973 / 100000) := by
  exact
    packedTile32768 903815424 903880960 13 3164 30063 30 _ _ (515553 / 25000) (412443 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903880960 :
    ThetaLowerSegment 903880960 903946496 (90383037188973 / 100000) (90389599169831 / 100000) := by
  exact
    packedTile32768 903880960 903946496 13 3182 30064 30 _ _ (2062219 / 100000) (1031111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell903946496 :
    ThetaLowerSegment 903946496 904012032 (90389599169831 / 100000) (22599024311777 / 25000) := by
  exact
    packedTile32768 903946496 904012032 13 3151 30065 30 _ _ (2062227 / 100000) (206223 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904012032 :
    ThetaLowerSegment 904012032 904077568 (22599024311777 / 25000) (2825082586807 / 3125) := by
  exact
    packedTile32768 904012032 904077568 13 3174 30066 30 _ _ (1031117 / 50000) (2062237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904077568 :
    ThetaLowerSegment 904077568 904143104 (2825082586807 / 3125) (11301136683459 / 12500) := by
  exact
    packedTile32768 904077568 904143104 13 3128 30067 30 _ _ (2062241 / 100000) (515561 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904143104 :
    ThetaLowerSegment 904143104 904208640 (11301136683459 / 12500) (11301977049519 / 12500) := by
  exact
    packedTile32768 904143104 904208640 13 3260 30068 30 _ _ (257781 / 12500) (2062251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904208640 :
    ThetaLowerSegment 904208640 904274176 (11301977049519 / 12500) (2260558998361 / 2500) := by
  exact
    packedTile32768 904208640 904274176 13 3173 30070 30 _ _ (128891 / 6250) (2062259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904274176 :
    ThetaLowerSegment 904274176 904339712 (2260558998361 / 2500) (90428985985459 / 100000) := by
  exact
    packedTile32768 904274176 904339712 13 3213 30071 30 _ _ (2062263 / 100000) (1031133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904339712 :
    ThetaLowerSegment 904339712 904405248 (90428985985459 / 100000) (90435618245779 / 100000) := by
  exact
    packedTile32768 904339712 904405248 13 3216 30072 30 _ _ (206227 / 10000) (2062273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904405248 :
    ThetaLowerSegment 904405248 904470784 (90435618245779 / 100000) (90442056674573 / 100000) := by
  exact
    packedTile32768 904405248 904470784 13 3122 30073 30 _ _ (2062277 / 100000) (51557 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904470784 :
    ThetaLowerSegment 904470784 904536320 (90442056674573 / 100000) (22612116048517 / 25000) := by
  exact
    packedTile32768 904470784 904536320 13 3107 30074 30 _ _ (412457 / 20000) (128893 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904536320 :
    ThetaLowerSegment 904536320 904601856 (22612116048517 / 25000) (22613694733043 / 25000) := by
  exact
    packedTile32768 904536320 904601856 13 3062 30075 30 _ _ (515573 / 25000) (412459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904601856 :
    ThetaLowerSegment 904601856 904667392 (22613694733043 / 25000) (90461339105291 / 100000) := by
  exact
    packedTile32768 904601856 904667392 13 3181 30076 30 _ _ (2062299 / 100000) (1031151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904667392 :
    ThetaLowerSegment 904667392 904732928 (90461339105291 / 100000) (90467841556109 / 100000) := by
  exact
    packedTile32768 904667392 904732928 13 3153 30077 30 _ _ (1031153 / 50000) (2062309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904732928 :
    ThetaLowerSegment 904732928 904798464 (90467841556109 / 100000) (90474403839257 / 100000) := by
  exact
    packedTile32768 904732928 904798464 13 3182 30078 30 _ _ (1031157 / 50000) (2062317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904798464 :
    ThetaLowerSegment 904798464 904864000 (90474403839257 / 100000) (90480887776481 / 100000) := by
  exact
    packedTile32768 904798464 904864000 13 3144 30079 30 _ _ (2062321 / 100000) (515581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904864000 :
    ThetaLowerSegment 904864000 904929536 (90480887776481 / 100000) (3619499324057 / 4000) := by
  exact
    packedTile32768 904864000 904929536 13 3198 30080 30 _ _ (257791 / 12500) (2062331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904929536 :
    ThetaLowerSegment 904929536 904995072 (3619499324057 / 4000) (18098798366137 / 20000) := by
  exact
    packedTile32768 904929536 904995072 13 3156 30082 30 _ _ (412467 / 20000) (1031169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell904995072 :
    ThetaLowerSegment 904995072 905060608 (18098798366137 / 20000) (90500442839589 / 100000) := by
  exact
    packedTile32768 904995072 905060608 13 3128 30083 30 _ _ (2062343 / 100000) (1031173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905060608 :
    ThetaLowerSegment 905060608 905126144 (90500442839589 / 100000) (90507161975889 / 100000) := by
  exact
    packedTile32768 905060608 905126144 13 3258 30084 30 _ _ (41247 / 2000) (2062353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905126144 :
    ThetaLowerSegment 905126144 905191680 (90507161975889 / 100000) (90513864636139 / 100000) := by
  exact
    packedTile32768 905126144 905191680 13 3250 30085 30 _ _ (2062357 / 100000) (51559 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905191680 :
    ThetaLowerSegment 905191680 905257216 (90513864636139 / 100000) (18104080053531 / 20000) := by
  exact
    packedTile32768 905191680 905257216 13 3169 30086 30 _ _ (515591 / 25000) (2062367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905257216 :
    ThetaLowerSegment 905257216 905322752 (18104080053531 / 20000) (45263500958613 / 50000) := by
  exact
    packedTile32768 905257216 905322752 13 3201 30087 30 _ _ (2062371 / 100000) (1031187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905322752 :
    ThetaLowerSegment 905322752 905339136 (45263500958613 / 50000) (9052864357091 / 10000) := by
  exact
    packedTile32768 905322752 905339136 11 796 30088 30 _ _ (2062379 / 100000) (1031191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905339136 :
    ThetaLowerSegment 905339136 905341184 (9052864357091 / 10000) (3621155229789 / 4000) := by
  exact
    packedTile32768 905339136 905341184 8 115 30088 30 _ _ (2062381 / 100000) (128899 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_873341184_905341184 :
    ThetaLowerSegment 873341184 905341184 (87330957008989 / 100000) (3621155229789 / 4000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell873341184 cell873406720)
                    (ThetaLowerSegment.join cell873472256 cell873537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell873603328 cell873668864)
                    (ThetaLowerSegment.join cell873734400 cell873799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell873865472 cell873931008)
                    (ThetaLowerSegment.join cell873996544 cell874062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell874127616 cell874193152)
                    (ThetaLowerSegment.join cell874258688 cell874324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell874389760 cell874455296)
                    (ThetaLowerSegment.join cell874520832 cell874586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell874651904 cell874717440)
                    (ThetaLowerSegment.join cell874782976 cell874848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell874914048 cell874979584)
                    (ThetaLowerSegment.join cell875045120 cell875110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell875176192 cell875241728)
                    (ThetaLowerSegment.join cell875307264 cell875372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell875438336 cell875503872)
                    (ThetaLowerSegment.join cell875569408 cell875634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell875700480 cell875766016)
                    (ThetaLowerSegment.join cell875831552 cell875897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell875962624 cell876028160)
                    (ThetaLowerSegment.join cell876093696 cell876159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell876224768 cell876290304)
                    (ThetaLowerSegment.join cell876355840 cell876421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell876486912 cell876552448)
                    (ThetaLowerSegment.join cell876617984 cell876683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell876749056 cell876814592)
                    (ThetaLowerSegment.join cell876880128 cell876945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell877011200 cell877076736)
                    (ThetaLowerSegment.join cell877142272 cell877207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell877273344 cell877338880)
                    (ThetaLowerSegment.join cell877404416 cell877469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell877535488 cell877601024)
                    (ThetaLowerSegment.join cell877666560 cell877732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell877797632 cell877863168)
                    (ThetaLowerSegment.join cell877928704 cell877994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell878059776 cell878125312)
                    (ThetaLowerSegment.join cell878190848 cell878256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell878321920 cell878387456)
                    (ThetaLowerSegment.join cell878452992 cell878518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell878584064 cell878649600)
                    (ThetaLowerSegment.join cell878715136 cell878780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell878846208 cell878911744)
                    (ThetaLowerSegment.join cell878977280 cell879042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell879108352 cell879173888)
                    (ThetaLowerSegment.join cell879239424 cell879304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell879370496 cell879436032)
                    (ThetaLowerSegment.join cell879501568 cell879567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell879632640 cell879698176)
                    (ThetaLowerSegment.join cell879763712 cell879829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell879894784 cell879960320)
                    (ThetaLowerSegment.join cell880025856 cell880091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell880156928 cell880222464)
                    (ThetaLowerSegment.join cell880288000 cell880353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell880419072 cell880484608)
                    (ThetaLowerSegment.join cell880550144 cell880615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell880681216 cell880746752)
                    (ThetaLowerSegment.join cell880812288 cell880877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell880943360 cell881008896)
                    (ThetaLowerSegment.join cell881074432 cell881139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell881205504 cell881271040)
                    (ThetaLowerSegment.join cell881336576 cell881402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell881467648 cell881533184)
                    (ThetaLowerSegment.join cell881598720 cell881664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell881729792 cell881795328)
                    (ThetaLowerSegment.join cell881860864 cell881926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell881991936 cell882057472)
                    (ThetaLowerSegment.join cell882123008 cell882188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell882254080 cell882319616)
                    (ThetaLowerSegment.join cell882385152 cell882450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell882516224 cell882581760)
                    (ThetaLowerSegment.join cell882647296 cell882712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell882778368 cell882843904)
                    (ThetaLowerSegment.join cell882909440 cell882974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell883040512 cell883106048)
                    (ThetaLowerSegment.join cell883171584 cell883237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell883302656 cell883368192)
                    (ThetaLowerSegment.join cell883433728 cell883499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell883564800 cell883630336)
                    (ThetaLowerSegment.join cell883695872 cell883761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell883826944 cell883892480)
                    (ThetaLowerSegment.join cell883958016 cell884023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell884089088 cell884154624)
                    (ThetaLowerSegment.join cell884220160 cell884285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell884351232 cell884416768)
                    (ThetaLowerSegment.join cell884482304 cell884547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell884613376 cell884678912)
                    (ThetaLowerSegment.join cell884744448 cell884809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell884875520 cell884941056)
                    (ThetaLowerSegment.join cell885006592 cell885072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell885137664 cell885203200)
                    (ThetaLowerSegment.join cell885268736 cell885334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell885399808 cell885465344)
                    (ThetaLowerSegment.join cell885530880 cell885596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell885661952 cell885727488)
                    (ThetaLowerSegment.join cell885793024 cell885858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell885924096 cell885989632)
                    (ThetaLowerSegment.join cell886055168 cell886120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell886186240 cell886251776)
                    (ThetaLowerSegment.join cell886317312 cell886382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell886448384 cell886513920)
                    (ThetaLowerSegment.join cell886579456 cell886644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell886710528 cell886776064)
                    (ThetaLowerSegment.join cell886841600 cell886907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell886972672 cell887038208)
                    (ThetaLowerSegment.join cell887103744 cell887169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell887234816 cell887300352)
                    (ThetaLowerSegment.join cell887365888 cell887431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell887496960 cell887562496)
                    (ThetaLowerSegment.join cell887628032 cell887693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell887759104 cell887824640)
                    (ThetaLowerSegment.join cell887890176 cell887955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell888021248 cell888086784)
                    (ThetaLowerSegment.join cell888152320 cell888217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell888283392 cell888348928)
                    (ThetaLowerSegment.join cell888414464 cell888480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell888545536 cell888611072)
                    (ThetaLowerSegment.join cell888676608 cell888742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell888807680 cell888873216)
                    (ThetaLowerSegment.join cell888938752 cell889004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell889069824 cell889135360)
                    (ThetaLowerSegment.join cell889200896 cell889266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell889331968 cell889397504)
                    (ThetaLowerSegment.join cell889463040 cell889528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell889594112 cell889659648)
                    (ThetaLowerSegment.join cell889725184 cell889790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell889856256 cell889921792)
                    (ThetaLowerSegment.join cell889987328 cell890052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell890118400 cell890183936)
                    (ThetaLowerSegment.join cell890249472 cell890315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell890380544 cell890446080)
                    (ThetaLowerSegment.join cell890511616 cell890577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell890642688 cell890708224)
                    (ThetaLowerSegment.join cell890773760 cell890839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell890904832 cell890970368)
                    (ThetaLowerSegment.join cell891035904 cell891101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell891166976 cell891232512)
                    (ThetaLowerSegment.join cell891298048 cell891363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell891429120 cell891494656)
                    (ThetaLowerSegment.join cell891560192 cell891625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell891691264 cell891756800)
                    (ThetaLowerSegment.join cell891822336 cell891887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell891953408 cell892018944)
                    (ThetaLowerSegment.join cell892084480 cell892150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell892215552 cell892281088)
                    (ThetaLowerSegment.join cell892346624 cell892412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell892477696 cell892543232)
                    (ThetaLowerSegment.join cell892608768 cell892674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell892739840 cell892805376)
                    (ThetaLowerSegment.join cell892870912 cell892936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell893001984 cell893067520)
                    (ThetaLowerSegment.join cell893133056 cell893198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell893264128 cell893329664)
                    (ThetaLowerSegment.join cell893395200 cell893460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell893526272 cell893591808)
                    (ThetaLowerSegment.join cell893657344 cell893722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell893788416 cell893853952)
                    (ThetaLowerSegment.join cell893919488 cell893985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell894050560 cell894116096)
                    (ThetaLowerSegment.join cell894181632 cell894247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell894312704 cell894378240)
                    (ThetaLowerSegment.join cell894443776 cell894509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell894574848 cell894640384)
                    (ThetaLowerSegment.join cell894705920 cell894771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell894836992 cell894902528)
                    (ThetaLowerSegment.join cell894968064 cell895033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell895099136 cell895164672)
                    (ThetaLowerSegment.join cell895230208 cell895295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell895361280 cell895426816)
                    (ThetaLowerSegment.join cell895492352 cell895557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell895623424 cell895688960)
                    (ThetaLowerSegment.join cell895754496 cell895820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell895885568 cell895951104)
                    (ThetaLowerSegment.join cell896016640 cell896082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell896147712 cell896213248)
                    (ThetaLowerSegment.join cell896278784 cell896344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell896409856 cell896475392)
                    (ThetaLowerSegment.join cell896540928 cell896606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell896672000 cell896737536)
                    (ThetaLowerSegment.join cell896803072 cell896868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell896934144 cell896999680)
                    (ThetaLowerSegment.join cell897065216 cell897130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell897196288 cell897261824)
                    (ThetaLowerSegment.join cell897327360 cell897392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell897458432 cell897523968)
                    (ThetaLowerSegment.join cell897589504 cell897655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell897720576 cell897786112)
                    (ThetaLowerSegment.join cell897851648 cell897917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell897982720 cell898048256)
                    (ThetaLowerSegment.join cell898113792 cell898179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell898244864 cell898310400)
                    (ThetaLowerSegment.join cell898375936 cell898441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell898507008 cell898572544)
                    (ThetaLowerSegment.join cell898638080 cell898703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell898769152 cell898834688)
                    (ThetaLowerSegment.join cell898900224 cell898965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell899031296 cell899096832)
                    (ThetaLowerSegment.join cell899162368 cell899227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell899293440 cell899358976)
                    (ThetaLowerSegment.join cell899424512 cell899490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell899555584 cell899621120)
                    (ThetaLowerSegment.join cell899686656 cell899752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell899817728 cell899883264)
                    (ThetaLowerSegment.join cell899948800 cell900014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell900079872 cell900145408)
                    (ThetaLowerSegment.join cell900210944 cell900276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell900342016 cell900407552)
                    (ThetaLowerSegment.join cell900473088 cell900538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell900604160 cell900669696)
                    (ThetaLowerSegment.join cell900735232 cell900800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell900866304 cell900931840)
                    (ThetaLowerSegment.join cell900997376 cell901062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell901128448 cell901193984)
                    (ThetaLowerSegment.join cell901259520 cell901325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell901390592 cell901456128)
                    (ThetaLowerSegment.join cell901521664 cell901587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell901652736 cell901718272)
                    (ThetaLowerSegment.join cell901783808 cell901849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell901914880 cell901980416)
                    (ThetaLowerSegment.join cell902045952 cell902111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell902177024 cell902242560)
                    (ThetaLowerSegment.join cell902308096 cell902373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell902439168 cell902504704)
                    (ThetaLowerSegment.join cell902570240 cell902635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell902701312 cell902766848)
                    (ThetaLowerSegment.join cell902832384 cell902897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell902963456 cell903028992)
                    (ThetaLowerSegment.join cell903094528 cell903160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell903225600 cell903291136)
                    (ThetaLowerSegment.join cell903356672 cell903422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell903487744 cell903553280)
                    (ThetaLowerSegment.join cell903618816 cell903684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell903749888 cell903815424)
                    (ThetaLowerSegment.join cell903880960 cell903946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell904012032 cell904077568)
                    (ThetaLowerSegment.join cell904143104 cell904208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell904274176 cell904339712)
                    (ThetaLowerSegment.join cell904405248 cell904470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell904536320 cell904601856)
                    (ThetaLowerSegment.join cell904667392 cell904732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell904798464 cell904864000)
                  (ThetaLowerSegment.join cell904929536 cell904995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell905060608 cell905126144)
                  (ThetaLowerSegment.join cell905191680 cell905257216)))
              (ThetaLowerSegment.join cell905322752 cell905339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
