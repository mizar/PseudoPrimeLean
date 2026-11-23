/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2921341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2889341184 :
    ThetaLowerSegment 2889341184 2889472256 (288928546597877 / 100000)
      (288941654199153 / 100000) := by
  exact
    packedTile65536 2889341184 2889472256 14 6017 53752 31 _ _ (544607 / 25000) (2178431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889472256 :
    ThetaLowerSegment 2889472256 2889603328 (288941654199153 / 100000)
      (288954604977393 / 100000) := by
  exact
    packedTile65536 2889472256 2889603328 14 5945 53753 31 _ _ (68076 / 3125) (435687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889603328 :
    ThetaLowerSegment 2889603328 2889734400 (288954604977393 / 100000)
      (144483912955773 / 50000) := by
  exact
    packedTile65536 2889603328 2889734400 14 6069 53755 31 _ _ (2178437 / 100000) (54461 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889734400 :
    ThetaLowerSegment 2889734400 2889865472 (144483912955773 / 50000) (36122601995149 / 12500) := by
  exact
    packedTile65536 2889734400 2889865472 14 5963 53756 31 _ _ (1089221 / 50000) (435689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889865472 :
    ThetaLowerSegment 2889865472 2889996544 (36122601995149 / 12500) (36124253257217 / 12500) := by
  exact
    packedTile65536 2889865472 2889996544 14 6064 53757 31 _ _ (1089223 / 50000) (2178449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2889996544 :
    ThetaLowerSegment 2889996544 2890127616 (36124253257217 / 12500)
      (289007151225011 / 100000) := by
  exact
    packedTile65536 2889996544 2890127616 14 6025 53758 31 _ _ (2178451 / 100000) (1089227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2890127616 :
    ThetaLowerSegment 2890127616 2890258688 (289007151225011 / 100000)
      (72255094156329 / 25000) := by
  exact
    packedTile65536 2890127616 2890258688 14 6071 53759 31 _ _ (435691 / 20000) (1089229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2890258688 :
    ThetaLowerSegment 2890258688 2890389760 (72255094156329 / 25000) (72258326990969 / 25000) := by
  exact
    packedTile65536 2890258688 2890389760 14 5936 53761 31 _ _ (108923 / 5000) (2178463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2890389760 :
    ThetaLowerSegment 2890389760 2890520832 (72258326990969 / 25000) (14452325037093 / 5000) := by
  exact
    packedTile65536 2890389760 2890520832 14 6056 53762 31 _ _ (68077 / 3125) (2178467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2890520832 :
    ThetaLowerSegment 2890520832 2890651904 (14452325037093 / 5000) (289059782867353 / 100000) := by
  exact
    packedTile65536 2890520832 2890651904 14 6097 53763 31 _ _ (2178469 / 100000) (272309 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2890651904 :
    ThetaLowerSegment 2890651904 2890782976 (289059782867353 / 100000)
      (144536488939157 / 50000) := by
  exact
    packedTile65536 2890651904 2890782976 14 6057 53764 31 _ _ (2178473 / 100000) (544619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2890782976 :
    ThetaLowerSegment 2890782976 2890914048 (144536488939157 / 50000)
      (144542969911207 / 50000) := by
  exact
    packedTile65536 2890782976 2890914048 14 5950 53766 31 _ _ (1089239 / 50000) (2178481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2890914048 :
    ThetaLowerSegment 2890914048 2891045120 (144542969911207 / 50000) (28909907171191 / 10000) := by
  exact
    packedTile65536 2890914048 2891045120 14 6028 53767 31 _ _ (1089241 / 50000) (435697 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2891045120 :
    ThetaLowerSegment 2891045120 2891176192 (28909907171191 / 10000) (144556019033267 / 50000) := by
  exact
    packedTile65536 2891045120 2891176192 14 5952 53768 31 _ _ (2178487 / 100000) (217849 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2891176192 :
    ThetaLowerSegment 2891176192 2891307264 (144556019033267 / 50000) (57825035309151 / 20000) := by
  exact
    packedTile65536 2891176192 2891307264 14 6031 53769 31 _ _ (2178491 / 100000) (1089247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2891307264 :
    ThetaLowerSegment 2891307264 2891438336 (57825035309151 / 20000)
      (289138003530203 / 100000) := by
  exact
    packedTile65536 2891307264 2891438336 14 5888 53770 31 _ _ (68078 / 3125) (2178499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2891438336 :
    ThetaLowerSegment 2891438336 2891569408 (289138003530203 / 100000)
      (289151109386203 / 100000) := by
  exact
    packedTile65536 2891438336 2891569408 14 6016 53772 31 _ _ (4357 / 200) (2178503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2891569408 :
    ThetaLowerSegment 2891569408 2891700480 (289151109386203 / 100000)
      (144582041191739 / 50000) := by
  exact
    packedTile65536 2891569408 2891700480 14 5955 53773 31 _ _ (435701 / 20000) (544627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2891700480 :
    ThetaLowerSegment 2891700480 2891831552 (144582041191739 / 50000)
      (144588611577899 / 50000) := by
  exact
    packedTile65536 2891700480 2891831552 14 6032 53774 31 _ _ (217851 / 10000) (2178513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2891831552 :
    ThetaLowerSegment 2891831552 2891962624 (144588611577899 / 50000)
      (144595107906647 / 50000) := by
  exact
    packedTile65536 2891831552 2891962624 14 5964 53775 31 _ _ (1089257 / 50000) (2178517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2891962624 :
    ThetaLowerSegment 2891962624 2892093696 (144595107906647 / 50000) (36150421213877 / 12500) := by
  exact
    packedTile65536 2891962624 2892093696 14 6038 53776 31 _ _ (2178519 / 100000) (1089261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2892093696 :
    ThetaLowerSegment 2892093696 2892224768 (36150421213877 / 12500) (72304142890099 / 25000) := by
  exact
    packedTile65536 2892093696 2892224768 14 6060 53778 31 _ _ (2178523 / 100000) (1089263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2892224768 :
    ThetaLowerSegment 2892224768 2892355840 (72304142890099 / 25000) (72307437913699 / 25000) := by
  exact
    packedTile65536 2892224768 2892355840 14 6050 53779 31 _ _ (68079 / 3125) (2178531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2892355840 :
    ThetaLowerSegment 2892355840 2892486912 (72307437913699 / 25000) (36155374368853 / 12500) := by
  exact
    packedTile65536 2892355840 2892486912 14 6079 53780 31 _ _ (544633 / 25000) (435707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2892486912 :
    ThetaLowerSegment 2892486912 2892617984 (36155374368853 / 12500) (72314044864187 / 25000) := by
  exact
    packedTile65536 2892486912 2892617984 14 6052 53781 31 _ _ (2178537 / 100000) (108927 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2892617984 :
    ThetaLowerSegment 2892617984 2892749056 (72314044864187 / 25000) (72317277819031 / 25000) := by
  exact
    packedTile65536 2892617984 2892749056 14 5936 53783 31 _ _ (2178541 / 100000) (136159 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2892749056 :
    ThetaLowerSegment 2892749056 2892880128 (72317277819031 / 25000) (36160250488919 / 12500) := by
  exact
    packedTile65536 2892749056 2892880128 14 5918 53784 31 _ _ (1089273 / 50000) (2178549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2892880128 :
    ThetaLowerSegment 2892880128 2893011200 (36160250488919 / 12500) (9040474095861 / 3125) := by
  exact
    packedTile65536 2892880128 2893011200 14 6044 53785 31 _ _ (43571 / 2000) (2178553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2893011200 :
    ThetaLowerSegment 2893011200 2893142272 (9040474095861 / 3125) (289308336075417 / 100000) := by
  exact
    packedTile65536 2893011200 2893142272 14 6043 53786 31 _ _ (435711 / 20000) (1089279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2893142272 :
    ThetaLowerSegment 2893142272 2893273344 (289308336075417 / 100000)
      (36165167486761 / 12500) := by
  exact
    packedTile65536 2893142272 2893273344 14 5969 53787 31 _ _ (2178559 / 100000) (1089281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2893273344 :
    ThetaLowerSegment 2893273344 2893404416 (36165167486761 / 12500) (36166789427659 / 12500) := by
  exact
    packedTile65536 2893273344 2893404416 14 5956 53789 31 _ _ (544641 / 25000) (2178567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2893404416 :
    ThetaLowerSegment 2893404416 2893535488 (36166789427659 / 12500) (9042113531483 / 3125) := by
  exact
    packedTile65536 2893404416 2893535488 14 6113 53790 31 _ _ (272321 / 12500) (2178571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2893535488 :
    ThetaLowerSegment 2893535488 2893666560 (9042113531483 / 3125) (144680336972717 / 50000) := by
  exact
    packedTile65536 2893535488 2893666560 14 5986 53791 31 _ _ (2178573 / 100000) (136161 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2893666560 :
    ThetaLowerSegment 2893666560 2893797632 (144680336972717 / 50000) (2893737388777 / 1000) := by
  exact
    packedTile65536 2893666560 2893797632 14 5997 53792 31 _ _ (1089289 / 50000) (2178581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2893797632 :
    ThetaLowerSegment 2893797632 2893928704 (2893737388777 / 1000) (144693391024067 / 50000) := by
  exact
    packedTile65536 2893797632 2893928704 14 5987 53794 31 _ _ (1089291 / 50000) (435717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2893928704 :
    ThetaLowerSegment 2893928704 2894059776 (144693391024067 / 50000) (72350034196611 / 25000) := by
  exact
    packedTile65536 2893928704 2894059776 14 6130 53795 31 _ _ (2178587 / 100000) (217859 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2894059776 :
    ThetaLowerSegment 2894059776 2894190848 (72350034196611 / 25000)
      (289413062366847 / 100000) := by
  exact
    packedTile65536 2894059776 2894190848 14 5933 53796 31 _ _ (2178591 / 100000) (1089297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2894190848 :
    ThetaLowerSegment 2894190848 2894321920 (289413062366847 / 100000)
      (289426153550211 / 100000) := by
  exact
    packedTile65536 2894190848 2894321920 14 6009 53797 31 _ _ (544649 / 25000) (2178599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2894321920 :
    ThetaLowerSegment 2894321920 2894452992 (289426153550211 / 100000)
      (289439220793011 / 100000) := by
  exact
    packedTile65536 2894321920 2894452992 14 5998 53798 31 _ _ (10893 / 500) (2178603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2894452992 :
    ThetaLowerSegment 2894452992 2894584064 (289439220793011 / 100000)
      (289452444925361 / 100000) := by
  exact
    packedTile65536 2894452992 2894584064 14 6070 53800 31 _ _ (435721 / 20000) (136163 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2894584064 :
    ThetaLowerSegment 2894584064 2894715136 (289452444925361 / 100000)
      (144732580733047 / 50000) := by
  exact
    packedTile65536 2894584064 2894715136 14 5837 53801 31 _ _ (2178609 / 100000) (544653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2894715136 :
    ThetaLowerSegment 2894715136 2894846208 (144732580733047 / 50000) (72369569725247 / 25000) := by
  exact
    packedTile65536 2894715136 2894846208 14 6021 53802 31 _ _ (1089307 / 50000) (2178617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2894846208 :
    ThetaLowerSegment 2894846208 2894977280 (72369569725247 / 25000) (144745722144781 / 50000) := by
  exact
    packedTile65536 2894846208 2894977280 14 6043 53803 31 _ _ (1089309 / 50000) (2178621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2894977280 :
    ThetaLowerSegment 2894977280 2895108352 (144745722144781 / 50000) (18094044506477 / 6250) := by
  exact
    packedTile65536 2894977280 2895108352 14 6090 53804 31 _ _ (2178623 / 100000) (1089313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2895108352 :
    ThetaLowerSegment 2895108352 2895239424 (18094044506477 / 6250) (72379496074829 / 25000) := by
  exact
    packedTile65536 2895108352 2895239424 14 6092 53806 31 _ _ (2178627 / 100000) (217863 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2895239424 :
    ThetaLowerSegment 2895239424 2895370496 (72379496074829 / 25000) (72382793979019 / 25000) := by
  exact
    packedTile65536 2895239424 2895370496 14 6055 53807 31 _ _ (272329 / 12500) (435727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2895370496 :
    ThetaLowerSegment 2895370496 2895501568 (72382793979019 / 25000) (72386095701877 / 25000) := by
  exact
    packedTile65536 2895370496 2895501568 14 6062 53808 31 _ _ (544659 / 25000) (2178639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2895501568 :
    ThetaLowerSegment 2895501568 2895632640 (72386095701877 / 25000) (57911480908953 / 20000) := by
  exact
    packedTile65536 2895501568 2895632640 14 5977 53809 31 _ _ (2178641 / 100000) (544661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2895632640 :
    ThetaLowerSegment 2895632640 2895763712 (57911480908953 / 20000) (11582822368131 / 4000) := by
  exact
    packedTile65536 2895632640 2895763712 14 6038 53811 31 _ _ (435729 / 20000) (272331 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2895763712 :
    ThetaLowerSegment 2895763712 2895894784 (11582822368131 / 4000) (2316669902857 / 800) := by
  exact
    packedTile65536 2895763712 2895894784 14 6049 53812 31 _ _ (43573 / 2000) (2178653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2895894784 :
    ThetaLowerSegment 2895894784 2896025856 (2316669902857 / 800) (57919337991031 / 20000) := by
  exact
    packedTile65536 2895894784 2896025856 14 5945 53813 31 _ _ (1089327 / 50000) (2178657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2896025856 :
    ThetaLowerSegment 2896025856 2896156928 (57919337991031 / 20000) (14480496265429 / 5000) := by
  exact
    packedTile65536 2896025856 2896156928 14 6075 53814 31 _ _ (2178659 / 100000) (1089331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2896156928 :
    ThetaLowerSegment 2896156928 2896288000 (14480496265429 / 5000) (72405766207791 / 25000) := by
  exact
    packedTile65536 2896156928 2896288000 14 6031 53815 31 _ _ (272333 / 12500) (2178667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2896288000 :
    ThetaLowerSegment 2896288000 2896419072 (72405766207791 / 25000) (72409055996471 / 25000) := by
  exact
    packedTile65536 2896288000 2896419072 14 6040 53817 31 _ _ (544667 / 25000) (2178671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2896419072 :
    ThetaLowerSegment 2896419072 2896550144 (72409055996471 / 25000) (144824576115733 / 50000) := by
  exact
    packedTile65536 2896419072 2896550144 14 5934 53818 31 _ _ (2178673 / 100000) (544669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2896550144 :
    ThetaLowerSegment 2896550144 2896681216 (144824576115733 / 50000) (36207779670691 / 12500) := by
  exact
    packedTile65536 2896550144 2896681216 14 6006 53819 31 _ _ (2178677 / 100000) (54467 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2896681216 :
    ThetaLowerSegment 2896681216 2896812288 (36207779670691 / 12500) (9052359139588 / 3125) := by
  exact
    packedTile65536 2896681216 2896812288 14 6084 53820 31 _ _ (1089341 / 50000) (435737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2896812288 :
    ThetaLowerSegment 2896812288 2896943360 (9052359139588 / 3125) (144844279023379 / 50000) := by
  exact
    packedTile65536 2896812288 2896943360 14 5997 53822 31 _ _ (1089343 / 50000) (2178689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2896943360 :
    ThetaLowerSegment 2896943360 2897074432 (144844279023379 / 50000)
      (289701636728831 / 100000) := by
  exact
    packedTile65536 2896943360 2897074432 14 6003 53823 31 _ _ (2178691 / 100000) (1089347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897074432 :
    ThetaLowerSegment 2897074432 2897205504 (289701636728831 / 100000)
      (72428648356999 / 25000) := by
  exact
    packedTile65536 2897074432 2897205504 14 5947 53824 31 _ _ (435739 / 20000) (1089349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897205504 :
    ThetaLowerSegment 2897205504 2897336576 (72428648356999 / 25000) (72431928389849 / 25000) := by
  exact
    packedTile65536 2897205504 2897336576 14 6022 53825 31 _ _ (21787 / 1000) (2178703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897336576 :
    ThetaLowerSegment 2897336576 2897467648 (72431928389849 / 25000) (72435234573169 / 25000) := by
  exact
    packedTile65536 2897336576 2897467648 14 6070 53826 31 _ _ (136169 / 6250) (2178707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897467648 :
    ThetaLowerSegment 2897467648 2897598720 (72435234573169 / 25000) (11590157023081 / 4000) := by
  exact
    packedTile65536 2897467648 2897598720 14 5961 53828 31 _ _ (2178709 / 100000) (272339 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897598720 :
    ThetaLowerSegment 2897598720 2897729792 (11590157023081 / 4000) (144883608952519 / 50000) := by
  exact
    packedTile65536 2897598720 2897729792 14 6101 53829 31 _ _ (2178713 / 100000) (544679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897729792 :
    ThetaLowerSegment 2897729792 2897860864 (144883608952519 / 50000) (72445064383067 / 25000) := by
  exact
    packedTile65536 2897729792 2897860864 14 5985 53830 31 _ _ (1089359 / 50000) (2178721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897860864 :
    ThetaLowerSegment 2897860864 2897991936 (72445064383067 / 25000) (36224154794743 / 12500) := by
  exact
    packedTile65536 2897860864 2897991936 14 5958 53831 31 _ _ (1089361 / 50000) (87149 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897991936 :
    ThetaLowerSegment 2897991936 2898123008 (36224154794743 / 12500)
      (289806508984101 / 100000) := by
  exact
    packedTile65536 2897991936 2898123008 14 6091 53833 31 _ _ (2178727 / 100000) (217873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2898123008 :
    ThetaLowerSegment 2898123008 2898254080 (289806508984101 / 100000)
      (72454919853249 / 25000) := by
  exact
    packedTile65536 2898123008 2898254080 14 6045 53834 31 _ _ (2178731 / 100000) (1089367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2898254080 :
    ThetaLowerSegment 2898254080 2898385152 (72454919853249 / 25000) (72458137301637 / 25000) := by
  exact
    packedTile65536 2898254080 2898385152 14 5907 53835 31 _ _ (136171 / 6250) (2178739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2898385152 :
    ThetaLowerSegment 2898385152 2898516224 (72458137301637 / 25000) (9057678331794 / 3125) := by
  exact
    packedTile65536 2898385152 2898516224 14 6039 53836 31 _ _ (108937 / 5000) (2178743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2898516224 :
    ThetaLowerSegment 2898516224 2898647296 (9057678331794 / 3125) (144929335075079 / 50000) := by
  exact
    packedTile65536 2898516224 2898647296 14 5950 53837 31 _ _ (435749 / 20000) (544687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2898647296 :
    ThetaLowerSegment 2898647296 2898778368 (144929335075079 / 50000)
      (144935897470079 / 50000) := by
  exact
    packedTile65536 2898647296 2898778368 14 6024 53839 31 _ _ (1743 / 80) (2178753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2898778368 :
    ThetaLowerSegment 2898778368 2898909440 (144935897470079 / 50000)
      (144942433732079 / 50000) := by
  exact
    packedTile65536 2898778368 2898909440 14 6000 53840 31 _ _ (1089377 / 50000) (2178757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2898909440 :
    ThetaLowerSegment 2898909440 2899040512 (144942433732079 / 50000)
      (289897894264219 / 100000) := by
  exact
    packedTile65536 2898909440 2899040512 14 5979 53841 31 _ _ (2178759 / 100000) (1089381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2899040512 :
    ThetaLowerSegment 2899040512 2899171584 (289897894264219 / 100000)
      (289910988629849 / 100000) := by
  exact
    packedTile65536 2899040512 2899171584 14 6010 53842 31 _ _ (2178763 / 100000) (1089383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2899171584 :
    ThetaLowerSegment 2899171584 2899302656 (289910988629849 / 100000)
      (289924144031033 / 100000) := by
  exact
    packedTile65536 2899171584 2899302656 14 6038 53843 31 _ _ (136173 / 6250) (2178771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2899302656 :
    ThetaLowerSegment 2899302656 2899433728 (289924144031033 / 100000)
      (57987461198537 / 20000) := by
  exact
    packedTile65536 2899302656 2899433728 14 6041 53845 31 _ _ (544693 / 25000) (87151 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2899433728 :
    ThetaLowerSegment 2899433728 2899564800 (57987461198537 / 20000) (36243798148877 / 12500) := by
  exact
    packedTile65536 2899433728 2899564800 14 6003 53846 31 _ _ (2178777 / 100000) (108939 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2899564800 :
    ThetaLowerSegment 2899564800 2899695872 (36243798148877 / 12500)
      (289963638715839 / 100000) := by
  exact
    packedTile65536 2899564800 2899695872 14 6083 53847 31 _ _ (2178781 / 100000) (68087 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2899695872 :
    ThetaLowerSegment 2899695872 2899826944 (289963638715839 / 100000)
      (289976720146983 / 100000) := by
  exact
    packedTile65536 2899695872 2899826944 14 6004 53848 31 _ _ (1089393 / 50000) (2178789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2899826944 :
    ThetaLowerSegment 2899826944 2899958016 (289976720146983 / 100000)
      (289989799423353 / 100000) := by
  exact
    packedTile65536 2899826944 2899958016 14 6003 53850 31 _ _ (217879 / 10000) (2178793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2899958016 :
    ThetaLowerSegment 2899958016 2900089088 (289989799423353 / 100000)
      (290002780683963 / 100000) := by
  exact
    packedTile65536 2899958016 2900089088 14 5958 53851 31 _ _ (435759 / 20000) (1089399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2900089088 :
    ThetaLowerSegment 2900089088 2900220160 (290002780683963 / 100000)
      (72504010758369 / 25000) := by
  exact
    packedTile65536 2900089088 2900220160 14 6087 53852 31 _ _ (2178799 / 100000) (1089401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2900220160 :
    ThetaLowerSegment 2900220160 2900351232 (72504010758369 / 25000) (14501455357113 / 5000) := by
  exact
    packedTile65536 2900220160 2900351232 14 5996 53853 31 _ _ (544701 / 25000) (2178807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2900351232 :
    ThetaLowerSegment 2900351232 2900482304 (14501455357113 / 5000) (14502121527659 / 5000) := by
  exact
    packedTile65536 2900351232 2900482304 14 6115 53854 31 _ _ (272351 / 12500) (2178811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2900482304 :
    ThetaLowerSegment 2900482304 2900613376 (14502121527659 / 5000) (72513923791681 / 25000) := by
  exact
    packedTile65536 2900482304 2900613376 14 6088 53856 31 _ _ (2178813 / 100000) (68088 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2900613376 :
    ThetaLowerSegment 2900613376 2900744448 (72513923791681 / 25000) (145034333921571 / 50000) := by
  exact
    packedTile65536 2900613376 2900744448 14 5954 53857 31 _ _ (2178817 / 100000) (108941 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2900744448 :
    ThetaLowerSegment 2900744448 2900875520 (145034333921571 / 50000) (7252042375497 / 2500) := by
  exact
    packedTile65536 2900744448 2900875520 14 5979 53858 31 _ _ (1089411 / 50000) (87153 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2900875520 :
    ThetaLowerSegment 2900875520 2901006592 (7252042375497 / 2500) (145047461336263 / 50000) := by
  exact
    packedTile65536 2900875520 2901006592 14 6071 53859 31 _ _ (1089413 / 50000) (2178829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901006592 :
    ThetaLowerSegment 2901006592 2901137664 (145047461336263 / 50000) (18131747277473 / 6250) := by
  exact
    packedTile65536 2901006592 2901137664 14 5982 53860 31 _ _ (2178831 / 100000) (1089417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901137664 :
    ThetaLowerSegment 2901137664 2901268736 (18131747277473 / 6250) (72530268256567 / 25000) := by
  exact
    packedTile65536 2901137664 2901268736 14 6020 53862 31 _ _ (435767 / 20000) (1089419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901268736 :
    ThetaLowerSegment 2901268736 2901399808 (72530268256567 / 25000) (72533531069467 / 25000) := by
  exact
    packedTile65536 2901268736 2901399808 14 5990 53863 31 _ _ (54471 / 2500) (2178843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901399808 :
    ThetaLowerSegment 2901399808 2901530880 (72533531069467 / 25000) (36268416281419 / 12500) := by
  exact
    packedTile65536 2901399808 2901530880 14 6061 53864 31 _ _ (544711 / 25000) (2178847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901530880 :
    ThetaLowerSegment 2901530880 2901661952 (36268416281419 / 12500)
      (290160453458879 / 100000) := by
  exact
    packedTile65536 2901530880 2901661952 14 6023 53865 31 _ _ (2178849 / 100000) (544713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901661952 :
    ThetaLowerSegment 2901661952 2901793024 (290160453458879 / 100000)
      (145086844995427 / 50000) := by
  exact
    packedTile65536 2901661952 2901793024 14 6075 53867 31 _ _ (2178853 / 100000) (272357 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901793024 :
    ThetaLowerSegment 2901793024 2901924096 (145086844995427 / 50000)
      (145093436040877 / 50000) := by
  exact
    packedTile65536 2901793024 2901924096 14 6050 53868 31 _ _ (1089429 / 50000) (2178861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901924096 :
    ThetaLowerSegment 2901924096 2902055168 (145093436040877 / 50000) (29019978837569 / 10000) := by
  exact
    packedTile65536 2901924096 2902055168 14 5928 53869 31 _ _ (1089431 / 50000) (435773 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2902055168 :
    ThetaLowerSegment 2902055168 2902186240 (29019978837569 / 10000) (145106422073377 / 50000) := by
  exact
    packedTile65536 2902055168 2902186240 14 5992 53870 31 _ _ (2178867 / 100000) (217887 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2902186240 :
    ThetaLowerSegment 2902186240 2902317312 (145106422073377 / 50000)
      (145112960868249 / 50000) := by
  exact
    packedTile65536 2902186240 2902317312 14 6002 53871 31 _ _ (272359 / 12500) (17431 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2902317312 :
    ThetaLowerSegment 2902317312 2902448384 (145112960868249 / 50000) (29023891219521 / 10000) := by
  exact
    packedTile65536 2902317312 2902448384 14 5962 53873 31 _ _ (544719 / 25000) (2178879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2902448384 :
    ThetaLowerSegment 2902448384 2902579456 (29023891219521 / 10000) (145126066822559 / 50000) := by
  exact
    packedTile65536 2902448384 2902579456 14 6068 53874 31 _ _ (2178881 / 100000) (544721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2902579456 :
    ThetaLowerSegment 2902579456 2902710528 (145126066822559 / 50000)
      (145132734210659 / 50000) := by
  exact
    packedTile65536 2902579456 2902710528 14 6120 53875 31 _ _ (435777 / 20000) (272361 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2902710528 :
    ThetaLowerSegment 2902710528 2902841600 (145132734210659 / 50000) (72569630537827 / 25000) := by
  exact
    packedTile65536 2902710528 2902841600 14 5991 53876 31 _ _ (217889 / 10000) (2178893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2902841600 :
    ThetaLowerSegment 2902841600 2902972672 (72569630537827 / 25000) (145145814099359 / 50000) := by
  exact
    packedTile65536 2902841600 2902972672 14 6015 53878 31 _ _ (1089447 / 50000) (2178897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2902972672 :
    ThetaLowerSegment 2902972672 2903103744 (145145814099359 / 50000)
      (145152355154157 / 50000) := by
  exact
    packedTile65536 2902972672 2903103744 14 6004 53879 31 _ _ (2178899 / 100000) (1089451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2903103744 :
    ThetaLowerSegment 2903103744 2903234816 (145152355154157 / 50000)
      (290317615950783 / 100000) := by
  exact
    packedTile65536 2903103744 2903234816 14 5923 53880 31 _ _ (2178903 / 100000) (1089453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2903234816 :
    ThetaLowerSegment 2903234816 2903365888 (290317615950783 / 100000)
      (290330868069239 / 100000) := by
  exact
    packedTile65536 2903234816 2903365888 14 6082 53881 31 _ _ (544727 / 25000) (2178911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2903365888 :
    ThetaLowerSegment 2903365888 2903496960 (290330868069239 / 100000)
      (58068796152331 / 20000) := by
  exact
    packedTile65536 2903365888 2903496960 14 6018 53882 31 _ _ (68091 / 3125) (435783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2903496960 :
    ThetaLowerSegment 2903496960 2903628032 (58068796152331 / 20000)
      (290357084768493 / 100000) := by
  exact
    packedTile65536 2903496960 2903628032 14 6014 53884 31 _ _ (2178917 / 100000) (54473 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2903628032 :
    ThetaLowerSegment 2903628032 2903759104 (290357084768493 / 100000)
      (145185102025917 / 50000) := by
  exact
    packedTile65536 2903628032 2903759104 14 6021 53885 31 _ _ (2178921 / 100000) (544731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2903759104 :
    ThetaLowerSegment 2903759104 2903890176 (145185102025917 / 50000) (29038326889213 / 10000) := by
  exact
    packedTile65536 2903759104 2903890176 14 5996 53886 31 _ _ (1089463 / 50000) (2178929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2903890176 :
    ThetaLowerSegment 2903890176 2904021248 (29038326889213 / 10000) (29039643398719 / 10000) := by
  exact
    packedTile65536 2903890176 2904021248 14 6042 53887 31 _ _ (217893 / 10000) (2178933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2904021248 :
    ThetaLowerSegment 2904021248 2904152320 (29039643398719 / 10000) (5808188234481 / 2000) := by
  exact
    packedTile65536 2904021248 2904152320 14 5956 53888 31 _ _ (435787 / 20000) (1089469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2904152320 :
    ThetaLowerSegment 2904152320 2904283392 (5808188234481 / 2000) (290422635704841 / 100000) := by
  exact
    packedTile65536 2904152320 2904283392 14 6069 53890 31 _ _ (2178939 / 100000) (1089471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2904283392 :
    ThetaLowerSegment 2904283392 2904414464 (290422635704841 / 100000)
      (290435789989769 / 100000) := by
  exact
    packedTile65536 2904283392 2904414464 14 6037 53891 31 _ _ (68092 / 3125) (2178947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2904414464 :
    ThetaLowerSegment 2904414464 2904545536 (290435789989769 / 100000)
      (290448859319873 / 100000) := by
  exact
    packedTile65536 2904414464 2904545536 14 5998 53892 31 _ _ (544737 / 25000) (2178951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2904545536 :
    ThetaLowerSegment 2904545536 2904676608 (290448859319873 / 100000)
      (72615532830649 / 25000) := by
  exact
    packedTile65536 2904545536 2904676608 14 6091 53893 31 _ _ (2178953 / 100000) (544739 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2904676608 :
    ThetaLowerSegment 2904676608 2904807680 (72615532830649 / 25000) (5809505060033 / 2000) := by
  exact
    packedTile65536 2904676608 2904807680 14 6022 53895 31 _ _ (2178957 / 100000) (27237 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2904807680 :
    ThetaLowerSegment 2904807680 2904938752 (5809505060033 / 2000) (5809762177549 / 2000) := by
  exact
    packedTile65536 2904807680 2904938752 14 5900 53896 31 _ _ (1089481 / 50000) (435793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2904938752 :
    ThetaLowerSegment 2904938752 2905069824 (5809762177549 / 2000) (145250669779501 / 50000) := by
  exact
    packedTile65536 2904938752 2905069824 14 6072 53897 31 _ _ (1089483 / 50000) (2178969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905069824 :
    ThetaLowerSegment 2905069824 2905200896 (145250669779501 / 50000)
      (290514541944291 / 100000) := by
  exact
    packedTile65536 2905069824 2905200896 14 6059 53898 31 _ _ (2178971 / 100000) (1089487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905200896 :
    ThetaLowerSegment 2905200896 2905331968 (290514541944291 / 100000)
      (145263891787683 / 50000) := by
  exact
    packedTile65536 2905200896 2905331968 14 6077 53899 31 _ _ (87159 / 4000) (1089489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905331968 :
    ThetaLowerSegment 2905331968 2905463040 (145263891787683 / 50000)
      (145270416743293 / 50000) := by
  exact
    packedTile65536 2905331968 2905463040 14 5989 53901 31 _ _ (108949 / 5000) (2178983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905463040 :
    ThetaLowerSegment 2905463040 2905594112 (145270416743293 / 50000)
      (145276985290561 / 50000) := by
  exact
    packedTile65536 2905463040 2905594112 14 6029 53902 31 _ _ (272373 / 12500) (2178987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905594112 :
    ThetaLowerSegment 2905594112 2905725184 (145276985290561 / 50000) (58113394521697 / 20000) := by
  exact
    packedTile65536 2905594112 2905725184 14 5967 53903 31 _ _ (2178989 / 100000) (136187 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905725184 :
    ThetaLowerSegment 2905725184 2905856256 (58113394521697 / 20000) (145290002582809 / 50000) := by
  exact
    packedTile65536 2905725184 2905856256 14 5981 53904 31 _ _ (2178993 / 100000) (544749 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905856256 :
    ThetaLowerSegment 2905856256 2905987328 (145290002582809 / 50000) (14529653848731 / 5000) := by
  exact
    packedTile65536 2905856256 2905987328 14 5999 53905 31 _ _ (1089499 / 50000) (2179001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905987328 :
    ThetaLowerSegment 2905987328 2906118400 (14529653848731 / 5000) (72651533388651 / 25000) := by
  exact
    packedTile65536 2905987328 2906118400 14 5992 53907 31 _ _ (1089501 / 50000) (435801 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2906118400 :
    ThetaLowerSegment 2906118400 2906249472 (72651533388651 / 25000)
      (290619283861849 / 100000) := by
  exact
    packedTile65536 2906118400 2906249472 14 6035 53908 31 _ _ (2179007 / 100000) (217901 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2906249472 :
    ThetaLowerSegment 2906249472 2906380544 (290619283861849 / 100000)
      (58126469842361 / 20000) := by
  exact
    packedTile65536 2906249472 2906380544 14 5996 53909 31 _ _ (2179011 / 100000) (1089507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2906380544 :
    ThetaLowerSegment 2906380544 2906511616 (58126469842361 / 20000) (11625814317493 / 4000) := by
  exact
    packedTile65536 2906380544 2906511616 14 5970 53910 31 _ _ (272377 / 12500) (2179019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2906511616 :
    ThetaLowerSegment 2906511616 2906642688 (11625814317493 / 4000) (58131707330057 / 20000) := by
  exact
    packedTile65536 2906511616 2906642688 14 6048 53912 31 _ _ (108951 / 5000) (2179023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2906642688 :
    ThetaLowerSegment 2906642688 2906773760 (58131707330057 / 20000) (7266789997629 / 2500) := by
  exact
    packedTile65536 2906642688 2906773760 14 5995 53913 31 _ _ (87161 / 4000) (544757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2906773760 :
    ThetaLowerSegment 2906773760 2906904832 (7266789997629 / 2500) (58136963143209 / 20000) := by
  exact
    packedTile65536 2906773760 2906904832 14 6065 53914 31 _ _ (2179029 / 100000) (272379 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2906904832 :
    ThetaLowerSegment 2906904832 2907035904 (58136963143209 / 20000) (58139632459859 / 20000) := by
  exact
    packedTile65536 2906904832 2907035904 14 6125 53915 31 _ _ (1089517 / 50000) (2179037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2907035904 :
    ThetaLowerSegment 2907035904 2907166976 (58139632459859 / 20000)
      (290711491474741 / 100000) := by
  exact
    packedTile65536 2907035904 2907166976 14 6117 53916 31 _ _ (1089519 / 50000) (2179041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2907166976 :
    ThetaLowerSegment 2907166976 2907298048 (290711491474741 / 100000)
      (58144851261727 / 20000) := by
  exact
    packedTile65536 2907166976 2907298048 14 5858 53918 31 _ _ (2179043 / 100000) (1089523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2907298048 :
    ThetaLowerSegment 2907298048 2907429120 (58144851261727 / 20000) (14536868163817 / 5000) := by
  exact
    packedTile65536 2907298048 2907429120 14 6015 53919 31 _ _ (2179047 / 100000) (43581 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2907429120 :
    ThetaLowerSegment 2907429120 2907560192 (14536868163817 / 5000) (7268759577801 / 2500) := by
  exact
    packedTile65536 2907429120 2907560192 14 5975 53920 31 _ _ (544763 / 25000) (435811 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2907560192 :
    ThetaLowerSegment 2907560192 2907691264 (7268759577801 / 2500) (58152689311751 / 20000) := by
  exact
    packedTile65536 2907560192 2907691264 14 5995 53921 31 _ _ (2179057 / 100000) (108953 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2907691264 :
    ThetaLowerSegment 2907691264 2907822336 (58152689311751 / 20000) (145388268089091 / 50000) := by
  exact
    packedTile65536 2907691264 2907822336 14 6007 53923 31 _ _ (2179061 / 100000) (272383 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2907822336 :
    ThetaLowerSegment 2907822336 2907953408 (145388268089091 / 50000)
      (145394833614949 / 50000) := by
  exact
    packedTile65536 2907822336 2907953408 14 6026 53924 31 _ _ (1089533 / 50000) (2179069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2907953408 :
    ThetaLowerSegment 2907953408 2908084480 (145394833614949 / 50000)
      (145401388257509 / 50000) := by
  exact
    packedTile65536 2907953408 2908084480 14 6016 53925 31 _ _ (217907 / 10000) (2179073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2908084480 :
    ThetaLowerSegment 2908084480 2908215552 (145401388257509 / 50000)
      (290815874934843 / 100000) := by
  exact
    packedTile65536 2908084480 2908215552 14 6011 53926 31 _ _ (87163 / 4000) (1089539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2908215552 :
    ThetaLowerSegment 2908215552 2908346624 (290815874934843 / 100000)
      (290828888394631 / 100000) := by
  exact
    packedTile65536 2908215552 2908346624 14 5972 53927 31 _ _ (2179079 / 100000) (1089541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2908346624 :
    ThetaLowerSegment 2908346624 2908477696 (290828888394631 / 100000)
      (290841949824127 / 100000) := by
  exact
    packedTile65536 2908346624 2908477696 14 5994 53929 31 _ _ (544771 / 25000) (2179087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2908477696 :
    ThetaLowerSegment 2908477696 2908608768 (290841949824127 / 100000)
      (290854902323199 / 100000) := by
  exact
    packedTile65536 2908477696 2908608768 14 5944 53930 31 _ _ (136193 / 6250) (2179091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2908608768 :
    ThetaLowerSegment 2908608768 2908739840 (290854902323199 / 100000)
      (290868020463059 / 100000) := by
  exact
    packedTile65536 2908608768 2908739840 14 6020 53931 31 _ _ (2179093 / 100000) (272387 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2908739840 :
    ThetaLowerSegment 2908739840 2908870912 (290868020463059 / 100000)
      (72720317887979 / 25000) := by
  exact
    packedTile65536 2908739840 2908870912 14 6081 53932 31 _ _ (2179097 / 100000) (21791 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2908870912 :
    ThetaLowerSegment 2908870912 2909001984 (72720317887979 / 25000) (36361800352571 / 12500) := by
  exact
    packedTile65536 2908870912 2909001984 14 6026 53933 31 _ _ (1089551 / 50000) (435821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2909001984 :
    ThetaLowerSegment 2909001984 2909133056 (36361800352571 / 12500) (145453722384989 / 50000) := by
  exact
    packedTile65536 2909001984 2909133056 14 5985 53935 31 _ _ (1089553 / 50000) (2179109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2909133056 :
    ThetaLowerSegment 2909133056 2909264128 (145453722384989 / 50000) (7273017453077 / 2500) := by
  exact
    packedTile65536 2909133056 2909264128 14 6082 53936 31 _ _ (2179111 / 100000) (1089557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2909264128 :
    ThetaLowerSegment 2909264128 2909395200 (7273017453077 / 2500) (14546685589893 / 5000) := by
  exact
    packedTile65536 2909264128 2909395200 14 5972 53937 31 _ _ (435823 / 20000) (1089559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2909395200 :
    ThetaLowerSegment 2909395200 2909526272 (14546685589893 / 5000) (2909469543101 / 1000) := by
  exact
    packedTile65536 2909395200 2909526272 14 6077 53938 31 _ _ (27239 / 1250) (2179123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2909526272 :
    ThetaLowerSegment 2909526272 2909657344 (2909469543101 / 1000) (72740008353087 / 25000) := by
  exact
    packedTile65536 2909526272 2909657344 14 6002 53940 31 _ _ (544781 / 25000) (2179127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2909657344 :
    ThetaLowerSegment 2909657344 2909788416 (72740008353087 / 25000)
      (290973075499413 / 100000) := by
  exact
    packedTile65536 2909657344 2909788416 14 5985 53941 31 _ _ (2179129 / 100000) (544783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2909788416 :
    ThetaLowerSegment 2909788416 2909919488 (290973075499413 / 100000)
      (72746565358299 / 25000) := by
  exact
    packedTile65536 2909788416 2909919488 14 6051 53942 31 _ _ (2179133 / 100000) (68098 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2909919488 :
    ThetaLowerSegment 2909919488 2910050560 (72746565358299 / 25000) (72749858035817 / 25000) := by
  exact
    packedTile65536 2909919488 2910050560 14 6044 53943 31 _ _ (1089569 / 50000) (2179141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2910050560 :
    ThetaLowerSegment 2910050560 2910181632 (72749858035817 / 25000) (145506219720933 / 50000) := by
  exact
    packedTile65536 2910050560 2910181632 14 5969 53944 31 _ _ (1089571 / 50000) (435829 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2910181632 :
    ThetaLowerSegment 2910181632 2910312704 (145506219720933 / 50000) (72756407999451 / 25000) := by
  exact
    packedTile65536 2910181632 2910312704 14 6054 53946 31 _ _ (2179147 / 100000) (43583 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2910312704 :
    ThetaLowerSegment 2910312704 2910443776 (72756407999451 / 25000)
      (291038778815787 / 100000) := by
  exact
    packedTile65536 2910312704 2910443776 14 6033 53947 31 _ _ (2179151 / 100000) (1089577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2910443776 :
    ThetaLowerSegment 2910443776 2910574848 (291038778815787 / 100000)
      (291051831960227 / 100000) := by
  exact
    packedTile65536 2910443776 2910574848 14 5990 53948 31 _ _ (544789 / 25000) (2179159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2910574848 :
    ThetaLowerSegment 2910574848 2910705920 (291051831960227 / 100000)
      (291064978832507 / 100000) := by
  exact
    packedTile65536 2910574848 2910705920 14 6033 53949 31 _ _ (54479 / 2500) (2179163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2910705920 :
    ThetaLowerSegment 2910705920 2910836992 (291064978832507 / 100000)
      (291078040747517 / 100000) := by
  exact
    packedTile65536 2910705920 2910836992 14 5994 53950 31 _ _ (435833 / 20000) (68099 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2910836992 :
    ThetaLowerSegment 2910836992 2910968064 (291078040747517 / 100000)
      (291091154986559 / 100000) := by
  exact
    packedTile65536 2910836992 2910968064 14 6018 53952 31 _ _ (2179169 / 100000) (544793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2910968064 :
    ThetaLowerSegment 2910968064 2911099136 (291091154986559 / 100000)
      (291104175551209 / 100000) := by
  exact
    packedTile65536 2910968064 2911099136 14 5975 53953 31 _ _ (1089587 / 50000) (2179177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2911099136 :
    ThetaLowerSegment 2911099136 2911230208 (291104175551209 / 100000)
      (291117368294821 / 100000) := by
  exact
    packedTile65536 2911099136 2911230208 14 6054 53954 31 _ _ (1089589 / 50000) (2179181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2911230208 :
    ThetaLowerSegment 2911230208 2911361280 (291117368294821 / 100000)
      (291130203682691 / 100000) := by
  exact
    packedTile65536 2911230208 2911361280 14 5890 53955 31 _ _ (2179183 / 100000) (1089593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2911361280 :
    ThetaLowerSegment 2911361280 2911492352 (291130203682691 / 100000)
      (291143265729569 / 100000) := by
  exact
    packedTile65536 2911361280 2911492352 14 5994 53957 31 _ _ (2179187 / 100000) (217919 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2911492352 :
    ThetaLowerSegment 2911492352 2911623424 (291143265729569 / 100000)
      (58231262946253 / 20000) := by
  exact
    packedTile65536 2911492352 2911623424 14 5988 53958 31 _ _ (272399 / 12500) (435839 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2911623424 :
    ThetaLowerSegment 2911623424 2911754496 (58231262946253 / 20000)
      (291169355040129 / 100000) := by
  exact
    packedTile65536 2911623424 2911754496 14 5984 53959 31 _ _ (544799 / 25000) (2179199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2911754496 :
    ThetaLowerSegment 2911754496 2911885568 (291169355040129 / 100000) (14559122710867 / 5000) := by
  exact
    packedTile65536 2911754496 2911885568 14 6011 53960 31 _ _ (2179201 / 100000) (544801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2911885568 :
    ThetaLowerSegment 2911885568 2912016640 (14559122710867 / 5000) (58239107196991 / 20000) := by
  exact
    packedTile65536 2911885568 2912016640 14 6003 53961 31 _ _ (435841 / 20000) (272401 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2912016640 :
    ThetaLowerSegment 2912016640 2912147712 (58239107196991 / 20000) (58241715275519 / 20000) := by
  exact
    packedTile65536 2912016640 2912147712 14 5984 53963 31 _ _ (217921 / 10000) (2179213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2912147712 :
    ThetaLowerSegment 2912147712 2912278784 (58241715275519 / 20000)
      (291221884837493 / 100000) := by
  exact
    packedTile65536 2912147712 2912278784 14 6107 53964 31 _ _ (1089607 / 50000) (2179217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2912278784 :
    ThetaLowerSegment 2912278784 2912409856 (291221884837493 / 100000)
      (291235038603377 / 100000) := by
  exact
    packedTile65536 2912278784 2912409856 14 6036 53965 31 _ _ (2179219 / 100000) (1089611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2912409856 :
    ThetaLowerSegment 2912409856 2912540928 (291235038603377 / 100000)
      (291248205468743 / 100000) := by
  exact
    packedTile65536 2912409856 2912540928 14 6042 53966 31 _ _ (2179223 / 100000) (1089613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2912540928 :
    ThetaLowerSegment 2912540928 2912672000 (291248205468743 / 100000)
      (291261337496671 / 100000) := by
  exact
    packedTile65536 2912540928 2912672000 14 6026 53967 31 _ _ (544807 / 25000) (2179231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2912672000 :
    ThetaLowerSegment 2912672000 2912803072 (291261337496671 / 100000) (11650978433271 / 4000) := by
  exact
    packedTile65536 2912672000 2912803072 14 6022 53969 31 _ _ (68101 / 3125) (435847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2912803072 :
    ThetaLowerSegment 2912803072 2912934144 (11650978433271 / 4000) (291287497027509 / 100000) := by
  exact
    packedTile65536 2912803072 2912934144 14 5982 53970 31 _ _ (2179237 / 100000) (54481 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2912934144 :
    ThetaLowerSegment 2912934144 2913065216 (291287497027509 / 100000)
      (291300668360113 / 100000) := by
  exact
    packedTile65536 2912934144 2913065216 14 6044 53971 31 _ _ (2179241 / 100000) (544811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913065216 :
    ThetaLowerSegment 2913065216 2913196288 (291300668360113 / 100000)
      (291313610902107 / 100000) := by
  exact
    packedTile65536 2913065216 2913196288 14 5939 53972 31 _ _ (1089623 / 50000) (2179249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913196288 :
    ThetaLowerSegment 2913196288 2913327360 (291313610902107 / 100000)
      (291326825874107 / 100000) := by
  exact
    packedTile65536 2913196288 2913327360 14 6064 53974 31 _ _ (8717 / 400) (2179253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913327360 :
    ThetaLowerSegment 2913327360 2913458432 (291326825874107 / 100000)
      (145669916923601 / 50000) := by
  exact
    packedTile65536 2913327360 2913458432 14 5969 53975 31 _ _ (435851 / 20000) (1089629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913458432 :
    ThetaLowerSegment 2913458432 2913589504 (145669916923601 / 50000) (72838213185117 / 25000) := by
  exact
    packedTile65536 2913458432 2913589504 14 5974 53976 31 _ _ (2179259 / 100000) (1089631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913589504 :
    ThetaLowerSegment 2913589504 2913720576 (72838213185117 / 25000) (14568292929401 / 5000) := by
  exact
    packedTile65536 2913589504 2913720576 14 5968 53977 31 _ _ (68102 / 3125) (2179267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913720576 :
    ThetaLowerSegment 2913720576 2913851648 (14568292929401 / 5000) (36422386660323 / 12500) := by
  exact
    packedTile65536 2913720576 2913851648 14 6073 53978 31 _ _ (544817 / 25000) (2179271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913851648 :
    ThetaLowerSegment 2913851648 2913982720 (36422386660323 / 12500) (58278401966731 / 20000) := by
  exact
    packedTile65536 2913851648 2913982720 14 5927 53980 31 _ _ (2179273 / 100000) (544819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913982720 :
    ThetaLowerSegment 2913982720 2914113792 (58278401966731 / 20000)
      (291405072419993 / 100000) := by
  exact
    packedTile65536 2913982720 2914113792 14 5994 53981 31 _ _ (2179277 / 100000) (27241 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2914113792 :
    ThetaLowerSegment 2914113792 2914244864 (291405072419993 / 100000)
      (291418217849017 / 100000) := by
  exact
    packedTile65536 2914113792 2914244864 14 6032 53982 31 _ _ (1089641 / 50000) (435857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2914244864 :
    ThetaLowerSegment 2914244864 2914375936 (291418217849017 / 100000)
      (291431457011467 / 100000) := by
  exact
    packedTile65536 2914244864 2914375936 14 6075 53983 31 _ _ (1089643 / 50000) (2179289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2914375936 :
    ThetaLowerSegment 2914375936 2914507008 (291431457011467 / 100000)
      (145722293619871 / 50000) := by
  exact
    packedTile65536 2914375936 2914507008 14 6025 53984 31 _ _ (2179291 / 100000) (1089647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2914507008 :
    ThetaLowerSegment 2914507008 2914638080 (145722293619871 / 50000)
      (291457656471857 / 100000) := by
  exact
    packedTile65536 2914507008 2914638080 14 5997 53986 31 _ _ (435859 / 20000) (1089649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2914638080 :
    ThetaLowerSegment 2914638080 2914769152 (291457656471857 / 100000)
      (291470751885557 / 100000) := by
  exact
    packedTile65536 2914638080 2914769152 14 6009 53987 31 _ _ (21793 / 1000) (2179303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2914769152 :
    ThetaLowerSegment 2914769152 2914900224 (291470751885557 / 100000)
      (291484008591789 / 100000) := by
  exact
    packedTile65536 2914769152 2914900224 14 6083 53988 31 _ _ (272413 / 12500) (2179307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2914900224 :
    ThetaLowerSegment 2914900224 2915031296 (291484008591789 / 100000)
      (72874264028693 / 25000) := by
  exact
    packedTile65536 2914900224 2915031296 14 5987 53989 31 _ _ (2179309 / 100000) (136207 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2915031296 :
    ThetaLowerSegment 2915031296 2915162368 (72874264028693 / 25000)
      (291510147247963 / 100000) := by
  exact
    packedTile65536 2915031296 2915162368 14 6007 53991 31 _ _ (2179313 / 100000) (544829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2915162368 :
    ThetaLowerSegment 2915162368 2915293440 (291510147247963 / 100000)
      (291523205721419 / 100000) := by
  exact
    packedTile65536 2915162368 2915293440 14 5992 53992 31 _ _ (1089659 / 50000) (2179321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2915293440 :
    ThetaLowerSegment 2915293440 2915424512 (291523205721419 / 100000)
      (291536416771383 / 100000) := by
  exact
    packedTile65536 2915293440 2915424512 14 6062 53993 31 _ _ (1089661 / 50000) (87173 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2915424512 :
    ThetaLowerSegment 2915424512 2915555584 (291536416771383 / 100000) (18221833352657 / 6250) := by
  exact
    packedTile65536 2915424512 2915555584 14 5927 53994 31 _ _ (2179327 / 100000) (217933 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2915555584 :
    ThetaLowerSegment 2915555584 2915686656 (18221833352657 / 6250) (2915622963033 / 1000) := by
  exact
    packedTile65536 2915555584 2915686656 14 5948 53995 31 _ _ (2179331 / 100000) (1089667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2915686656 :
    ThetaLowerSegment 2915686656 2915817728 (2915622963033 / 1000) (72893849072999 / 25000) := by
  exact
    packedTile65536 2915686656 2915817728 14 6011 53997 31 _ _ (272417 / 12500) (2179339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2915817728 :
    ThetaLowerSegment 2915817728 2915948800 (72893849072999 / 25000) (36448584376327 / 12500) := by
  exact
    packedTile65536 2915817728 2915948800 14 6093 53998 31 _ _ (108967 / 5000) (2179343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2915948800 :
    ThetaLowerSegment 2915948800 2916079872 (36448584376327 / 12500)
      (291601770694721 / 100000) := by
  exact
    packedTile65536 2915948800 2916079872 14 6009 53999 31 _ _ (435869 / 20000) (544837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2916079872 :
    ThetaLowerSegment 2916079872 2916210944 (291601770694721 / 100000)
      (72903780891511 / 25000) := by
  exact
    packedTile65536 2916079872 2916210944 14 6127 54000 31 _ _ (2179349 / 100000) (272419 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2916210944 :
    ThetaLowerSegment 2916210944 2916342016 (72903780891511 / 25000) (145814039912787 / 50000) := by
  exact
    packedTile65536 2916210944 2916342016 14 5945 54001 31 _ _ (1089677 / 50000) (2179357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2916342016 :
    ThetaLowerSegment 2916342016 2916473088 (145814039912787 / 50000)
      (145820665161107 / 50000) := by
  exact
    packedTile65536 2916342016 2916473088 14 6080 54003 31 _ _ (1089679 / 50000) (2179361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2916473088 :
    ThetaLowerSegment 2916473088 2916604160 (145820665161107 / 50000)
      (291654238689263 / 100000) := by
  exact
    packedTile65536 2916473088 2916604160 14 5923 54004 31 _ _ (2179363 / 100000) (1089683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2916604160 :
    ThetaLowerSegment 2916604160 2916735232 (291654238689263 / 100000)
      (58333483028429 / 20000) := by
  exact
    packedTile65536 2916604160 2916735232 14 6046 54005 31 _ _ (2179367 / 100000) (217937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2916735232 :
    ThetaLowerSegment 2916735232 2916866304 (58333483028429 / 20000)
      (291680530602841 / 100000) := by
  exact
    packedTile65536 2916735232 2916866304 14 6018 54006 31 _ _ (544843 / 25000) (3487 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2916866304 :
    ThetaLowerSegment 2916866304 2916997376 (291680530602841 / 100000)
      (291693486993161 / 100000) := by
  exact
    packedTile65536 2916866304 2916997376 14 5945 54008 31 _ _ (136211 / 6250) (2179379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2916997376 :
    ThetaLowerSegment 2916997376 2917128448 (291693486993161 / 100000)
      (291706489180207 / 100000) := by
  exact
    packedTile65536 2916997376 2917128448 14 5966 54009 31 _ _ (2179381 / 100000) (272423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2917128448 :
    ThetaLowerSegment 2917128448 2917259520 (291706489180207 / 100000)
      (291719718047157 / 100000) := by
  exact
    packedTile65536 2917128448 2917259520 14 6070 54010 31 _ _ (435877 / 20000) (544847 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2917259520 :
    ThetaLowerSegment 2917259520 2917390592 (291719718047157 / 100000)
      (291732770413867 / 100000) := by
  exact
    packedTile65536 2917259520 2917390592 14 5989 54011 31 _ _ (217939 / 10000) (2179393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2917390592 :
    ThetaLowerSegment 2917390592 2917521664 (291732770413867 / 100000)
      (291745886006959 / 100000) := by
  exact
    packedTile65536 2917390592 2917521664 14 6018 54012 31 _ _ (1089697 / 50000) (2179397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2917521664 :
    ThetaLowerSegment 2917521664 2917652736 (291745886006959 / 100000)
      (291759184699657 / 100000) := by
  exact
    packedTile65536 2917521664 2917652736 14 6102 54014 31 _ _ (2179399 / 100000) (1089701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2917652736 :
    ThetaLowerSegment 2917652736 2917783808 (291759184699657 / 100000)
      (72943039671429 / 25000) := by
  exact
    packedTile65536 2917652736 2917783808 14 5953 54015 31 _ _ (2179403 / 100000) (1089703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2917783808 :
    ThetaLowerSegment 2917783808 2917914880 (72943039671429 / 25000) (72946339839993 / 25000) := by
  exact
    packedTile65536 2917783808 2917914880 14 6057 54016 31 _ _ (136213 / 6250) (2179411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2917914880 :
    ThetaLowerSegment 2917914880 2918045952 (72946339839993 / 25000) (18237406462109 / 6250) := by
  exact
    packedTile65536 2917914880 2918045952 14 6031 54017 31 _ _ (544853 / 25000) (435883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2918045952 :
    ThetaLowerSegment 2918045952 2918177024 (18237406462109 / 6250) (29181170630193 / 10000) := by
  exact
    packedTile65536 2918045952 2918177024 14 6058 54018 31 _ _ (2179417 / 100000) (108971 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2918177024 :
    ThetaLowerSegment 2918177024 2918308096 (29181170630193 / 10000) (72956140131747 / 25000) := by
  exact
    packedTile65536 2918177024 2918308096 14 5898 54020 31 _ _ (2179421 / 100000) (68107 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2918308096 :
    ThetaLowerSegment 2918308096 2918439168 (72956140131747 / 25000)
      (291837508490913 / 100000) := by
  exact
    packedTile65536 2918308096 2918439168 14 5941 54021 31 _ _ (87177 / 4000) (544857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2918439168 :
    ThetaLowerSegment 2918439168 2918570240 (291837508490913 / 100000)
      (291850637377233 / 100000) := by
  exact
    packedTile65536 2918439168 2918570240 14 6024 54022 31 _ _ (217943 / 10000) (2179433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2918570240 :
    ThetaLowerSegment 2918570240 2918701312 (291850637377233 / 100000)
      (291863713981233 / 100000) := by
  exact
    packedTile65536 2918570240 2918701312 14 6000 54023 31 _ _ (1089717 / 50000) (2179437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2918701312 :
    ThetaLowerSegment 2918701312 2918832384 (291863713981233 / 100000) (5837535943071 / 2000) := by
  exact
    packedTile65536 2918701312 2918832384 14 6003 54025 31 _ _ (2179439 / 100000) (1089721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2918832384 :
    ThetaLowerSegment 2918832384 2918963456 (5837535943071 / 2000) (291890176754127 / 100000) := by
  exact
    packedTile65536 2918832384 2918963456 14 6139 54026 31 _ _ (2179443 / 100000) (1089723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2918963456 :
    ThetaLowerSegment 2918963456 2919094528 (291890176754127 / 100000)
      (291903203314823 / 100000) := by
  exact
    packedTile65536 2918963456 2919094528 14 5977 54027 31 _ _ (272431 / 12500) (2179451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2919094528 :
    ThetaLowerSegment 2919094528 2919225600 (291903203314823 / 100000)
      (58383269517967 / 20000) := by
  exact
    packedTile65536 2919094528 2919225600 14 6031 54028 31 _ _ (544863 / 25000) (435891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2919225600 :
    ThetaLowerSegment 2919225600 2919356672 (58383269517967 / 20000) (145964658769221 / 50000) := by
  exact
    packedTile65536 2919225600 2919356672 14 5951 54029 31 _ _ (2179457 / 100000) (108973 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2919356672 :
    ThetaLowerSegment 2919356672 2919487744 (145964658769221 / 50000) (29194262968623 / 10000) := by
  exact
    packedTile65536 2919356672 2919487744 14 6108 54031 31 _ _ (2179461 / 100000) (272433 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2919487744 :
    ThetaLowerSegment 2919487744 2919618816 (29194262968623 / 10000) (72988939152487 / 25000) := by
  exact
    packedTile65536 2919487744 2919618816 14 6023 54032 31 _ _ (1089733 / 50000) (2179469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2919618816 :
    ThetaLowerSegment 2919618816 2919749888 (72988939152487 / 25000) (145984433060999 / 50000) := by
  exact
    packedTile65536 2919618816 2919749888 14 6015 54033 31 _ _ (217947 / 10000) (2179473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2919749888 :
    ThetaLowerSegment 2919749888 2919880960 (145984433060999 / 50000)
      (291981844895623 / 100000) := by
  exact
    packedTile65536 2919749888 2919880960 14 5955 54034 31 _ _ (87179 / 4000) (1089739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2919880960 :
    ThetaLowerSegment 2919880960 2920012032 (291981844895623 / 100000)
      (291994956641287 / 100000) := by
  exact
    packedTile65536 2919880960 2920012032 14 6016 54035 31 _ _ (2179479 / 100000) (1089741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2920012032 :
    ThetaLowerSegment 2920012032 2920143104 (291994956641287 / 100000) (2336065262207 / 800) := by
  exact
    packedTile65536 2920012032 2920143104 14 6057 54037 31 _ _ (544871 / 25000) (2179487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2920143104 :
    ThetaLowerSegment 2920143104 2920274176 (2336065262207 / 800) (292021215088483 / 100000) := by
  exact
    packedTile65536 2920143104 2920274176 14 5991 54038 31 _ _ (68109 / 3125) (2179491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2920274176 :
    ThetaLowerSegment 2920274176 2920405248 (292021215088483 / 100000)
      (292034353072287 / 100000) := by
  exact
    packedTile65536 2920274176 2920405248 14 6028 54039 31 _ _ (2179493 / 100000) (272437 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2920405248 :
    ThetaLowerSegment 2920405248 2920536320 (292034353072287 / 100000) (18252972142851 / 6250) := by
  exact
    packedTile65536 2920405248 2920536320 14 6057 54040 31 _ _ (2179497 / 100000) (4359 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2920536320 :
    ThetaLowerSegment 2920536320 2920667392 (18252972142851 / 6250) (146030260071507 / 50000) := by
  exact
    packedTile65536 2920536320 2920667392 14 5949 54041 31 _ _ (1089751 / 50000) (435901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2920667392 :
    ThetaLowerSegment 2920667392 2920798464 (146030260071507 / 50000) (18254603774043 / 6250) := by
  exact
    packedTile65536 2920667392 2920798464 14 6029 54043 31 _ _ (1089753 / 50000) (2179509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2920798464 :
    ThetaLowerSegment 2920798464 2920929536 (18254603774043 / 6250) (292086508602033 / 100000) := by
  exact
    packedTile65536 2920798464 2920929536 14 5895 54044 31 _ _ (2179511 / 100000) (1089757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2920929536 :
    ThetaLowerSegment 2920929536 2921060608 (292086508602033 / 100000)
      (292099677231663 / 100000) := by
  exact
    packedTile65536 2920929536 2921060608 14 6042 54045 31 _ _ (435903 / 20000) (1089759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921060608 :
    ThetaLowerSegment 2921060608 2921191680 (292099677231663 / 100000)
      (292112898199983 / 100000) := by
  exact
    packedTile65536 2921060608 2921191680 14 6066 54046 31 _ _ (13622 / 625) (2179523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921191680 :
    ThetaLowerSegment 2921191680 2921322752 (292112898199983 / 100000)
      (292126295734011 / 100000) := by
  exact
    packedTile65536 2921191680 2921322752 14 6147 54048 31 _ _ (544881 / 25000) (2179527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921322752 :
    ThetaLowerSegment 2921322752 2921339136 (292126295734011 / 100000)
      (292127851917717 / 100000) := by
  exact
    packedTile65536 2921322752 2921339136 11 714 54049 31 _ _ (2179529 / 100000) (544883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921339136 :
    ThetaLowerSegment 2921339136 2921341184 (292127851917717 / 100000) (14606402076837 / 5000) := by
  exact
    packedTile65536 2921339136 2921341184 8 87 54049 31 _ _ (2179529 / 100000) (544883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2889341184_2921341184 :
    ThetaLowerSegment 2889341184 2921341184 (288928546597877 / 100000) (14606402076837 / 5000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2889341184 cell2889472256)
                  (ThetaLowerSegment.join cell2889603328 cell2889734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2889865472 cell2889996544)
                  (ThetaLowerSegment.join cell2890127616 cell2890258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2890389760 cell2890520832)
                  (ThetaLowerSegment.join cell2890651904 cell2890782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2890914048 cell2891045120)
                  (ThetaLowerSegment.join cell2891176192 cell2891307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2891438336 cell2891569408)
                  (ThetaLowerSegment.join cell2891700480 cell2891831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2891962624 cell2892093696)
                  (ThetaLowerSegment.join cell2892224768 cell2892355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2892486912 cell2892617984)
                  (ThetaLowerSegment.join cell2892749056 cell2892880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2893011200 cell2893142272)
                  (ThetaLowerSegment.join cell2893273344 cell2893404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2893535488 cell2893666560)
                  (ThetaLowerSegment.join cell2893797632 cell2893928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2894059776 cell2894190848)
                  (ThetaLowerSegment.join cell2894321920 cell2894452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2894584064 cell2894715136)
                  (ThetaLowerSegment.join cell2894846208 cell2894977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2895108352 cell2895239424)
                  (ThetaLowerSegment.join cell2895370496 cell2895501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2895632640 cell2895763712)
                  (ThetaLowerSegment.join cell2895894784 cell2896025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2896156928 cell2896288000)
                  (ThetaLowerSegment.join cell2896419072 cell2896550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2896681216 cell2896812288)
                  (ThetaLowerSegment.join cell2896943360 cell2897074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2897205504 cell2897336576)
                  (ThetaLowerSegment.join cell2897467648 cell2897598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2897729792 cell2897860864)
                  (ThetaLowerSegment.join cell2897991936 cell2898123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2898254080 cell2898385152)
                  (ThetaLowerSegment.join cell2898516224 cell2898647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2898778368 cell2898909440)
                  (ThetaLowerSegment.join cell2899040512 cell2899171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2899302656 cell2899433728)
                  (ThetaLowerSegment.join cell2899564800 cell2899695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2899826944 cell2899958016)
                  (ThetaLowerSegment.join cell2900089088 cell2900220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2900351232 cell2900482304)
                  (ThetaLowerSegment.join cell2900613376 cell2900744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2900875520 cell2901006592)
                  (ThetaLowerSegment.join cell2901137664 cell2901268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2901399808 cell2901530880)
                  (ThetaLowerSegment.join cell2901661952 cell2901793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2901924096 cell2902055168)
                  (ThetaLowerSegment.join cell2902186240 cell2902317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2902448384 cell2902579456)
                  (ThetaLowerSegment.join cell2902710528 cell2902841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2902972672 cell2903103744)
                  (ThetaLowerSegment.join cell2903234816 cell2903365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2903496960 cell2903628032)
                  (ThetaLowerSegment.join cell2903759104 cell2903890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2904021248 cell2904152320)
                  (ThetaLowerSegment.join cell2904283392 cell2904414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2904545536 cell2904676608)
                  (ThetaLowerSegment.join cell2904807680 cell2904938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2905069824 cell2905200896)
                  (ThetaLowerSegment.join cell2905331968 cell2905463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2905594112 cell2905725184)
                  (ThetaLowerSegment.join cell2905856256 cell2905987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2906118400 cell2906249472)
                  (ThetaLowerSegment.join cell2906380544 cell2906511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2906642688 cell2906773760)
                  (ThetaLowerSegment.join cell2906904832 cell2907035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2907166976 cell2907298048)
                  (ThetaLowerSegment.join cell2907429120 cell2907560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2907691264 cell2907822336)
                  (ThetaLowerSegment.join cell2907953408 cell2908084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2908215552 cell2908346624)
                  (ThetaLowerSegment.join cell2908477696 cell2908608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2908739840 cell2908870912)
                  (ThetaLowerSegment.join cell2909001984 cell2909133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2909264128 cell2909395200)
                  (ThetaLowerSegment.join cell2909526272 cell2909657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2909788416 cell2909919488)
                  (ThetaLowerSegment.join cell2910050560 cell2910181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2910312704 cell2910443776)
                  (ThetaLowerSegment.join cell2910574848 cell2910705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2910836992 cell2910968064)
                  (ThetaLowerSegment.join cell2911099136 cell2911230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2911361280 cell2911492352)
                  (ThetaLowerSegment.join cell2911623424 cell2911754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2911885568 cell2912016640)
                  (ThetaLowerSegment.join cell2912147712 cell2912278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2912409856 cell2912540928)
                  (ThetaLowerSegment.join cell2912672000 cell2912803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2912934144 cell2913065216)
                  (ThetaLowerSegment.join cell2913196288 cell2913327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2913458432 cell2913589504)
                  (ThetaLowerSegment.join cell2913720576 cell2913851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2913982720 cell2914113792)
                  (ThetaLowerSegment.join cell2914244864 cell2914375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2914507008 cell2914638080)
                  (ThetaLowerSegment.join cell2914769152 cell2914900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2915031296 cell2915162368)
                  (ThetaLowerSegment.join cell2915293440 cell2915424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2915555584 cell2915686656)
                  (ThetaLowerSegment.join cell2915817728 cell2915948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2916079872 cell2916210944)
                  (ThetaLowerSegment.join cell2916342016 cell2916473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2916604160 cell2916735232)
                  (ThetaLowerSegment.join cell2916866304 cell2916997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2917128448 cell2917259520)
                  (ThetaLowerSegment.join cell2917390592 cell2917521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2917652736 cell2917783808)
                  (ThetaLowerSegment.join cell2917914880 cell2918045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2918177024 cell2918308096)
                  (ThetaLowerSegment.join cell2918439168 cell2918570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2918701312 cell2918832384)
                  (ThetaLowerSegment.join cell2918963456 cell2919094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2919225600 cell2919356672)
                  (ThetaLowerSegment.join cell2919487744 cell2919618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2919749888 cell2919880960)
                  (ThetaLowerSegment.join cell2920012032 cell2920143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2920274176 cell2920405248)
                  (ThetaLowerSegment.join cell2920536320 cell2920667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2920798464 cell2920929536)
                (ThetaLowerSegment.join cell2921060608 cell2921191680))
              (ThetaLowerSegment.join cell2921322752 cell2921339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
