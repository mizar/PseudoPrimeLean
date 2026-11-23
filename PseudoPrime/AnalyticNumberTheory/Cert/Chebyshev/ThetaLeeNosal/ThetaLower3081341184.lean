/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3081341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3049341184 :
    ThetaLowerSegment 3049341184 3049472256 (304926605125579 / 100000)
      (304939587923589 / 100000) := by
  exact
    packedTile65536 3049341184 3049472256 14 5945 55220 32 _ _ (1091909 / 50000) (2183821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049472256 :
    ThetaLowerSegment 3049472256 3049603328 (304939587923589 / 100000) (12198106585989 / 4000) := by
  exact
    packedTile65536 3049472256 3049603328 14 5988 55222 32 _ _ (1091911 / 50000) (87353 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049603328 :
    ThetaLowerSegment 3049603328 3049734400 (12198106585989 / 4000) (60993160072623 / 20000) := by
  exact
    packedTile65536 3049603328 3049734400 14 6015 55223 32 _ _ (1091913 / 50000) (2183829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049734400 :
    ThetaLowerSegment 3049734400 3049865472 (60993160072623 / 20000)
      (304978833466523 / 100000) := by
  exact
    packedTile65536 3049734400 3049865472 14 5968 55224 32 _ _ (2183831 / 100000) (1091917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049865472 :
    ThetaLowerSegment 3049865472 3049996544 (304978833466523 / 100000)
      (304991875329143 / 100000) := by
  exact
    packedTile65536 3049865472 3049996544 14 5972 55225 32 _ _ (436767 / 20000) (1091919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049996544 :
    ThetaLowerSegment 3049996544 3050127616 (304991875329143 / 100000) (12200198086283 / 4000) := by
  exact
    packedTile65536 3049996544 3050127616 14 5988 55226 32 _ _ (2183839 / 100000) (1091921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3050127616 :
    ThetaLowerSegment 3050127616 3050258688 (12200198086283 / 4000) (152508919507309 / 50000) := by
  exact
    packedTile65536 3050127616 3050258688 14 5901 55227 32 _ _ (2183843 / 100000) (1091923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3050258688 :
    ThetaLowerSegment 3050258688 3050389760 (152508919507309 / 50000) (30503109278813 / 10000) := by
  exact
    packedTile65536 3050258688 3050389760 14 6069 55229 32 _ _ (272981 / 12500) (2183851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3050389760 :
    ThetaLowerSegment 3050389760 3050520832 (30503109278813 / 10000) (30504417406161 / 10000) := by
  exact
    packedTile65536 3050389760 3050520832 14 5990 55230 32 _ _ (545963 / 25000) (436771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3050520832 :
    ThetaLowerSegment 3050520832 3050651904 (30504417406161 / 10000) (152528727044973 / 50000) := by
  exact
    packedTile65536 3050520832 3050651904 14 6081 55231 32 _ _ (136491 / 6250) (2183859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3050651904 :
    ThetaLowerSegment 3050651904 3050782976 (152528727044973 / 50000) (61014102278973 / 20000) := by
  exact
    packedTile65536 3050651904 3050782976 14 5979 55232 32 _ _ (2183861 / 100000) (272983 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3050782976 :
    ThetaLowerSegment 3050782976 3050914048 (61014102278973 / 20000) (30508373032971 / 10000) := by
  exact
    packedTile65536 3050782976 3050914048 14 6053 55233 32 _ _ (436773 / 20000) (545967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3050914048 :
    ThetaLowerSegment 3050914048 3051045120 (30508373032971 / 10000) (61019351421659 / 20000) := by
  exact
    packedTile65536 3050914048 3051045120 14 5965 55235 32 _ _ (2183869 / 100000) (68246 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3051045120 :
    ThetaLowerSegment 3051045120 3051176192 (61019351421659 / 20000) (61021965518837 / 20000) := by
  exact
    packedTile65536 3051045120 3051176192 14 5985 55236 32 _ _ (1091937 / 50000) (2183877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3051176192 :
    ThetaLowerSegment 3051176192 3051307264 (61021965518837 / 20000)
      (305122815116651 / 100000) := by
  exact
    packedTile65536 3051176192 3051307264 14 5947 55237 32 _ _ (1091939 / 50000) (2183881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3051307264 :
    ThetaLowerSegment 3051307264 3051438336 (305122815116651 / 100000)
      (305135946799117 / 100000) := by
  exact
    packedTile65536 3051307264 3051438336 14 6013 55238 32 _ _ (1091941 / 50000) (436777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3051438336 :
    ThetaLowerSegment 3051438336 3051569408 (305135946799117 / 100000)
      (305149095976723 / 100000) := by
  exact
    packedTile65536 3051438336 3051569408 14 6021 55239 32 _ _ (1091943 / 50000) (2183889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3051569408 :
    ThetaLowerSegment 3051569408 3051700480 (305149095976723 / 100000)
      (305162238632761 / 100000) := by
  exact
    packedTile65536 3051569408 3051700480 14 6018 55241 32 _ _ (2183891 / 100000) (1091947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3051700480 :
    ThetaLowerSegment 3051700480 3051831552 (305162238632761 / 100000)
      (305175433726351 / 100000) := by
  exact
    packedTile65536 3051700480 3051831552 14 6042 55242 32 _ _ (436779 / 20000) (1091949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3051831552 :
    ThetaLowerSegment 3051831552 3051962624 (305175433726351 / 100000) (9537143081701 / 3125) := by
  exact
    packedTile65536 3051831552 3051962624 14 6019 55243 32 _ _ (2183899 / 100000) (1091951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3051962624 :
    ThetaLowerSegment 3051962624 3052093696 (9537143081701 / 3125) (9537553587406 / 3125) := by
  exact
    packedTile65536 3051962624 3052093696 14 6015 55244 32 _ _ (68247 / 3125) (2183907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3052093696 :
    ThetaLowerSegment 3052093696 3052224768 (9537553587406 / 3125) (76303735681937 / 25000) := by
  exact
    packedTile65536 3052093696 3052224768 14 6057 55245 32 _ _ (545977 / 25000) (2183911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3052224768 :
    ThetaLowerSegment 3052224768 3052355840 (76303735681937 / 25000) (15261402965161 / 5000) := by
  exact
    packedTile65536 3052224768 3052355840 14 6006 55246 32 _ _ (272989 / 12500) (436783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3052355840 :
    ThetaLowerSegment 3052355840 3052486912 (15261402965161 / 5000) (76310300527427 / 25000) := by
  exact
    packedTile65536 3052355840 3052486912 14 6018 55248 32 _ _ (545979 / 25000) (2183919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3052486912 :
    ThetaLowerSegment 3052486912 3052617984 (76310300527427 / 25000) (152627115691197 / 50000) := by
  exact
    packedTile65536 3052486912 3052617984 14 5966 55249 32 _ _ (2183921 / 100000) (545981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3052617984 :
    ThetaLowerSegment 3052617984 3052749056 (152627115691197 / 50000)
      (152633623787697 / 50000) := by
  exact
    packedTile65536 3052617984 3052749056 14 5960 55250 32 _ _ (87357 / 4000) (272991 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3052749056 :
    ThetaLowerSegment 3052749056 3052880128 (152633623787697 / 50000)
      (305280449426199 / 100000) := by
  exact
    packedTile65536 3052749056 3052880128 14 6045 55251 32 _ _ (2183929 / 100000) (545983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3052880128 :
    ThetaLowerSegment 3052880128 3053011200 (305280449426199 / 100000)
      (305293417626291 / 100000) := by
  exact
    packedTile65536 3052880128 3053011200 14 5938 55252 32 _ _ (1091967 / 50000) (2183937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3053011200 :
    ThetaLowerSegment 3053011200 3053142272 (305293417626291 / 100000)
      (61061292457593 / 20000) := by
  exact
    packedTile65536 3053011200 3053142272 14 5973 55254 32 _ _ (1091969 / 50000) (2183941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3053142272 :
    ThetaLowerSegment 3053142272 3053273344 (61061292457593 / 20000) (2442556178089 / 800) := by
  exact
    packedTile65536 3053142272 3053273344 14 5980 55255 32 _ _ (1091971 / 50000) (436789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3053273344 :
    ThetaLowerSegment 3053273344 3053404416 (2442556178089 / 800) (305332621575231 / 100000) := by
  exact
    packedTile65536 3053273344 3053404416 14 5998 55256 32 _ _ (2183947 / 100000) (43679 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3053404416 :
    ThetaLowerSegment 3053404416 3053535488 (305332621575231 / 100000)
      (305345830110879 / 100000) := by
  exact
    packedTile65536 3053404416 3053535488 14 6048 55257 32 _ _ (2183951 / 100000) (1091977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3053535488 :
    ThetaLowerSegment 3053535488 3053666560 (305345830110879 / 100000)
      (305358846482679 / 100000) := by
  exact
    packedTile65536 3053535488 3053666560 14 5960 55258 32 _ _ (436791 / 20000) (1091979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3053666560 :
    ThetaLowerSegment 3053666560 3053797632 (305358846482679 / 100000)
      (305371976444187 / 100000) := by
  exact
    packedTile65536 3053666560 3053797632 14 6012 55259 32 _ _ (2183959 / 100000) (1091981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3053797632 :
    ThetaLowerSegment 3053797632 3053928704 (305371976444187 / 100000)
      (305384981949807 / 100000) := by
  exact
    packedTile65536 3053797632 3053928704 14 5955 55261 32 _ _ (545991 / 25000) (2183967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3053928704 :
    ThetaLowerSegment 3053928704 3054059776 (305384981949807 / 100000)
      (61079663451683 / 20000) := by
  exact
    packedTile65536 3053928704 3054059776 14 6106 55262 32 _ _ (68249 / 3125) (2183971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3054059776 :
    ThetaLowerSegment 3054059776 3054190848 (61079663451683 / 20000)
      (305411412354527 / 100000) := by
  exact
    packedTile65536 3054059776 3054190848 14 5996 55263 32 _ _ (545993 / 25000) (87359 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3054190848 :
    ThetaLowerSegment 3054190848 3054321920 (305411412354527 / 100000)
      (152712239544459 / 50000) := by
  exact
    packedTile65536 3054190848 3054321920 14 5983 55264 32 _ _ (2183977 / 100000) (109199 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3054321920 :
    ThetaLowerSegment 3054321920 3054452992 (152712239544459 / 50000)
      (305437550215203 / 100000) := by
  exact
    packedTile65536 3054321920 3054452992 14 5985 55265 32 _ _ (2183981 / 100000) (136499 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3054452992 :
    ThetaLowerSegment 3054452992 3054584064 (305437550215203 / 100000)
      (305450566765803 / 100000) := by
  exact
    packedTile65536 3054452992 3054584064 14 5960 55267 32 _ _ (436797 / 20000) (545997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3054584064 :
    ThetaLowerSegment 3054584064 3054715136 (305450566765803 / 100000)
      (305463705643627 / 100000) := by
  exact
    packedTile65536 3054584064 3054715136 14 6016 55268 32 _ _ (2183989 / 100000) (272999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3054715136 :
    ThetaLowerSegment 3054715136 3054846208 (305463705643627 / 100000)
      (61095356243141 / 20000) := by
  exact
    packedTile65536 3054715136 3054846208 14 5987 55269 32 _ _ (1091997 / 50000) (2183997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3054846208 :
    ThetaLowerSegment 3054846208 3054977280 (61095356243141 / 20000) (61097974856743 / 20000) := by
  exact
    packedTile65536 3054846208 3054977280 14 5995 55270 32 _ _ (1091999 / 50000) (2184001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3054977280 :
    ThetaLowerSegment 3054977280 3055108352 (61097974856743 / 20000)
      (305502984847721 / 100000) := by
  exact
    packedTile65536 3054977280 3055108352 14 6003 55271 32 _ _ (1092001 / 50000) (436801 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3055108352 :
    ThetaLowerSegment 3055108352 3055239424 (305502984847721 / 100000)
      (61103209915519 / 20000) := by
  exact
    packedTile65536 3055108352 3055239424 14 5982 55273 32 _ _ (2184007 / 100000) (218401 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3055239424 :
    ThetaLowerSegment 3055239424 3055370496 (61103209915519 / 20000)
      (305529162379639 / 100000) := by
  exact
    packedTile65536 3055239424 3055370496 14 6004 55274 32 _ _ (2184011 / 100000) (1092007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3055370496 :
    ThetaLowerSegment 3055370496 3055501568 (305529162379639 / 100000)
      (38192791771763 / 12500) := by
  exact
    packedTile65536 3055370496 3055501568 14 6031 55275 32 _ _ (436803 / 20000) (1092009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3055501568 :
    ThetaLowerSegment 3055501568 3055632640 (38192791771763 / 12500)
      (305555274486679 / 100000) := by
  exact
    packedTile65536 3055501568 3055632640 14 5925 55276 32 _ _ (2184019 / 100000) (1092011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3055632640 :
    ThetaLowerSegment 3055632640 3055763712 (305555274486679 / 100000)
      (305568439783351 / 100000) := by
  exact
    packedTile65536 3055632640 3055763712 14 6028 55277 32 _ _ (273003 / 12500) (2184027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3055763712 :
    ThetaLowerSegment 3055763712 3055894784 (305568439783351 / 100000) (12223262456943 / 4000) := by
  exact
    packedTile65536 3055763712 3055894784 14 6008 55278 32 _ _ (546007 / 25000) (2184031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3055894784 :
    ThetaLowerSegment 3055894784 3056025856 (12223262456943 / 4000) (61118950595371 / 20000) := by
  exact
    packedTile65536 3055894784 3056025856 14 6040 55280 32 _ _ (68251 / 3125) (436807 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056025856 :
    ThetaLowerSegment 3056025856 3056156928 (61118950595371 / 20000)
      (305607844094633 / 100000) := by
  exact
    packedTile65536 3056025856 3056156928 14 5994 55281 32 _ _ (2184037 / 100000) (54601 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056156928 :
    ThetaLowerSegment 3056156928 3056288000 (305607844094633 / 100000)
      (76405282404009 / 25000) := by
  exact
    packedTile65536 3056156928 3056288000 14 6083 55282 32 _ _ (2184041 / 100000) (546011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056288000 :
    ThetaLowerSegment 3056288000 3056419072 (76405282404009 / 25000) (152817127863243 / 50000) := by
  exact
    packedTile65536 3056288000 3056419072 14 6010 55283 32 _ _ (436809 / 20000) (136503 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056419072 :
    ThetaLowerSegment 3056419072 3056550144 (152817127863243 / 50000)
      (152823706218831 / 50000) := by
  exact
    packedTile65536 3056419072 3056550144 14 6024 55284 32 _ _ (2184049 / 100000) (546013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056550144 :
    ThetaLowerSegment 3056550144 3056681216 (152823706218831 / 50000)
      (152830356663261 / 50000) := by
  exact
    packedTile65536 3056550144 3056681216 14 6090 55286 32 _ _ (1092027 / 50000) (2184057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056681216 :
    ThetaLowerSegment 3056681216 3056812288 (152830356663261 / 50000) (30567387446003 / 10000) := by
  exact
    packedTile65536 3056681216 3056812288 14 6026 55287 32 _ _ (1092029 / 50000) (2184061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056812288 :
    ThetaLowerSegment 3056812288 3056943360 (30567387446003 / 10000) (152843506888511 / 50000) := by
  exact
    packedTile65536 3056812288 3056943360 14 6016 55288 32 _ _ (1092031 / 50000) (436813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056943360 :
    ThetaLowerSegment 3056943360 3057074432 (152843506888511 / 50000) (38212522962629 / 12500) := by
  exact
    packedTile65536 3056943360 3057074432 14 6030 55289 32 _ _ (2184067 / 100000) (218407 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3057074432 :
    ThetaLowerSegment 3057074432 3057205504 (38212522962629 / 12500)
      (305713259734109 / 100000) := by
  exact
    packedTile65536 3057074432 3057205504 14 5987 55290 32 _ _ (2184071 / 100000) (1092037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3057205504 :
    ThetaLowerSegment 3057205504 3057336576 (305713259734109 / 100000)
      (152863163527417 / 50000) := by
  exact
    packedTile65536 3057205504 3057336576 14 5983 55292 32 _ _ (87363 / 4000) (1092039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3057336576 :
    ThetaLowerSegment 3057336576 3057467648 (152863163527417 / 50000)
      (305739416240281 / 100000) := by
  exact
    packedTile65536 3057336576 3057467648 14 5993 55293 32 _ _ (2184079 / 100000) (1092041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3057467648 :
    ThetaLowerSegment 3057467648 3057598720 (305739416240281 / 100000)
      (305752470510349 / 100000) := by
  exact
    packedTile65536 3057467648 3057598720 14 5977 55294 32 _ _ (546021 / 25000) (2184087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3057598720 :
    ThetaLowerSegment 3057598720 3057729792 (305752470510349 / 100000)
      (305765540092941 / 100000) := by
  exact
    packedTile65536 3057598720 3057729792 14 5984 55295 32 _ _ (273011 / 12500) (2184091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3057729792 :
    ThetaLowerSegment 3057729792 3057860864 (305765540092941 / 100000)
      (61155703593521 / 20000) := by
  exact
    packedTile65536 3057729792 3057860864 14 5942 55296 32 _ _ (546023 / 25000) (436819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3057860864 :
    ThetaLowerSegment 3057860864 3057991936 (61155703593521 / 20000)
      (305791596340441 / 100000) := by
  exact
    packedTile65536 3057860864 3057991936 14 5988 55297 32 _ _ (2184097 / 100000) (21841 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3057991936 :
    ThetaLowerSegment 3057991936 3058123008 (305791596340441 / 100000)
      (305804805783289 / 100000) := by
  exact
    packedTile65536 3057991936 3058123008 14 6048 55299 32 _ _ (2184101 / 100000) (273013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3058123008 :
    ThetaLowerSegment 3058123008 3058254080 (305804805783289 / 100000)
      (305817823049089 / 100000) := by
  exact
    packedTile65536 3058123008 3058254080 14 5960 55300 32 _ _ (436821 / 20000) (546027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3058254080 :
    ThetaLowerSegment 3058254080 3058385152 (305817823049089 / 100000)
      (305830929893199 / 100000) := by
  exact
    packedTile65536 3058254080 3058385152 14 6001 55301 32 _ _ (218411 / 10000) (2184113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3058385152 :
    ThetaLowerSegment 3058385152 3058516224 (305830929893199 / 100000)
      (61168802110389 / 20000) := by
  exact
    packedTile65536 3058385152 3058516224 14 5989 55302 32 _ _ (1092057 / 50000) (2184117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3058516224 :
    ThetaLowerSegment 3058516224 3058647296 (61168802110389 / 20000) (12234278931691 / 4000) := by
  exact
    packedTile65536 3058516224 3058647296 14 5935 55303 32 _ _ (1092059 / 50000) (2184121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3058647296 :
    ThetaLowerSegment 3058647296 3058778368 (12234278931691 / 4000) (61174017788977 / 20000) := by
  exact
    packedTile65536 3058647296 3058778368 14 6005 55305 32 _ _ (1092061 / 50000) (17473 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3058778368 :
    ThetaLowerSegment 3058778368 3058909440 (61174017788977 / 20000)
      (305883272335457 / 100000) := by
  exact
    packedTile65536 3058778368 3058909440 14 6036 55306 32 _ _ (2184127 / 100000) (218413 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3058909440 :
    ThetaLowerSegment 3058909440 3059040512 (305883272335457 / 100000)
      (305896398962767 / 100000) := by
  exact
    packedTile65536 3058909440 3059040512 14 6010 55307 32 _ _ (2184131 / 100000) (1092067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3059040512 :
    ThetaLowerSegment 3059040512 3059171584 (305896398962767 / 100000)
      (76477386317833 / 25000) := by
  exact
    packedTile65536 3059040512 3059171584 14 6019 55308 32 _ _ (436827 / 20000) (1092069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3059171584 :
    ThetaLowerSegment 3059171584 3059302656 (76477386317833 / 25000) (152961274817469 / 50000) := by
  exact
    packedTile65536 3059171584 3059302656 14 5954 55309 32 _ _ (2184139 / 100000) (1092071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3059302656 :
    ThetaLowerSegment 3059302656 3059433728 (152961274817469 / 50000)
      (152967899326221 / 50000) := by
  exact
    packedTile65536 3059302656 3059433728 14 6066 55310 32 _ _ (136509 / 6250) (2184147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3059433728 :
    ThetaLowerSegment 3059433728 3059564800 (152967899326221 / 50000)
      (152974531491623 / 50000) := by
  exact
    packedTile65536 3059433728 3059564800 14 6073 55312 32 _ _ (546037 / 25000) (2184151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3059564800 :
    ThetaLowerSegment 3059564800 3059695872 (152974531491623 / 50000)
      (152981051185343 / 50000) := by
  exact
    packedTile65536 3059564800 3059695872 14 5970 55313 32 _ _ (273019 / 12500) (436831 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3059695872 :
    ThetaLowerSegment 3059695872 3059826944 (152981051185343 / 50000)
      (305975183286959 / 100000) := by
  exact
    packedTile65536 3059695872 3059826944 14 5989 55314 32 _ _ (2184157 / 100000) (13651 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3059826944 :
    ThetaLowerSegment 3059826944 3059958016 (305975183286959 / 100000)
      (76497066056797 / 25000) := by
  exact
    packedTile65536 3059826944 3059958016 14 5989 55315 32 _ _ (2184161 / 100000) (546041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3059958016 :
    ThetaLowerSegment 3059958016 3060089088 (76497066056797 / 25000)
      (306001463136283 / 100000) := by
  exact
    packedTile65536 3059958016 3060089088 14 6043 55316 32 _ _ (436833 / 20000) (273021 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3060089088 :
    ThetaLowerSegment 3060089088 3060220160 (306001463136283 / 100000)
      (153007261141367 / 50000) := by
  exact
    packedTile65536 3060089088 3060220160 14 5979 55318 32 _ _ (2184169 / 100000) (546043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3060220160 :
    ThetaLowerSegment 3060220160 3060351232 (153007261141367 / 50000) (38253428024819 / 12500) := by
  exact
    packedTile65536 3060220160 3060351232 14 5907 55319 32 _ _ (1092087 / 50000) (2184177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3060351232 :
    ThetaLowerSegment 3060351232 3060482304 (38253428024819 / 12500) (153020248251941 / 50000) := by
  exact
    packedTile65536 3060351232 3060482304 14 5985 55320 32 _ _ (1092089 / 50000) (2184181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3060482304 :
    ThetaLowerSegment 3060482304 3060613376 (153020248251941 / 50000)
      (153026787692849 / 50000) := by
  exact
    packedTile65536 3060482304 3060613376 14 5988 55321 32 _ _ (1092091 / 50000) (436837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3060613376 :
    ThetaLowerSegment 3060613376 3060744448 (153026787692849 / 50000)
      (306066774427739 / 100000) := by
  exact
    packedTile65536 3060613376 3060744448 14 6043 55322 32 _ _ (2184187 / 100000) (218419 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3060744448 :
    ThetaLowerSegment 3060744448 3060875520 (306066774427739 / 100000) (19129991790799 / 6250) := by
  exact
    packedTile65536 3060744448 3060875520 14 5995 55323 32 _ _ (2184191 / 100000) (1092097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3060875520 :
    ThetaLowerSegment 3060875520 3061006592 (19129991790799 / 6250) (76523258745061 / 25000) := by
  exact
    packedTile65536 3060875520 3061006592 14 6028 55325 32 _ _ (436839 / 20000) (1092099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3061006592 :
    ThetaLowerSegment 3061006592 3061137664 (76523258745061 / 25000) (30610582128119 / 10000) := by
  exact
    packedTile65536 3061006592 3061137664 14 5854 55326 32 _ _ (2184199 / 100000) (1092101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3061137664 :
    ThetaLowerSegment 3061137664 3061268736 (30610582128119 / 10000) (153059439226351 / 50000) := by
  exact
    packedTile65536 3061137664 3061268736 14 5978 55327 32 _ _ (546051 / 25000) (2184207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3061268736 :
    ThetaLowerSegment 3061268736 3061399808 (153059439226351 / 50000)
      (153066051916071 / 50000) := by
  exact
    packedTile65536 3061268736 3061399808 14 6055 55328 32 _ _ (136513 / 6250) (2184211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3061399808 :
    ThetaLowerSegment 3061399808 3061530880 (153066051916071 / 50000)
      (153072617657343 / 50000) := by
  exact
    packedTile65536 3061399808 3061530880 14 6012 55329 32 _ _ (546053 / 25000) (436843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3061530880 :
    ThetaLowerSegment 3061530880 3061661952 (153072617657343 / 50000)
      (306158216116317 / 100000) := by
  exact
    packedTile65536 3061530880 3061661952 14 5943 55331 32 _ _ (2184217 / 100000) (109211 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3061661952 :
    ThetaLowerSegment 3061661952 3061793024 (306158216116317 / 100000)
      (306171461232461 / 100000) := by
  exact
    packedTile65536 3061661952 3061793024 14 6064 55332 32 _ _ (2184221 / 100000) (68257 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3061793024 :
    ThetaLowerSegment 3061793024 3061924096 (306171461232461 / 100000)
      (153092280014893 / 50000) := by
  exact
    packedTile65536 3061793024 3061924096 14 5997 55333 32 _ _ (87369 / 4000) (546057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3061924096 :
    ThetaLowerSegment 3061924096 3062055168 (153092280014893 / 50000)
      (153098732227359 / 50000) := by
  exact
    packedTile65536 3061924096 3062055168 14 5908 55334 32 _ _ (2184229 / 100000) (273029 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3062055168 :
    ThetaLowerSegment 3062055168 3062186240 (153098732227359 / 50000)
      (153105365746017 / 50000) := by
  exact
    packedTile65536 3062055168 3062186240 14 6074 55335 32 _ _ (1092117 / 50000) (2184237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3062186240 :
    ThetaLowerSegment 3062186240 3062317312 (153105365746017 / 50000)
      (153111824537783 / 50000) := by
  exact
    packedTile65536 3062186240 3062317312 14 5914 55337 32 _ _ (1092119 / 50000) (2184241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3062317312 :
    ThetaLowerSegment 3062317312 3062448384 (153111824537783 / 50000) (76559255797333 / 25000) := by
  exact
    packedTile65536 3062317312 3062448384 14 6123 55338 32 _ _ (1092121 / 50000) (436849 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3062448384 :
    ThetaLowerSegment 3062448384 3062579456 (76559255797333 / 25000) (76562471008917 / 25000) := by
  exact
    packedTile65536 3062448384 3062579456 14 5888 55339 32 _ _ (2184247 / 100000) (8737 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3062579456 :
    ThetaLowerSegment 3062579456 3062710528 (76562471008917 / 25000)
      (306262930566891 / 100000) := by
  exact
    packedTile65536 3062579456 3062710528 14 5973 55340 32 _ _ (2184251 / 100000) (1092127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3062710528 :
    ThetaLowerSegment 3062710528 3062841600 (306262930566891 / 100000)
      (153137979823983 / 50000) := by
  exact
    packedTile65536 3062710528 3062841600 14 5965 55341 32 _ _ (436851 / 20000) (1092129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3062841600 :
    ThetaLowerSegment 3062841600 3062972672 (153137979823983 / 50000)
      (153144585023199 / 50000) := by
  exact
    packedTile65536 3062841600 3062972672 14 6048 55342 32 _ _ (2184259 / 100000) (1092131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3062972672 :
    ThetaLowerSegment 3062972672 3063103744 (153144585023199 / 50000)
      (153151215356571 / 50000) := by
  exact
    packedTile65536 3062972672 3063103744 14 6071 55344 32 _ _ (273033 / 12500) (2184267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3063103744 :
    ThetaLowerSegment 3063103744 3063234816 (153151215356571 / 50000)
      (153157843517817 / 50000) := by
  exact
    packedTile65536 3063103744 3063234816 14 6069 55345 32 _ _ (546067 / 25000) (2184271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3063234816 :
    ThetaLowerSegment 3063234816 3063365888 (153157843517817 / 50000)
      (153164479336153 / 50000) := by
  exact
    packedTile65536 3063234816 3063365888 14 6076 55346 32 _ _ (136517 / 6250) (87371 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3063365888 :
    ThetaLowerSegment 3063365888 3063496960 (153164479336153 / 50000)
      (306342258734959 / 100000) := by
  exact
    packedTile65536 3063365888 3063496960 14 6089 55347 32 _ _ (2184277 / 100000) (54607 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3063496960 :
    ThetaLowerSegment 3063496960 3063628032 (306342258734959 / 100000)
      (306355447423637 / 100000) := by
  exact
    packedTile65536 3063496960 3063628032 14 6038 55348 32 _ _ (2184281 / 100000) (546071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3063628032 :
    ThetaLowerSegment 3063628032 3063759104 (306355447423637 / 100000)
      (306368601187907 / 100000) := by
  exact
    packedTile65536 3063628032 3063759104 14 6022 55350 32 _ _ (436857 / 20000) (68259 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3063759104 :
    ThetaLowerSegment 3063759104 3063890176 (306368601187907 / 100000)
      (153190913528901 / 50000) := by
  exact
    packedTile65536 3063759104 3063890176 14 6055 55351 32 _ _ (2184289 / 100000) (546073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3063890176 :
    ThetaLowerSegment 3063890176 3064021248 (153190913528901 / 50000)
      (153197462042313 / 50000) := by
  exact
    packedTile65536 3063890176 3064021248 14 5996 55352 32 _ _ (1092147 / 50000) (2184297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064021248 :
    ThetaLowerSegment 3064021248 3064152320 (153197462042313 / 50000) (30640795997509 / 10000) := by
  exact
    packedTile65536 3064021248 3064152320 14 5968 55353 32 _ _ (1092149 / 50000) (2184301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064152320 :
    ThetaLowerSegment 3064152320 3064283392 (30640795997509 / 10000) (30642106578709 / 10000) := by
  exact
    packedTile65536 3064152320 3064283392 14 6000 55354 32 _ _ (1092151 / 50000) (436861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064283392 :
    ThetaLowerSegment 3064283392 3064414464 (30642106578709 / 10000) (383042537054 / 125) := by
  exact
    packedTile65536 3064283392 3064414464 14 5935 55355 32 _ _ (1092153 / 50000) (2184309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064414464 :
    ThetaLowerSegment 3064414464 3064545536 (383042537054 / 125) (306447120219023 / 100000) := by
  exact
    packedTile65536 3064414464 3064545536 14 5993 55357 32 _ _ (2184311 / 100000) (1092157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064545536 :
    ThetaLowerSegment 3064545536 3064676608 (306447120219023 / 100000)
      (153230197150639 / 50000) := by
  exact
    packedTile65536 3064545536 3064676608 14 6077 55358 32 _ _ (436863 / 20000) (1092159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064676608 :
    ThetaLowerSegment 3064676608 3064807680 (153230197150639 / 50000) (61294679510457 / 20000) := by
  exact
    packedTile65536 3064676608 3064807680 14 5953 55359 32 _ _ (2184319 / 100000) (1092161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064807680 :
    ThetaLowerSegment 3064807680 3064938752 (61294679510457 / 20000)
      (306486466362777 / 100000) := by
  exact
    packedTile65536 3064807680 3064938752 14 5983 55360 32 _ _ (546081 / 25000) (2184327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064938752 :
    ThetaLowerSegment 3064938752 3065069824 (306486466362777 / 100000)
      (306499646597929 / 100000) := by
  exact
    packedTile65536 3064938752 3065069824 14 6034 55361 32 _ _ (273041 / 12500) (2184331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3065069824 :
    ThetaLowerSegment 3065069824 3065200896 (306499646597929 / 100000)
      (61302538722593 / 20000) := by
  exact
    packedTile65536 3065069824 3065200896 14 5973 55363 32 _ _ (546083 / 25000) (436867 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3065200896 :
    ThetaLowerSegment 3065200896 3065331968 (61302538722593 / 20000)
      (306525926320453 / 100000) := by
  exact
    packedTile65536 3065200896 3065331968 14 6058 55364 32 _ _ (136521 / 6250) (2184339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3065331968 :
    ThetaLowerSegment 3065331968 3065463040 (306525926320453 / 100000)
      (306539023629089 / 100000) := by
  exact
    packedTile65536 3065331968 3065463040 14 5996 55365 32 _ _ (2184341 / 100000) (273043 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3065463040 :
    ThetaLowerSegment 3065463040 3065594112 (306539023629089 / 100000)
      (153276140209447 / 50000) := by
  exact
    packedTile65536 3065463040 3065594112 14 6069 55366 32 _ _ (436869 / 20000) (546087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3065594112 :
    ThetaLowerSegment 3065594112 3065725184 (153276140209447 / 50000)
      (306565419278129 / 100000) := by
  exact
    packedTile65536 3065594112 3065725184 14 6015 55367 32 _ _ (2184349 / 100000) (68261 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3065725184 :
    ThetaLowerSegment 3065725184 3065856256 (306565419278129 / 100000)
      (306578713250487 / 100000) := by
  exact
    packedTile65536 3065725184 3065856256 14 6086 55368 32 _ _ (2184353 / 100000) (546089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3065856256 :
    ThetaLowerSegment 3065856256 3065987328 (306578713250487 / 100000)
      (306591775711327 / 100000) := by
  exact
    packedTile65536 3065856256 3065987328 14 5980 55370 32 _ _ (1092179 / 50000) (2184361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3065987328 :
    ThetaLowerSegment 3065987328 3066118400 (306591775711327 / 100000)
      (306604757374693 / 100000) := by
  exact
    packedTile65536 3065987328 3066118400 14 5943 55371 32 _ _ (1092181 / 50000) (436873 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3066118400 :
    ThetaLowerSegment 3066118400 3066249472 (306604757374693 / 100000)
      (306617990263921 / 100000) := by
  exact
    packedTile65536 3066118400 3066249472 14 6058 55372 32 _ _ (1092183 / 50000) (2184369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3066249472 :
    ThetaLowerSegment 3066249472 3066380544 (306617990263921 / 100000)
      (153315573365227 / 50000) := by
  exact
    packedTile65536 3066249472 3066380544 14 6023 55373 32 _ _ (2184371 / 100000) (1092187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3066380544 :
    ThetaLowerSegment 3066380544 3066511616 (153315573365227 / 50000)
      (306644421177329 / 100000) := by
  exact
    packedTile65536 3066380544 3066511616 14 6077 55374 32 _ _ (699 / 32) (1092189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3066511616 :
    ThetaLowerSegment 3066511616 3066642688 (306644421177329 / 100000)
      (306657348332251 / 100000) := by
  exact
    packedTile65536 3066511616 3066642688 14 5918 55376 32 _ _ (2184379 / 100000) (1092191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3066642688 :
    ThetaLowerSegment 3066642688 3066773760 (306657348332251 / 100000)
      (306670480842847 / 100000) := by
  exact
    packedTile65536 3066642688 3066773760 14 6012 55377 32 _ _ (2184383 / 100000) (1092193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3066773760 :
    ThetaLowerSegment 3066773760 3066904832 (306670480842847 / 100000)
      (306683528192371 / 100000) := by
  exact
    packedTile65536 3066773760 3066904832 14 5973 55378 32 _ _ (546097 / 25000) (2184391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3066904832 :
    ThetaLowerSegment 3066904832 3067035904 (306683528192371 / 100000)
      (306696669494643 / 100000) := by
  exact
    packedTile65536 3066904832 3067035904 14 6016 55379 32 _ _ (273049 / 12500) (436879 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3067035904 :
    ThetaLowerSegment 3067035904 3067166976 (306696669494643 / 100000)
      (306709985572659 / 100000) := by
  exact
    packedTile65536 3067035904 3067166976 14 6096 55380 32 _ _ (546099 / 25000) (2184399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3067166976 :
    ThetaLowerSegment 3067166976 3067298048 (306709985572659 / 100000)
      (61344594804201 / 20000) := by
  exact
    packedTile65536 3067166976 3067298048 14 5946 55382 32 _ _ (2184401 / 100000) (546101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3067298048 :
    ThetaLowerSegment 3067298048 3067429120 (61344594804201 / 20000) (61347203857533 / 20000) := by
  exact
    packedTile65536 3067298048 3067429120 14 5972 55383 32 _ _ (436881 / 20000) (273051 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3067429120 :
    ThetaLowerSegment 3067429120 3067560192 (61347203857533 / 20000) (1917182786776 / 625) := by
  exact
    packedTile65536 3067429120 3067560192 14 6055 55384 32 _ _ (2184409 / 100000) (546103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3067560192 :
    ThetaLowerSegment 3067560192 3067691264 (1917182786776 / 625) (306762249694749 / 100000) := by
  exact
    packedTile65536 3067560192 3067691264 14 5953 55385 32 _ _ (2184413 / 100000) (68263 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3067691264 :
    ThetaLowerSegment 3067691264 3067822336 (306762249694749 / 100000)
      (306775277563701 / 100000) := by
  exact
    packedTile65536 3067691264 3067822336 14 5964 55386 32 _ _ (1092209 / 50000) (2184421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3067822336 :
    ThetaLowerSegment 3067822336 3067953408 (306775277563701 / 100000)
      (306788436521829 / 100000) := by
  exact
    packedTile65536 3067822336 3067953408 14 6024 55387 32 _ _ (1092211 / 50000) (87377 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3067953408 :
    ThetaLowerSegment 3067953408 3068084480 (306788436521829 / 100000) (12272065742457 / 4000) := by
  exact
    packedTile65536 3067953408 3068084480 14 6046 55389 32 _ _ (1092213 / 50000) (2184429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3068084480 :
    ThetaLowerSegment 3068084480 3068215552 (12272065742457 / 4000) (61362948280741 / 20000) := by
  exact
    packedTile65536 3068084480 3068215552 14 5996 55390 32 _ _ (218443 / 10000) (2184433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3068215552 :
    ThetaLowerSegment 3068215552 3068346624 (61362948280741 / 20000) (30682785456701 / 10000) := by
  exact
    packedTile65536 3068215552 3068346624 14 6003 55391 32 _ _ (436887 / 20000) (1092219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3068346624 :
    ThetaLowerSegment 3068346624 3068477696 (30682785456701 / 10000) (76710230470277 / 25000) := by
  exact
    packedTile65536 3068346624 3068477696 14 5982 55392 32 _ _ (2184439 / 100000) (1092221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3068477696 :
    ThetaLowerSegment 3068477696 3068608768 (76710230470277 / 25000)
      (306854030723551 / 100000) := by
  exact
    packedTile65536 3068477696 3068608768 14 6001 55393 32 _ _ (2184443 / 100000) (1092223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3068608768 :
    ThetaLowerSegment 3068608768 3068739840 (306854030723551 / 100000)
      (61373415686291 / 20000) := by
  exact
    packedTile65536 3068608768 3068739840 14 5973 55395 32 _ _ (68264 / 3125) (2184451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3068739840 :
    ThetaLowerSegment 3068739840 3068870912 (61373415686291 / 20000)
      (306880045338527 / 100000) := by
  exact
    packedTile65536 3068739840 3068870912 14 5936 55396 32 _ _ (546113 / 25000) (436891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3068870912 :
    ThetaLowerSegment 3068870912 3069001984 (306880045338527 / 100000)
      (306893250375047 / 100000) := by
  exact
    packedTile65536 3068870912 3069001984 14 6045 55397 32 _ _ (273057 / 12500) (2184459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069001984 :
    ThetaLowerSegment 3069001984 3069133056 (306893250375047 / 100000)
      (306906328737067 / 100000) := by
  exact
    packedTile65536 3069001984 3069133056 14 5987 55398 32 _ _ (109223 / 5000) (2184463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069133056 :
    ThetaLowerSegment 3069133056 3069264128 (306906328737067 / 100000)
      (306919522905667 / 100000) := by
  exact
    packedTile65536 3069133056 3069264128 14 6040 55399 32 _ _ (436893 / 20000) (546117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069264128 :
    ThetaLowerSegment 3069264128 3069395200 (306919522905667 / 100000)
      (306932708360551 / 100000) := by
  exact
    packedTile65536 3069264128 3069395200 14 6036 55400 32 _ _ (2184469 / 100000) (273059 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069395200 :
    ThetaLowerSegment 3069395200 3069526272 (306932708360551 / 100000)
      (153472871555471 / 50000) := by
  exact
    packedTile65536 3069395200 3069526272 14 5967 55402 32 _ _ (2184473 / 100000) (546119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069526272 :
    ThetaLowerSegment 3069526272 3069657344 (153472871555471 / 50000) (61391787033509 / 20000) := by
  exact
    packedTile65536 3069526272 3069657344 14 6039 55403 32 _ _ (2184477 / 100000) (13653 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069657344 :
    ThetaLowerSegment 3069657344 3069788416 (61391787033509 / 20000)
      (306972127254343 / 100000) := by
  exact
    packedTile65536 3069657344 3069788416 14 6039 55404 32 _ _ (1092241 / 50000) (436897 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069788416 :
    ThetaLowerSegment 3069788416 3069919488 (306972127254343 / 100000)
      (306985297520437 / 100000) := by
  exact
    packedTile65536 3069788416 3069919488 14 6029 55405 32 _ _ (1092243 / 50000) (2184489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069919488 :
    ThetaLowerSegment 3069919488 3070050560 (306985297520437 / 100000)
      (306998310527367 / 100000) := by
  exact
    packedTile65536 3069919488 3070050560 14 5957 55406 32 _ _ (218449 / 10000) (2184493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3070050560 :
    ThetaLowerSegment 3070050560 3070181632 (306998310527367 / 100000) (491218117693 / 160) := by
  exact
    packedTile65536 3070050560 3070181632 14 5957 55408 32 _ _ (1092247 / 50000) (2184497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3070181632 :
    ThetaLowerSegment 3070181632 3070312704 (491218117693 / 160) (153512196707821 / 50000) := by
  exact
    packedTile65536 3070181632 3070312704 14 5983 55409 32 _ _ (2184499 / 100000) (1092251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3070312704 :
    ThetaLowerSegment 3070312704 3070443776 (153512196707821 / 50000) (19189845142417 / 6250) := by
  exact
    packedTile65536 3070312704 3070443776 14 6010 55410 32 _ _ (2184503 / 100000) (1092253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3070443776 :
    ThetaLowerSegment 3070443776 3070574848 (19189845142417 / 6250) (30705083466433 / 10000) := by
  exact
    packedTile65536 3070443776 3070574848 14 6094 55411 32 _ _ (2184507 / 100000) (218451 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3070574848 :
    ThetaLowerSegment 3070574848 3070705920 (30705083466433 / 10000) (153531968683653 / 50000) := by
  exact
    packedTile65536 3070574848 3070705920 14 5998 55412 32 _ _ (68266 / 3125) (436903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3070705920 :
    ThetaLowerSegment 3070705920 3070836992 (153531968683653 / 50000)
      (153538491648429 / 50000) := by
  exact
    packedTile65536 3070705920 3070836992 14 5972 55413 32 _ _ (546129 / 25000) (2184519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3070836992 :
    ThetaLowerSegment 3070836992 3070968064 (153538491648429 / 50000)
      (153544989503169 / 50000) := by
  exact
    packedTile65536 3070836992 3070968064 14 5949 55415 32 _ _ (54613 / 2500) (2184523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3070968064 :
    ThetaLowerSegment 3070968064 3071099136 (153544989503169 / 50000)
      (153551511399571 / 50000) := by
  exact
    packedTile65536 3070968064 3071099136 14 5971 55416 32 _ _ (546131 / 25000) (2184527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3071099136 :
    ThetaLowerSegment 3071099136 3071230208 (153551511399571 / 50000) (76779035770079 / 25000) := by
  exact
    packedTile65536 3071099136 3071230208 14 6006 55417 32 _ _ (2184529 / 100000) (546133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3071230208 :
    ThetaLowerSegment 3071230208 3071361280 (76779035770079 / 25000)
      (307129221879387 / 100000) := by
  exact
    packedTile65536 3071230208 3071361280 14 5987 55418 32 _ _ (2184533 / 100000) (273067 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3071361280 :
    ThetaLowerSegment 3071361280 3071492352 (307129221879387 / 100000) (15357113069037 / 5000) := by
  exact
    packedTile65536 3071361280 3071492352 14 5969 55419 32 _ _ (2184537 / 100000) (109227 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3071492352 :
    ThetaLowerSegment 3071492352 3071623424 (15357113069037 / 5000) (153577699605157 / 50000) := by
  exact
    packedTile65536 3071492352 3071623424 14 6014 55421 32 _ _ (2184541 / 100000) (68267 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3071623424 :
    ThetaLowerSegment 3071623424 3071754496 (153577699605157 / 50000)
      (153584294749531 / 50000) := by
  exact
    packedTile65536 3071623424 3071754496 14 6038 55422 32 _ _ (1092273 / 50000) (2184549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3071754496 :
    ThetaLowerSegment 3071754496 3071885568 (153584294749531 / 50000) (38397699811789 / 12500) := by
  exact
    packedTile65536 3071754496 3071885568 14 5955 55423 32 _ _ (43691 / 2000) (2184553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3071885568 :
    ThetaLowerSegment 3071885568 3072016640 (38397699811789 / 12500) (153597410799837 / 50000) := by
  exact
    packedTile65536 3071885568 3072016640 14 6053 55424 32 _ _ (1092277 / 50000) (2184557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3072016640 :
    ThetaLowerSegment 3072016640 3072147712 (153597410799837 / 50000)
      (153603995060663 / 50000) := by
  exact
    packedTile65536 3072016640 3072147712 14 6028 55425 32 _ _ (2184559 / 100000) (1092281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3072147712 :
    ThetaLowerSegment 3072147712 3072278784 (153603995060663 / 50000) (38402645379527 / 12500) := by
  exact
    packedTile65536 3072147712 3072278784 14 6030 55426 32 _ _ (2184563 / 100000) (1092283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3072278784 :
    ThetaLowerSegment 3072278784 3072409856 (38402645379527 / 12500) (76808539210183 / 25000) := by
  exact
    packedTile65536 3072278784 3072409856 14 5948 55428 32 _ _ (2184567 / 100000) (218457 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3072409856 :
    ThetaLowerSegment 3072409856 3072540928 (76808539210183 / 25000) (153623625579653 / 50000) := by
  exact
    packedTile65536 3072409856 3072540928 14 5994 55429 32 _ _ (2184571 / 100000) (1092287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3072540928 :
    ThetaLowerSegment 3072540928 3072672000 (153623625579653 / 50000) (30726058581121 / 10000) := by
  exact
    packedTile65536 3072540928 3072672000 14 6104 55430 32 _ _ (68268 / 3125) (2184579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3072672000 :
    ThetaLowerSegment 3072672000 3072803072 (30726058581121 / 10000) (30727393796417 / 10000) := by
  exact
    packedTile65536 3072672000 3072803072 14 6112 55431 32 _ _ (109229 / 5000) (2184583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3072803072 :
    ThetaLowerSegment 3072803072 3072934144 (30727393796417 / 10000) (6145741783197 / 2000) := by
  exact
    packedTile65536 3072803072 3072934144 14 6020 55432 32 _ _ (273073 / 12500) (2184587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3072934144 :
    ThetaLowerSegment 3072934144 3073065216 (6145741783197 / 2000) (153650078682633 / 50000) := by
  exact
    packedTile65536 3072934144 3073065216 14 5982 55434 32 _ _ (546147 / 25000) (2184591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073065216 :
    ThetaLowerSegment 3073065216 3073196288 (153650078682633 / 50000)
      (153656676153493 / 50000) := by
  exact
    packedTile65536 3073065216 3073196288 14 6040 55435 32 _ _ (2184593 / 100000) (546149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073196288 :
    ThetaLowerSegment 3073196288 3073327360 (153656676153493 / 50000) (30732652979609 / 10000) := by
  exact
    packedTile65536 3073196288 3073327360 14 6032 55436 32 _ _ (2184597 / 100000) (10923 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073327360 :
    ThetaLowerSegment 3073327360 3073458432 (30732652979609 / 10000)
      (307339578417863 / 100000) := by
  exact
    packedTile65536 3073327360 3073458432 14 5973 55437 32 _ _ (2184601 / 100000) (546151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073458432 :
    ThetaLowerSegment 3073458432 3073589504 (307339578417863 / 100000)
      (76838176427327 / 25000) := by
  exact
    packedTile65536 3073458432 3073589504 14 6009 55438 32 _ _ (436921 / 20000) (68269 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073589504 :
    ThetaLowerSegment 3073589504 3073720576 (76838176427327 / 25000) (38420719571181 / 12500) := by
  exact
    packedTile65536 3073589504 3073720576 14 5974 55439 32 _ _ (218461 / 10000) (2184613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073720576 :
    ThetaLowerSegment 3073720576 3073851648 (38420719571181 / 12500) (153689444142101 / 50000) := by
  exact
    packedTile65536 3073720576 3073851648 14 6011 55441 32 _ _ (1092307 / 50000) (2184617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073851648 :
    ThetaLowerSegment 3073851648 3073982720 (153689444142101 / 50000) (15369597724223 / 5000) := by
  exact
    packedTile65536 3073851648 3073982720 14 5981 55442 32 _ _ (1092309 / 50000) (2184621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073982720 :
    ThetaLowerSegment 3073982720 3074113792 (15369597724223 / 5000) (9606411880814 / 3125) := by
  exact
    packedTile65536 3073982720 3074113792 14 6054 55443 32 _ _ (1092311 / 50000) (17477 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3074113792 :
    ThetaLowerSegment 3074113792 3074244864 (9606411880814 / 3125) (9606824775317 / 3125) := by
  exact
    packedTile65536 3074113792 3074244864 14 6048 55444 32 _ _ (2184627 / 100000) (218463 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3074244864 :
    ThetaLowerSegment 3074244864 3074375936 (9606824775317 / 3125) (12297260111231 / 4000) := by
  exact
    packedTile65536 3074244864 3074375936 14 6001 55445 32 _ _ (2184631 / 100000) (1092317 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3074375936 :
    ThetaLowerSegment 3074375936 3074507008 (12297260111231 / 4000) (30744456034417 / 10000) := by
  exact
    packedTile65536 3074375936 3074507008 14 5977 55447 32 _ _ (436927 / 20000) (1092319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3074507008 :
    ThetaLowerSegment 3074507008 3074638080 (30744456034417 / 10000) (30745783858609 / 10000) := by
  exact
    packedTile65536 3074507008 3074638080 14 6078 55448 32 _ _ (13654 / 625) (2184643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3074638080 :
    ThetaLowerSegment 3074638080 3074769152 (30745783858609 / 10000) (153735469948079 / 50000) := by
  exact
    packedTile65536 3074638080 3074769152 14 5997 55449 32 _ _ (546161 / 25000) (2184647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3074769152 :
    ThetaLowerSegment 3074769152 3074900224 (153735469948079 / 50000)
      (153742005322571 / 50000) := by
  exact
    packedTile65536 3074769152 3074900224 14 5983 55450 32 _ _ (273081 / 12500) (2184651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3074900224 :
    ThetaLowerSegment 3074900224 3075031296 (153742005322571 / 50000)
      (153748556001593 / 50000) := by
  exact
    packedTile65536 3074900224 3075031296 14 5997 55451 32 _ _ (546163 / 25000) (436931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3075031296 :
    ThetaLowerSegment 3075031296 3075162368 (153748556001593 / 50000) (61502029570301 / 20000) := by
  exact
    packedTile65536 3075031296 3075162368 14 5967 55452 32 _ _ (2184657 / 100000) (109233 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3075162368 :
    ThetaLowerSegment 3075162368 3075293440 (61502029570301 / 20000)
      (307523264556149 / 100000) := by
  exact
    packedTile65536 3075162368 3075293440 14 6004 55454 32 _ _ (2184661 / 100000) (273083 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3075293440 :
    ThetaLowerSegment 3075293440 3075424512 (307523264556149 / 100000)
      (307536337591509 / 100000) := by
  exact
    packedTile65536 3075293440 3075424512 14 5984 55455 32 _ _ (436933 / 20000) (546167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3075424512 :
    ThetaLowerSegment 3075424512 3075555584 (307536337591509 / 100000) (9610919560734 / 3125) := by
  exact
    packedTile65536 3075424512 3075555584 14 5991 55456 32 _ _ (2184669 / 100000) (68271 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3075555584 :
    ThetaLowerSegment 3075555584 3075686656 (9610919560734 / 3125) (153781252793363 / 50000) := by
  exact
    packedTile65536 3075555584 3075686656 14 5987 55457 32 _ _ (1092337 / 50000) (2184677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3075686656 :
    ThetaLowerSegment 3075686656 3075817728 (153781252793363 / 50000)
      (153787835228177 / 50000) := by
  exact
    packedTile65536 3075686656 3075817728 14 6026 55458 32 _ _ (1092339 / 50000) (2184681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3075817728 :
    ThetaLowerSegment 3075817728 3075948800 (153787835228177 / 50000)
      (153794367427357 / 50000) := by
  exact
    packedTile65536 3075817728 3075948800 14 5980 55460 32 _ _ (1092341 / 50000) (436937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3075948800 :
    ThetaLowerSegment 3075948800 3076079872 (153794367427357 / 50000)
      (153800976102507 / 50000) := by
  exact
    packedTile65536 3075948800 3076079872 14 6050 55461 32 _ _ (1092343 / 50000) (2184689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3076079872 :
    ThetaLowerSegment 3076079872 3076210944 (153800976102507 / 50000)
      (153807573869327 / 50000) := by
  exact
    packedTile65536 3076079872 3076210944 14 6040 55462 32 _ _ (2184691 / 100000) (1092347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3076210944 :
    ThetaLowerSegment 3076210944 3076342016 (153807573869327 / 50000) (19226767905899 / 6250) := by
  exact
    packedTile65536 3076210944 3076342016 14 6014 55463 32 _ _ (436939 / 20000) (1092349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3076342016 :
    ThetaLowerSegment 3076342016 3076473088 (19226767905899 / 6250) (76910311532213 / 25000) := by
  exact
    packedTile65536 3076342016 3076473088 14 5932 55464 32 _ _ (2184699 / 100000) (1092351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3076473088 :
    ThetaLowerSegment 3076473088 3076604160 (76910311532213 / 25000) (76913558000871 / 25000) := by
  exact
    packedTile65536 3076473088 3076604160 14 5944 55465 32 _ _ (2184703 / 100000) (1092353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3076604160 :
    ThetaLowerSegment 3076604160 3076735232 (76913558000871 / 25000) (76916861279367 / 25000) := by
  exact
    packedTile65536 3076604160 3076735232 14 6048 55467 32 _ _ (546177 / 25000) (2184711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3076735232 :
    ThetaLowerSegment 3076735232 3076866304 (76916861279367 / 25000) (76920166748623 / 25000) := by
  exact
    packedTile65536 3076735232 3076866304 14 6052 55468 32 _ _ (273089 / 12500) (436943 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3076866304 :
    ThetaLowerSegment 3076866304 3076997376 (76920166748623 / 25000) (38461712353179 / 12500) := by
  exact
    packedTile65536 3076866304 3076997376 14 5965 55469 32 _ _ (546179 / 25000) (2184719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3076997376 :
    ThetaLowerSegment 3076997376 3077128448 (38461712353179 / 12500) (153853340218807 / 50000) := by
  exact
    packedTile65536 3076997376 3077128448 14 5942 55470 32 _ _ (2184721 / 100000) (546181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3077128448 :
    ThetaLowerSegment 3077128448 3077259520 (153853340218807 / 50000) (19232479425779 / 6250) := by
  exact
    packedTile65536 3077128448 3077259520 14 5946 55471 32 _ _ (87389 / 4000) (273091 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3077259520 :
    ThetaLowerSegment 3077259520 3077390592 (19232479425779 / 6250) (307732759523903 / 100000) := by
  exact
    packedTile65536 3077259520 3077390592 14 5991 55473 32 _ _ (2184729 / 100000) (546183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3077390592 :
    ThetaLowerSegment 3077390592 3077521664 (307732759523903 / 100000) (12309833318647 / 4000) := by
  exact
    packedTile65536 3077390592 3077521664 14 5984 55474 32 _ _ (2184733 / 100000) (68273 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3077521664 :
    ThetaLowerSegment 3077521664 3077652736 (12309833318647 / 4000) (307758871482559 / 100000) := by
  exact
    packedTile65536 3077521664 3077652736 14 5968 55475 32 _ _ (1092369 / 50000) (2184741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3077652736 :
    ThetaLowerSegment 3077652736 3077783808 (307758871482559 / 100000)
      (307771905653331 / 100000) := by
  exact
    packedTile65536 3077652736 3077783808 14 5966 55476 32 _ _ (1092371 / 50000) (436949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3077783808 :
    ThetaLowerSegment 3077783808 3077914880 (307771905653331 / 100000)
      (307784950771697 / 100000) := by
  exact
    packedTile65536 3077783808 3077914880 14 5971 55477 32 _ _ (1092373 / 50000) (2184749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3077914880 :
    ThetaLowerSegment 3077914880 3078045952 (307784950771697 / 100000)
      (307798089858197 / 100000) := by
  exact
    packedTile65536 3077914880 3078045952 14 6014 55478 32 _ _ (8739 / 400) (2184753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3078045952 :
    ThetaLowerSegment 3078045952 3078177024 (307798089858197 / 100000)
      (153905602471231 / 50000) := by
  exact
    packedTile65536 3078045952 3078177024 14 6003 55480 32 _ _ (436951 / 20000) (1092379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3078177024 :
    ThetaLowerSegment 3078177024 3078308096 (153905602471231 / 50000)
      (307824477353387 / 100000) := by
  exact
    packedTile65536 3078177024 3078308096 14 6075 55481 32 _ _ (2184759 / 100000) (1092381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3078308096 :
    ThetaLowerSegment 3078308096 3078439168 (307824477353387 / 100000)
      (307837612148543 / 100000) := by
  exact
    packedTile65536 3078308096 3078439168 14 6012 55482 32 _ _ (2184763 / 100000) (1092383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3078439168 :
    ThetaLowerSegment 3078439168 3078570240 (307837612148543 / 100000)
      (61570129293693 / 20000) := by
  exact
    packedTile65536 3078439168 3078570240 14 5966 55483 32 _ _ (2184767 / 100000) (218477 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3078570240 :
    ThetaLowerSegment 3078570240 3078701312 (61570129293693 / 20000)
      (307863936436541 / 100000) := by
  exact
    packedTile65536 3078570240 3078701312 14 6083 55484 32 _ _ (546193 / 25000) (87391 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3078701312 :
    ThetaLowerSegment 3078701312 3078832384 (307863936436541 / 100000)
      (307877047277317 / 100000) := by
  exact
    packedTile65536 3078701312 3078832384 14 6001 55486 32 _ _ (273097 / 12500) (2184779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3078832384 :
    ThetaLowerSegment 3078832384 3078963456 (307877047277317 / 100000)
      (307890086044357 / 100000) := by
  exact
    packedTile65536 3078832384 3078963456 14 5968 55487 32 _ _ (109239 / 5000) (2184783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3078963456 :
    ThetaLowerSegment 3078963456 3079094528 (307890086044357 / 100000)
      (307902928204709 / 100000) := by
  exact
    packedTile65536 3078963456 3079094528 14 5878 55488 32 _ _ (136549 / 6250) (2184787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3079094528 :
    ThetaLowerSegment 3079094528 3079225600 (307902928204709 / 100000)
      (30791610029759 / 10000) := by
  exact
    packedTile65536 3079094528 3079225600 14 6029 55489 32 _ _ (2184789 / 100000) (273099 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3079225600 :
    ThetaLowerSegment 3079225600 3079356672 (30791610029759 / 10000) (61585857104669 / 20000) := by
  exact
    packedTile65536 3079225600 3079356672 14 6035 55490 32 _ _ (2184793 / 100000) (546199 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3079356672 :
    ThetaLowerSegment 3079356672 3079487744 (61585857104669 / 20000) (76985619878107 / 25000) := by
  exact
    packedTile65536 3079356672 3079487744 14 6039 55491 32 _ _ (2184797 / 100000) (2731 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3079487744 :
    ThetaLowerSegment 3079487744 3079618816 (76985619878107 / 25000) (19247227000903 / 6250) := by
  exact
    packedTile65536 3079487744 3079618816 14 6020 55493 32 _ _ (2184801 / 100000) (546201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3079618816 :
    ThetaLowerSegment 3079618816 3079749888 (19247227000903 / 6250) (153984321267089 / 50000) := by
  exact
    packedTile65536 3079618816 3079749888 14 5955 55494 32 _ _ (1092403 / 50000) (2184809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3079749888 :
    ThetaLowerSegment 3079749888 3079880960 (153984321267089 / 50000)
      (153990880066709 / 50000) := by
  exact
    packedTile65536 3079749888 3079880960 14 6004 55495 32 _ _ (218481 / 10000) (2184813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3079880960 :
    ThetaLowerSegment 3079880960 3080012032 (153990880066709 / 50000) (9624841636782 / 3125) := by
  exact
    packedTile65536 3079880960 3080012032 14 6029 55496 32 _ _ (1092407 / 50000) (2184817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3080012032 :
    ThetaLowerSegment 3080012032 3080143104 (9624841636782 / 3125) (38501017177127 / 12500) := by
  exact
    packedTile65536 3080012032 3080143104 14 6044 55497 32 _ _ (1092409 / 50000) (2184821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3080143104 :
    ThetaLowerSegment 3080143104 3080274176 (38501017177127 / 12500)
      (308021108711167 / 100000) := by
  exact
    packedTile65536 3080143104 3080274176 14 5937 55499 32 _ _ (2184823 / 100000) (1092413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3080274176 :
    ThetaLowerSegment 3080274176 3080405248 (308021108711167 / 100000)
      (308034213303513 / 100000) := by
  exact
    packedTile65536 3080274176 3080405248 14 5998 55500 32 _ _ (2184827 / 100000) (218483 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3080405248 :
    ThetaLowerSegment 3080405248 3080536320 (308034213303513 / 100000)
      (61609474071159 / 20000) := by
  exact
    packedTile65536 3080405248 3080536320 14 6022 55501 32 _ _ (2184831 / 100000) (1092417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3080536320 :
    ThetaLowerSegment 3080536320 3080667392 (61609474071159 / 20000) (1925378419348 / 625) := by
  exact
    packedTile65536 3080536320 3080667392 14 6031 55502 32 _ _ (436967 / 20000) (1092419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3080667392 :
    ThetaLowerSegment 3080667392 3080798464 (1925378419348 / 625) (1925459695396 / 625) := by
  exact
    packedTile65536 3080667392 3080798464 14 5952 55503 32 _ _ (54621 / 2500) (2184843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3080798464 :
    ThetaLowerSegment 3080798464 3080929536 (1925459695396 / 625) (38510830902287 / 12500) := by
  exact
    packedTile65536 3080798464 3080929536 14 5994 55504 32 _ _ (546211 / 25000) (2184847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3080929536 :
    ThetaLowerSegment 3080929536 3081060608 (38510830902287 / 12500) (38512475273513 / 12500) := by
  exact
    packedTile65536 3080929536 3081060608 14 6021 55506 32 _ _ (136553 / 6250) (2184851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081060608 :
    ThetaLowerSegment 3081060608 3081191680 (38512475273513 / 12500) (15405641523029 / 5000) := by
  exact
    packedTile65536 3081060608 3081191680 14 5963 55507 32 _ _ (546213 / 25000) (436971 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081191680 :
    ThetaLowerSegment 3081191680 3081322752 (15405641523029 / 5000) (308125915569153 / 100000) := by
  exact
    packedTile65536 3081191680 3081322752 14 5989 55508 32 _ _ (2184857 / 100000) (109243 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081322752 :
    ThetaLowerSegment 3081322752 3081339136 (308125915569153 / 100000)
      (61625507347203 / 20000) := by
  exact
    packedTile65536 3081322752 3081339136 11 742 55509 32 _ _ (2184861 / 100000) (68277 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081339136 :
    ThetaLowerSegment 3081339136 3081341184 (61625507347203 / 20000)
      (308127750852491 / 100000) := by
  exact
    packedTile65536 3081339136 3081341184 8 98 55509 32 _ _ (1092431 / 50000) (436973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3049341184_3081341184 :
    ThetaLowerSegment 3049341184 3081341184 (304926605125579 / 100000)
      (308127750852491 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3049341184 cell3049472256)
                  (ThetaLowerSegment.join cell3049603328 cell3049734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3049865472 cell3049996544)
                  (ThetaLowerSegment.join cell3050127616 cell3050258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3050389760 cell3050520832)
                  (ThetaLowerSegment.join cell3050651904 cell3050782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3050914048 cell3051045120)
                  (ThetaLowerSegment.join cell3051176192 cell3051307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3051438336 cell3051569408)
                  (ThetaLowerSegment.join cell3051700480 cell3051831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3051962624 cell3052093696)
                  (ThetaLowerSegment.join cell3052224768 cell3052355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3052486912 cell3052617984)
                  (ThetaLowerSegment.join cell3052749056 cell3052880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3053011200 cell3053142272)
                  (ThetaLowerSegment.join cell3053273344 cell3053404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3053535488 cell3053666560)
                  (ThetaLowerSegment.join cell3053797632 cell3053928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3054059776 cell3054190848)
                  (ThetaLowerSegment.join cell3054321920 cell3054452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3054584064 cell3054715136)
                  (ThetaLowerSegment.join cell3054846208 cell3054977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3055108352 cell3055239424)
                  (ThetaLowerSegment.join cell3055370496 cell3055501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3055632640 cell3055763712)
                  (ThetaLowerSegment.join cell3055894784 cell3056025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3056156928 cell3056288000)
                  (ThetaLowerSegment.join cell3056419072 cell3056550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3056681216 cell3056812288)
                  (ThetaLowerSegment.join cell3056943360 cell3057074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3057205504 cell3057336576)
                  (ThetaLowerSegment.join cell3057467648 cell3057598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3057729792 cell3057860864)
                  (ThetaLowerSegment.join cell3057991936 cell3058123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3058254080 cell3058385152)
                  (ThetaLowerSegment.join cell3058516224 cell3058647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3058778368 cell3058909440)
                  (ThetaLowerSegment.join cell3059040512 cell3059171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3059302656 cell3059433728)
                  (ThetaLowerSegment.join cell3059564800 cell3059695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3059826944 cell3059958016)
                  (ThetaLowerSegment.join cell3060089088 cell3060220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3060351232 cell3060482304)
                  (ThetaLowerSegment.join cell3060613376 cell3060744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3060875520 cell3061006592)
                  (ThetaLowerSegment.join cell3061137664 cell3061268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3061399808 cell3061530880)
                  (ThetaLowerSegment.join cell3061661952 cell3061793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3061924096 cell3062055168)
                  (ThetaLowerSegment.join cell3062186240 cell3062317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3062448384 cell3062579456)
                  (ThetaLowerSegment.join cell3062710528 cell3062841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3062972672 cell3063103744)
                  (ThetaLowerSegment.join cell3063234816 cell3063365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3063496960 cell3063628032)
                  (ThetaLowerSegment.join cell3063759104 cell3063890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3064021248 cell3064152320)
                  (ThetaLowerSegment.join cell3064283392 cell3064414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3064545536 cell3064676608)
                  (ThetaLowerSegment.join cell3064807680 cell3064938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3065069824 cell3065200896)
                  (ThetaLowerSegment.join cell3065331968 cell3065463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3065594112 cell3065725184)
                  (ThetaLowerSegment.join cell3065856256 cell3065987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3066118400 cell3066249472)
                  (ThetaLowerSegment.join cell3066380544 cell3066511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3066642688 cell3066773760)
                  (ThetaLowerSegment.join cell3066904832 cell3067035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3067166976 cell3067298048)
                  (ThetaLowerSegment.join cell3067429120 cell3067560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3067691264 cell3067822336)
                  (ThetaLowerSegment.join cell3067953408 cell3068084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3068215552 cell3068346624)
                  (ThetaLowerSegment.join cell3068477696 cell3068608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3068739840 cell3068870912)
                  (ThetaLowerSegment.join cell3069001984 cell3069133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3069264128 cell3069395200)
                  (ThetaLowerSegment.join cell3069526272 cell3069657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3069788416 cell3069919488)
                  (ThetaLowerSegment.join cell3070050560 cell3070181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3070312704 cell3070443776)
                  (ThetaLowerSegment.join cell3070574848 cell3070705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3070836992 cell3070968064)
                  (ThetaLowerSegment.join cell3071099136 cell3071230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3071361280 cell3071492352)
                  (ThetaLowerSegment.join cell3071623424 cell3071754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3071885568 cell3072016640)
                  (ThetaLowerSegment.join cell3072147712 cell3072278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3072409856 cell3072540928)
                  (ThetaLowerSegment.join cell3072672000 cell3072803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3072934144 cell3073065216)
                  (ThetaLowerSegment.join cell3073196288 cell3073327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3073458432 cell3073589504)
                  (ThetaLowerSegment.join cell3073720576 cell3073851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3073982720 cell3074113792)
                  (ThetaLowerSegment.join cell3074244864 cell3074375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3074507008 cell3074638080)
                  (ThetaLowerSegment.join cell3074769152 cell3074900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3075031296 cell3075162368)
                  (ThetaLowerSegment.join cell3075293440 cell3075424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3075555584 cell3075686656)
                  (ThetaLowerSegment.join cell3075817728 cell3075948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3076079872 cell3076210944)
                  (ThetaLowerSegment.join cell3076342016 cell3076473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3076604160 cell3076735232)
                  (ThetaLowerSegment.join cell3076866304 cell3076997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3077128448 cell3077259520)
                  (ThetaLowerSegment.join cell3077390592 cell3077521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3077652736 cell3077783808)
                  (ThetaLowerSegment.join cell3077914880 cell3078045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3078177024 cell3078308096)
                  (ThetaLowerSegment.join cell3078439168 cell3078570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3078701312 cell3078832384)
                  (ThetaLowerSegment.join cell3078963456 cell3079094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3079225600 cell3079356672)
                  (ThetaLowerSegment.join cell3079487744 cell3079618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3079749888 cell3079880960)
                  (ThetaLowerSegment.join cell3080012032 cell3080143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3080274176 cell3080405248)
                  (ThetaLowerSegment.join cell3080536320 cell3080667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3080798464 cell3080929536)
                (ThetaLowerSegment.join cell3081060608 cell3081191680))
              (ThetaLowerSegment.join cell3081322752 cell3081339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
