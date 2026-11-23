/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3337341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3305341184 :
    ThetaLowerSegment 3305341184 3305472256 (330525015691687 / 100000)
      (165269106497573 / 50000) := by
  exact
    packedTile65536 3305341184 3305472256 14 6021 57492 32 _ _ (2191879 / 100000) (1095941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305472256 :
    ThetaLowerSegment 3305472256 3305603328 (165269106497573 / 50000) (66110265406227 / 20000) := by
  exact
    packedTile65536 3305472256 3305603328 14 5983 57493 32 _ _ (2191883 / 100000) (1095943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305603328 :
    ThetaLowerSegment 3305603328 3305734400 (66110265406227 / 20000) (13222572120087 / 4000) := by
  exact
    packedTile65536 3305603328 3305734400 14 5920 57494 32 _ _ (2191887 / 100000) (219189 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305734400 :
    ThetaLowerSegment 3305734400 3305865472 (13222572120087 / 4000) (82644406876891 / 25000) := by
  exact
    packedTile65536 3305734400 3305865472 14 6079 57495 32 _ _ (2191891 / 100000) (1095947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305865472 :
    ThetaLowerSegment 3305865472 3305996544 (82644406876891 / 25000) (41323839688063 / 12500) := by
  exact
    packedTile65536 3305865472 3305996544 14 5972 57496 32 _ _ (438379 / 20000) (1095949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3305996544 :
    ThetaLowerSegment 3305996544 3306127616 (41323839688063 / 12500) (165301875267979 / 50000) := by
  exact
    packedTile65536 3305996544 3306127616 14 5946 57497 32 _ _ (2191899 / 100000) (1095951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3306127616 :
    ThetaLowerSegment 3306127616 3306258688 (165301875267979 / 50000)
      (330616842772577 / 100000) := by
  exact
    packedTile65536 3306127616 3306258688 14 5973 57498 32 _ _ (2191903 / 100000) (1095953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3306258688 :
    ThetaLowerSegment 3306258688 3306389760 (330616842772577 / 100000)
      (82657494717807 / 25000) := by
  exact
    packedTile65536 3306258688 3306389760 14 5993 57500 32 _ _ (2191907 / 100000) (219191 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3306389760 :
    ThetaLowerSegment 3306389760 3306520832 (82657494717807 / 25000) (16532168791563 / 5000) := by
  exact
    packedTile65536 3306389760 3306520832 14 6112 57501 32 _ _ (2191911 / 100000) (1095957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3306520832 :
    ThetaLowerSegment 3306520832 3306651904 (16532168791563 / 5000) (33065629497827 / 10000) := by
  exact
    packedTile65536 3306520832 3306651904 14 5894 57502 32 _ _ (438383 / 20000) (1095959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3306651904 :
    ThetaLowerSegment 3306651904 3306782976 (33065629497827 / 10000)
      (330669470603379 / 100000) := by
  exact
    packedTile65536 3306651904 3306782976 14 6011 57503 32 _ _ (2191919 / 100000) (1095961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3306782976 :
    ThetaLowerSegment 3306782976 3306914048 (330669470603379 / 100000)
      (165341259560499 / 50000) := by
  exact
    packedTile65536 3306782976 3306914048 14 5953 57504 32 _ _ (2191923 / 100000) (1095963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3306914048 :
    ThetaLowerSegment 3306914048 3307045120 (165341259560499 / 50000) (41336967055101 / 12500) := by
  exact
    packedTile65536 3306914048 3307045120 14 6030 57505 32 _ _ (2191927 / 100000) (219193 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3307045120 :
    ThetaLowerSegment 3307045120 3307176192 (41336967055101 / 12500)
      (330709039270047 / 100000) := by
  exact
    packedTile65536 3307045120 3307176192 14 6069 57506 32 _ _ (2191931 / 100000) (1095967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3307176192 :
    ThetaLowerSegment 3307176192 3307307264 (330709039270047 / 100000)
      (165361079000511 / 50000) := by
  exact
    packedTile65536 3307176192 3307307264 14 5985 57508 32 _ _ (438387 / 20000) (1095969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3307307264 :
    ThetaLowerSegment 3307307264 3307438336 (165361079000511 / 50000)
      (330735289907571 / 100000) := by
  exact
    packedTile65536 3307307264 3307438336 14 5991 57509 32 _ _ (2191939 / 100000) (1095971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3307438336 :
    ThetaLowerSegment 3307438336 3307569408 (330735289907571 / 100000)
      (330748334154413 / 100000) := by
  exact
    packedTile65536 3307438336 3307569408 14 5951 57510 32 _ _ (1095971 / 50000) (438389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3307569408 :
    ThetaLowerSegment 3307569408 3307700480 (330748334154413 / 100000)
      (330761470486791 / 100000) := by
  exact
    packedTile65536 3307569408 3307700480 14 5993 57511 32 _ _ (1095973 / 50000) (2191949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3307700480 :
    ThetaLowerSegment 3307700480 3307831552 (330761470486791 / 100000)
      (330774501629541 / 100000) := by
  exact
    packedTile65536 3307700480 3307831552 14 5945 57512 32 _ _ (43839 / 2000) (2191953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3307831552 :
    ThetaLowerSegment 3307831552 3307962624 (330774501629541 / 100000)
      (330787596362737 / 100000) := by
  exact
    packedTile65536 3307831552 3307962624 14 5974 57513 32 _ _ (1095977 / 50000) (2191957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3307962624 :
    ThetaLowerSegment 3307962624 3308093696 (330787596362737 / 100000)
      (330800776606191 / 100000) := by
  exact
    packedTile65536 3307962624 3308093696 14 6013 57514 32 _ _ (1095979 / 50000) (2191961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3308093696 :
    ThetaLowerSegment 3308093696 3308224768 (330800776606191 / 100000)
      (66162749289069 / 20000) := by
  exact
    packedTile65536 3308093696 3308224768 14 5917 57516 32 _ _ (1095981 / 50000) (438393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3308224768 :
    ThetaLowerSegment 3308224768 3308355840 (66162749289069 / 20000)
      (330826970576223 / 100000) := by
  exact
    packedTile65536 3308224768 3308355840 14 6033 57517 32 _ _ (1095983 / 50000) (2191969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3308355840 :
    ThetaLowerSegment 3308355840 3308486912 (330826970576223 / 100000)
      (330839990878023 / 100000) := by
  exact
    packedTile65536 3308355840 3308486912 14 5940 57518 32 _ _ (219197 / 10000) (2191973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3308486912 :
    ThetaLowerSegment 3308486912 3308617984 (330839990878023 / 100000)
      (330853101074517 / 100000) := by
  exact
    packedTile65536 3308486912 3308617984 14 5981 57519 32 _ _ (1095987 / 50000) (2191977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3308617984 :
    ThetaLowerSegment 3308617984 3308749056 (330853101074517 / 100000)
      (330866198143067 / 100000) := by
  exact
    packedTile65536 3308617984 3308749056 14 5975 57520 32 _ _ (1095989 / 50000) (2191981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3308749056 :
    ThetaLowerSegment 3308749056 3308880128 (330866198143067 / 100000)
      (330879214132183 / 100000) := by
  exact
    packedTile65536 3308749056 3308880128 14 5938 57521 32 _ _ (1095991 / 50000) (438397 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3308880128 :
    ThetaLowerSegment 3308880128 3309011200 (330879214132183 / 100000)
      (66178452166571 / 20000) := by
  exact
    packedTile65536 3308880128 3309011200 14 5952 57522 32 _ _ (1095993 / 50000) (2191989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3309011200 :
    ThetaLowerSegment 3309011200 3309142272 (66178452166571 / 20000) (66181080362581 / 20000) := by
  exact
    packedTile65536 3309011200 3309142272 14 5995 57524 32 _ _ (219199 / 10000) (2191993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3309142272 :
    ThetaLowerSegment 3309142272 3309273344 (66181080362581 / 20000)
      (330918450753187 / 100000) := by
  exact
    packedTile65536 3309142272 3309273344 14 5953 57525 32 _ _ (1095997 / 50000) (2191997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3309273344 :
    ThetaLowerSegment 3309273344 3309404416 (330918450753187 / 100000)
      (330931387925383 / 100000) := by
  exact
    packedTile65536 3309273344 3309404416 14 5902 57526 32 _ _ (1095999 / 50000) (2192001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3309404416 :
    ThetaLowerSegment 3309404416 3309535488 (330931387925383 / 100000)
      (330944583777423 / 100000) := by
  exact
    packedTile65536 3309404416 3309535488 14 6020 57527 32 _ _ (1096001 / 50000) (438401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3309535488 :
    ThetaLowerSegment 3309535488 3309666560 (330944583777423 / 100000)
      (330957599909051 / 100000) := by
  exact
    packedTile65536 3309535488 3309666560 14 5938 57528 32 _ _ (1096003 / 50000) (2192009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3309666560 :
    ThetaLowerSegment 3309666560 3309797632 (330957599909051 / 100000)
      (330970657712621 / 100000) := by
  exact
    packedTile65536 3309666560 3309797632 14 5957 57529 32 _ _ (219201 / 10000) (2192013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3309797632 :
    ThetaLowerSegment 3309797632 3309928704 (330970657712621 / 100000)
      (330983645395571 / 100000) := by
  exact
    packedTile65536 3309797632 3309928704 14 5925 57530 32 _ _ (1096007 / 50000) (2192017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3309928704 :
    ThetaLowerSegment 3309928704 3310059776 (330983645395571 / 100000)
      (330996806271643 / 100000) := by
  exact
    packedTile65536 3309928704 3310059776 14 6004 57531 32 _ _ (1096009 / 50000) (2192021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310059776 :
    ThetaLowerSegment 3310059776 3310190848 (330996806271643 / 100000)
      (331009975939819 / 100000) := by
  exact
    packedTile65536 3310059776 3310190848 14 6008 57533 32 _ _ (1096011 / 50000) (87681 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310190848 :
    ThetaLowerSegment 3310190848 3310321920 (331009975939819 / 100000)
      (66204615097439 / 20000) := by
  exact
    packedTile65536 3310190848 3310321920 14 5976 57534 32 _ _ (1096013 / 50000) (2192029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310321920 :
    ThetaLowerSegment 3310321920 3310452992 (66204615097439 / 20000) (66207229750823 / 20000) := by
  exact
    packedTile65536 3310321920 3310452992 14 5964 57535 32 _ _ (219203 / 10000) (2192033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310452992 :
    ThetaLowerSegment 3310452992 3310584064 (66207229750823 / 20000)
      (331049314110319 / 100000) := by
  exact
    packedTile65536 3310452992 3310584064 14 6006 57536 32 _ _ (1096017 / 50000) (2192037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310584064 :
    ThetaLowerSegment 3310584064 3310715136 (331049314110319 / 100000)
      (331062378656799 / 100000) := by
  exact
    packedTile65536 3310584064 3310715136 14 5960 57537 32 _ _ (1096019 / 50000) (2192041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310715136 :
    ThetaLowerSegment 3310715136 3310846208 (331062378656799 / 100000)
      (331075414730573 / 100000) := by
  exact
    packedTile65536 3310715136 3310846208 14 5947 57538 32 _ _ (1096021 / 50000) (438409 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310846208 :
    ThetaLowerSegment 3310846208 3310977280 (331075414730573 / 100000)
      (331088623993743 / 100000) := by
  exact
    packedTile65536 3310846208 3310977280 14 6026 57539 32 _ _ (438409 / 20000) (137003 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310977280 :
    ThetaLowerSegment 3310977280 3311108352 (331088623993743 / 100000)
      (331101631612509 / 100000) := by
  exact
    packedTile65536 3310977280 3311108352 14 5934 57541 32 _ _ (2192049 / 100000) (548013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3311108352 :
    ThetaLowerSegment 3311108352 3311239424 (331101631612509 / 100000)
      (165557252769889 / 50000) := by
  exact
    packedTile65536 3311108352 3311239424 14 5873 57542 32 _ _ (2192053 / 100000) (274007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3311239424 :
    ThetaLowerSegment 3311239424 3311370496 (165557252769889 / 50000)
      (331127589928011 / 100000) := by
  exact
    packedTile65536 3311239424 3311370496 14 5969 57543 32 _ _ (2192057 / 100000) (109603 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3311370496 :
    ThetaLowerSegment 3311370496 3311501568 (331127589928011 / 100000)
      (165570334977999 / 50000) := by
  exact
    packedTile65536 3311370496 3311501568 14 5967 57544 32 _ _ (2192061 / 100000) (68502 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3311501568 :
    ThetaLowerSegment 3311501568 3311632640 (165570334977999 / 50000)
      (331153653556993 / 100000) := by
  exact
    packedTile65536 3311501568 3311632640 14 5923 57545 32 _ _ (438413 / 20000) (548017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3311632640 :
    ThetaLowerSegment 3311632640 3311763712 (331153653556993 / 100000)
      (331166902422029 / 100000) := by
  exact
    packedTile65536 3311632640 3311763712 14 6044 57546 32 _ _ (2192069 / 100000) (274009 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3311763712 :
    ThetaLowerSegment 3311763712 3311894784 (331166902422029 / 100000)
      (41397512063677 / 12500) := by
  exact
    packedTile65536 3311763712 3311894784 14 6019 57547 32 _ _ (2192073 / 100000) (548019 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3311894784 :
    ThetaLowerSegment 3311894784 3312025856 (41397512063677 / 12500) (827983078587 / 250) := by
  exact
    packedTile65536 3311894784 3312025856 14 5992 57549 32 _ _ (2192077 / 100000) (27401 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3312025856 :
    ThetaLowerSegment 3312025856 3312156928 (827983078587 / 250) (13248257548913 / 4000) := by
  exact
    packedTile65536 3312025856 3312156928 14 6025 57550 32 _ _ (2192081 / 100000) (548021 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3312156928 :
    ThetaLowerSegment 3312156928 3312288000 (13248257548913 / 4000) (66243934029577 / 20000) := by
  exact
    packedTile65536 3312156928 3312288000 14 6036 57551 32 _ _ (438417 / 20000) (274011 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3312288000 :
    ThetaLowerSegment 3312288000 3312419072 (66243934029577 / 20000) (33123274595877 / 10000) := by
  exact
    packedTile65536 3312288000 3312419072 14 5965 57552 32 _ _ (2192089 / 100000) (548023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3312419072 :
    ThetaLowerSegment 3312419072 3312550144 (33123274595877 / 10000) (66249159974517 / 20000) := by
  exact
    packedTile65536 3312419072 3312550144 14 5955 57553 32 _ _ (2192093 / 100000) (68503 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3312550144 :
    ThetaLowerSegment 3312550144 3312681216 (66249159974517 / 20000)
      (331258965607167 / 100000) := by
  exact
    packedTile65536 3312550144 3312681216 14 6006 57554 32 _ _ (2192097 / 100000) (21921 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3312681216 :
    ThetaLowerSegment 3312681216 3312812288 (331258965607167 / 100000)
      (331272061218541 / 100000) := by
  exact
    packedTile65536 3312681216 3312812288 14 5974 57555 32 _ _ (2192101 / 100000) (274013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3312812288 :
    ThetaLowerSegment 3312812288 3312943360 (331272061218541 / 100000)
      (165642599251903 / 50000) := by
  exact
    packedTile65536 3312812288 3312943360 14 5993 57557 32 _ _ (438421 / 20000) (548027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3312943360 :
    ThetaLowerSegment 3312943360 3313074432 (165642599251903 / 50000) (10353070870552 / 3125) := by
  exact
    packedTile65536 3312943360 3313074432 14 5962 57558 32 _ _ (2192109 / 100000) (137007 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3313074432 :
    ThetaLowerSegment 3313074432 3313205504 (10353070870552 / 3125) (41413929759071 / 12500) := by
  exact
    packedTile65536 3313074432 3313205504 14 6008 57559 32 _ _ (2192113 / 100000) (548029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3313205504 :
    ThetaLowerSegment 3313205504 3313336576 (41413929759071 / 12500) (20707774866767 / 6250) := by
  exact
    packedTile65536 3313205504 3313336576 14 5912 57560 32 _ _ (2192117 / 100000) (54803 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3313336576 :
    ThetaLowerSegment 3313336576 3313467648 (20707774866767 / 6250) (20708585951537 / 6250) := by
  exact
    packedTile65536 3313336576 3313467648 14 5920 57561 32 _ _ (2192121 / 100000) (548031 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3313467648 :
    ThetaLowerSegment 3313467648 3313598720 (20708585951537 / 6250) (331350582777717 / 100000) := by
  exact
    packedTile65536 3313467648 3313598720 14 6025 57562 32 _ _ (17537 / 800) (68504 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3313598720 :
    ThetaLowerSegment 3313598720 3313729792 (331350582777717 / 100000)
      (165681838182117 / 50000) := by
  exact
    packedTile65536 3313598720 3313729792 14 5973 57563 32 _ _ (2192129 / 100000) (548033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3313729792 :
    ThetaLowerSegment 3313729792 3313860864 (165681838182117 / 50000) (82844199618093 / 25000) := by
  exact
    packedTile65536 3313729792 3313860864 14 5986 57565 32 _ _ (2192133 / 100000) (274017 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3313860864 :
    ThetaLowerSegment 3313860864 3313991936 (82844199618093 / 25000) (16569489672729 / 5000) := by
  exact
    packedTile65536 3313860864 3313991936 14 5928 57566 32 _ _ (274017 / 12500) (2192139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3313991936 :
    ThetaLowerSegment 3313991936 3314123008 (16569489672729 / 5000) (1657014106713 / 500) := by
  exact
    packedTile65536 3313991936 3314123008 14 5943 57567 32 _ _ (109607 / 5000) (2192143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3314123008 :
    ThetaLowerSegment 3314123008 3314254080 (1657014106713 / 500) (41426985541087 / 12500) := by
  exact
    packedTile65536 3314123008 3314254080 14 5959 57568 32 _ _ (137009 / 6250) (2192147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3314254080 :
    ThetaLowerSegment 3314254080 3314385152 (41426985541087 / 12500) (82857225873917 / 25000) := by
  exact
    packedTile65536 3314254080 3314385152 14 5939 57569 32 _ _ (548037 / 25000) (2192151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3314385152 :
    ThetaLowerSegment 3314385152 3314516224 (82857225873917 / 25000) (82860550820463 / 25000) := by
  exact
    packedTile65536 3314385152 3314516224 14 6067 57570 32 _ _ (274019 / 12500) (438431 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3314516224 :
    ThetaLowerSegment 3314516224 3314647296 (82860550820463 / 25000) (82863833574073 / 25000) := by
  exact
    packedTile65536 3314516224 3314647296 14 5990 57571 32 _ _ (548039 / 25000) (2192159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3314647296 :
    ThetaLowerSegment 3314647296 3314778368 (82863833574073 / 25000) (82867100988553 / 25000) := by
  exact
    packedTile65536 3314647296 3314778368 14 5962 57572 32 _ _ (13701 / 625) (2192163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3314778368 :
    ThetaLowerSegment 3314778368 3314909440 (82867100988553 / 25000) (82870355256011 / 25000) := by
  exact
    packedTile65536 3314778368 3314909440 14 5938 57574 32 _ _ (548041 / 25000) (2192167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3314909440 :
    ThetaLowerSegment 3314909440 3315040512 (82870355256011 / 25000) (82873634739339 / 25000) := by
  exact
    packedTile65536 3314909440 3315040512 14 5984 57575 32 _ _ (274021 / 12500) (2192171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3315040512 :
    ThetaLowerSegment 3315040512 3315171584 (82873634739339 / 25000) (20719231160367 / 6250) := by
  exact
    packedTile65536 3315040512 3315171584 14 6003 57576 32 _ _ (548043 / 25000) (87687 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3315171584 :
    ThetaLowerSegment 3315171584 3315302656 (20719231160367 / 6250) (20720042265487 / 6250) := by
  exact
    packedTile65536 3315171584 3315302656 14 5920 57577 32 _ _ (137011 / 6250) (2192179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3315302656 :
    ThetaLowerSegment 3315302656 3315433728 (20720042265487 / 6250) (10360430796381 / 3125) := by
  exact
    packedTile65536 3315302656 3315433728 14 5980 57578 32 _ _ (109609 / 5000) (2192183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3315433728 :
    ThetaLowerSegment 3315433728 3315564800 (10360430796381 / 3125) (20721679551417 / 6250) := by
  exact
    packedTile65536 3315433728 3315564800 14 5970 57579 32 _ _ (274023 / 12500) (2192187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3315564800 :
    ThetaLowerSegment 3315564800 3315695872 (20721679551417 / 6250) (82890020188843 / 25000) := by
  exact
    packedTile65536 3315564800 3315695872 14 6025 57580 32 _ _ (548047 / 25000) (2192191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3315695872 :
    ThetaLowerSegment 3315695872 3315826944 (82890020188843 / 25000) (16578663777951 / 5000) := by
  exact
    packedTile65536 3315695872 3315826944 14 6019 57582 32 _ _ (68506 / 3125) (438439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3315826944 :
    ThetaLowerSegment 3315826944 3315958016 (16578663777951 / 5000) (82896611568147 / 25000) := by
  exact
    packedTile65536 3315826944 3315958016 14 6008 57583 32 _ _ (548049 / 25000) (2192199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3315958016 :
    ThetaLowerSegment 3315958016 3316089088 (82896611568147 / 25000) (82899914117447 / 25000) := by
  exact
    packedTile65536 3315958016 3316089088 14 6026 57584 32 _ _ (10961 / 500) (2192203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3316089088 :
    ThetaLowerSegment 3316089088 3316220160 (82899914117447 / 25000) (82903222153283 / 25000) := by
  exact
    packedTile65536 3316089088 3316220160 14 6036 57585 32 _ _ (548051 / 25000) (2192207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3316220160 :
    ThetaLowerSegment 3316220160 3316351232 (82903222153283 / 25000) (82906486899047 / 25000) := by
  exact
    packedTile65536 3316220160 3316351232 14 5957 57586 32 _ _ (137013 / 6250) (2192211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3316351232 :
    ThetaLowerSegment 3316351232 3316482304 (82906486899047 / 25000) (10363722244664 / 3125) := by
  exact
    packedTile65536 3316351232 3316482304 14 6005 57587 32 _ _ (548053 / 25000) (438443 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3316482304 :
    ThetaLowerSegment 3316482304 3316613376 (10363722244664 / 3125) (41456531770521 / 12500) := by
  exact
    packedTile65536 3316482304 3316613376 14 5995 57588 32 _ _ (274027 / 12500) (2192219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3316613376 :
    ThetaLowerSegment 3316613376 3316744448 (41456531770521 / 12500) (10364541380619 / 3125) := by
  exact
    packedTile65536 3316613376 3316744448 14 5962 57590 32 _ _ (109611 / 5000) (2192223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3316744448 :
    ThetaLowerSegment 3316744448 3316875520 (10364541380619 / 3125) (165839183953329 / 50000) := by
  exact
    packedTile65536 3316744448 3316875520 14 5950 57591 32 _ _ (2192223 / 100000) (1096113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3316875520 :
    ThetaLowerSegment 3316875520 3317006592 (165839183953329 / 50000)
      (165845747480967 / 50000) := by
  exact
    packedTile65536 3316875520 3317006592 14 5988 57592 32 _ _ (2192227 / 100000) (219223 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3317006592 :
    ThetaLowerSegment 3317006592 3317137664 (165845747480967 / 50000)
      (331704668078013 / 100000) := by
  exact
    packedTile65536 3317006592 3317137664 14 6009 57593 32 _ _ (2192231 / 100000) (1096117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3317137664 :
    ThetaLowerSegment 3317137664 3317268736 (331704668078013 / 100000)
      (41464741113441 / 12500) := by
  exact
    packedTile65536 3317137664 3317268736 14 6049 57594 32 _ _ (438447 / 20000) (1096119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3317268736 :
    ThetaLowerSegment 3317268736 3317399808 (41464741113441 / 12500) (41466358985823 / 12500) := by
  exact
    packedTile65536 3317268736 3317399808 14 5904 57595 32 _ _ (2192239 / 100000) (1096121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3317399808 :
    ThetaLowerSegment 3317399808 3317530880 (41466358985823 / 12500) (13269759873817 / 4000) := by
  exact
    packedTile65536 3317399808 3317530880 14 5987 57596 32 _ _ (2192243 / 100000) (1096123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3317530880 :
    ThetaLowerSegment 3317530880 3317661952 (13269759873817 / 4000) (331756970563171 / 100000) := by
  exact
    packedTile65536 3317530880 3317661952 14 5918 57598 32 _ _ (2192247 / 100000) (8769 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3317661952 :
    ThetaLowerSegment 3317661952 3317793024 (331756970563171 / 100000)
      (331770031994629 / 100000) := by
  exact
    packedTile65536 3317661952 3317793024 14 5958 57599 32 _ _ (2192251 / 100000) (1096127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3317793024 :
    ThetaLowerSegment 3317793024 3317924096 (331770031994629 / 100000)
      (165891574128147 / 50000) := by
  exact
    packedTile65536 3317793024 3317924096 14 5983 57600 32 _ _ (438451 / 20000) (1096129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3317924096 :
    ThetaLowerSegment 3317924096 3318055168 (165891574128147 / 50000)
      (331796251388337 / 100000) := by
  exact
    packedTile65536 3317924096 3318055168 14 5977 57601 32 _ _ (2192259 / 100000) (1096131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318055168 :
    ThetaLowerSegment 3318055168 3318186240 (331796251388337 / 100000)
      (331809431273493 / 100000) := by
  exact
    packedTile65536 3318055168 3318186240 14 6012 57602 32 _ _ (2192263 / 100000) (1096133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318186240 :
    ThetaLowerSegment 3318186240 3318317312 (331809431273493 / 100000)
      (165911203650933 / 50000) := by
  exact
    packedTile65536 3318186240 3318317312 14 5919 57603 32 _ _ (2192267 / 100000) (219227 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318317312 :
    ThetaLowerSegment 3318317312 3318448384 (165911203650933 / 50000) (66367133669829 / 20000) := by
  exact
    packedTile65536 3318317312 3318448384 14 6049 57604 32 _ _ (2192271 / 100000) (1096137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318448384 :
    ThetaLowerSegment 3318448384 3318579456 (66367133669829 / 20000) (33184880226867 / 10000) := by
  exact
    packedTile65536 3318448384 3318579456 14 5991 57605 32 _ _ (87691 / 4000) (1096139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318579456 :
    ThetaLowerSegment 3318579456 3318710528 (33184880226867 / 10000) (165931017432357 / 50000) := by
  exact
    packedTile65536 3318579456 3318710528 14 6036 57607 32 _ _ (2192279 / 100000) (1096141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318710528 :
    ThetaLowerSegment 3318710528 3318841600 (165931017432357 / 50000) (82968835505631 / 25000) := by
  exact
    packedTile65536 3318710528 3318841600 14 6070 57608 32 _ _ (2192283 / 100000) (1096143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318841600 :
    ThetaLowerSegment 3318841600 3318972672 (82968835505631 / 25000) (53102123541 / 16) := by
  exact
    packedTile65536 3318841600 3318972672 14 5898 57609 32 _ _ (2192287 / 100000) (219229 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318972672 :
    ThetaLowerSegment 3318972672 3319103744 (53102123541 / 16) (165950730476953 / 50000) := by
  exact
    packedTile65536 3318972672 3319103744 14 6016 57610 32 _ _ (2192291 / 100000) (1096147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3319103744 :
    ThetaLowerSegment 3319103744 3319234816 (165950730476953 / 50000)
      (331914608147021 / 100000) := by
  exact
    packedTile65536 3319103744 3319234816 14 5997 57611 32 _ _ (438459 / 20000) (1096149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3319234816 :
    ThetaLowerSegment 3319234816 3319365888 (331914608147021 / 100000)
      (165963993873909 / 50000) := by
  exact
    packedTile65536 3319234816 3319365888 14 6103 57612 32 _ _ (2192299 / 100000) (1096151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3319365888 :
    ThetaLowerSegment 3319365888 3319496960 (165963993873909 / 50000) (82985273880369 / 25000) := by
  exact
    packedTile65536 3319365888 3319496960 14 5979 57613 32 _ _ (1096151 / 50000) (438461 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3319496960 :
    ThetaLowerSegment 3319496960 3319628032 (82985273880369 / 25000) (82988540416309 / 25000) := by
  exact
    packedTile65536 3319496960 3319628032 14 5960 57615 32 _ _ (1096153 / 50000) (2192309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3319628032 :
    ThetaLowerSegment 3319628032 3319759104 (82988540416309 / 25000) (165983667628013 / 50000) := by
  exact
    packedTile65536 3319628032 3319759104 14 6009 57616 32 _ _ (219231 / 10000) (2192313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3319759104 :
    ThetaLowerSegment 3319759104 3319890176 (165983667628013 / 50000) (41497551003051 / 12500) := by
  exact
    packedTile65536 3319759104 3319890176 14 5963 57617 32 _ _ (1096157 / 50000) (2192317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3319890176 :
    ThetaLowerSegment 3319890176 3320021248 (41497551003051 / 12500) (82998446387211 / 25000) := by
  exact
    packedTile65536 3319890176 3320021248 14 6102 57618 32 _ _ (1096159 / 50000) (2192321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3320021248 :
    ThetaLowerSegment 3320021248 3320152320 (82998446387211 / 25000) (41500860310059 / 12500) := by
  exact
    packedTile65536 3320021248 3320152320 14 5974 57619 32 _ _ (1096161 / 50000) (87693 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3320152320 :
    ThetaLowerSegment 3320152320 3320283392 (41500860310059 / 12500) (166009993006487 / 50000) := by
  exact
    packedTile65536 3320152320 3320283392 14 5977 57620 32 _ _ (1096163 / 50000) (2192329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3320283392 :
    ThetaLowerSegment 3320283392 3320414464 (166009993006487 / 50000) (83008260334531 / 25000) := by
  exact
    packedTile65536 3320283392 3320414464 14 5955 57621 32 _ _ (219233 / 10000) (2192333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3320414464 :
    ThetaLowerSegment 3320414464 3320545536 (83008260334531 / 25000) (166023011073869 / 50000) := by
  exact
    packedTile65536 3320414464 3320545536 14 5921 57623 32 _ _ (1096167 / 50000) (2192337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3320545536 :
    ThetaLowerSegment 3320545536 3320676608 (166023011073869 / 50000) (10376845624432 / 3125) := by
  exact
    packedTile65536 3320545536 3320676608 14 5947 57624 32 _ _ (1096169 / 50000) (2192341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3320676608 :
    ThetaLowerSegment 3320676608 3320807680 (10376845624432 / 3125) (166036059881559 / 50000) := by
  exact
    packedTile65536 3320676608 3320807680 14 5957 57625 32 _ _ (1096171 / 50000) (438469 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3320807680 :
    ThetaLowerSegment 3320807680 3320938752 (166036059881559 / 50000) (83021326681077 / 25000) := by
  exact
    packedTile65536 3320807680 3320938752 14 6015 57626 32 _ _ (1096173 / 50000) (2192349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3320938752 :
    ThetaLowerSegment 3320938752 3321069824 (83021326681077 / 25000) (83024599859627 / 25000) := by
  exact
    packedTile65536 3320938752 3321069824 14 5972 57627 32 _ _ (43847 / 2000) (2192353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3321069824 :
    ThetaLowerSegment 3321069824 3321200896 (83024599859627 / 25000) (166055788839201 / 50000) := by
  exact
    packedTile65536 3321069824 3321200896 14 6011 57628 32 _ _ (1096177 / 50000) (2192357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3321200896 :
    ThetaLowerSegment 3321200896 3321331968 (166055788839201 / 50000) (83031164869647 / 25000) := by
  exact
    packedTile65536 3321200896 3321331968 14 5967 57629 32 _ _ (1096179 / 50000) (2192361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3321331968 :
    ThetaLowerSegment 3321331968 3321463040 (83031164869647 / 25000) (33213766237761 / 10000) := by
  exact
    packedTile65536 3321331968 3321463040 14 5931 57630 32 _ _ (1096181 / 50000) (438473 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3321463040 :
    ThetaLowerSegment 3321463040 3321594112 (33213766237761 / 10000) (83037710172409 / 25000) := by
  exact
    packedTile65536 3321463040 3321594112 14 6011 57632 32 _ _ (1096183 / 50000) (2192369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3321594112 :
    ThetaLowerSegment 3321594112 3321725184 (83037710172409 / 25000) (166081952511233 / 50000) := by
  exact
    packedTile65536 3321594112 3321725184 14 5959 57633 32 _ _ (219237 / 10000) (2192373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3321725184 :
    ThetaLowerSegment 3321725184 3321856256 (166081952511233 / 50000)
      (166088509901867 / 50000) := by
  exact
    packedTile65536 3321725184 3321856256 14 5982 57634 32 _ _ (1096187 / 50000) (2192377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3321856256 :
    ThetaLowerSegment 3321856256 3321987328 (166088509901867 / 50000) (41523772306311 / 12500) := by
  exact
    packedTile65536 3321856256 3321987328 14 6002 57635 32 _ _ (2192377 / 100000) (109619 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3321987328 :
    ThetaLowerSegment 3321987328 3322118400 (41523772306311 / 12500) (20762705007459 / 6250) := by
  exact
    packedTile65536 3321987328 3322118400 14 5976 57636 32 _ _ (2192381 / 100000) (68512 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3322118400 :
    ThetaLowerSegment 3322118400 3322249472 (20762705007459 / 6250) (83054084491101 / 25000) := by
  exact
    packedTile65536 3322118400 3322249472 14 5956 57637 32 _ _ (438477 / 20000) (548097 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3322249472 :
    ThetaLowerSegment 3322249472 3322380544 (83054084491101 / 25000)
      (332229455027791 / 100000) := by
  exact
    packedTile65536 3322249472 3322380544 14 5983 57638 32 _ _ (2192389 / 100000) (274049 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3322380544 :
    ThetaLowerSegment 3322380544 3322511616 (332229455027791 / 100000)
      (83060690165227 / 25000) := by
  exact
    packedTile65536 3322380544 3322511616 14 6069 57640 32 _ _ (2192393 / 100000) (548099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3322511616 :
    ThetaLowerSegment 3322511616 3322642688 (83060690165227 / 25000) (41532005823341 / 12500) := by
  exact
    packedTile65536 3322511616 3322642688 14 6060 57641 32 _ _ (2192397 / 100000) (5481 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3322642688 :
    ThetaLowerSegment 3322642688 3322773760 (41532005823341 / 12500)
      (332269247033149 / 100000) := by
  exact
    packedTile65536 3322642688 3322773760 14 6021 57642 32 _ _ (2192401 / 100000) (548101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3322773760 :
    ThetaLowerSegment 3322773760 3322904832 (332269247033149 / 100000)
      (332282344460619 / 100000) := by
  exact
    packedTile65536 3322773760 3322904832 14 5974 57643 32 _ _ (438481 / 20000) (274051 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3322904832 :
    ThetaLowerSegment 3322904832 3323035904 (332282344460619 / 100000)
      (166147665049563 / 50000) := by
  exact
    packedTile65536 3322904832 3323035904 14 5923 57644 32 _ _ (2192409 / 100000) (548103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323035904 :
    ThetaLowerSegment 3323035904 3323166976 (166147665049563 / 50000) (83077128817727 / 25000) := by
  exact
    packedTile65536 3323035904 3323166976 14 6014 57645 32 _ _ (2192413 / 100000) (68513 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323166976 :
    ThetaLowerSegment 3323166976 3323298048 (83077128817727 / 25000) (166160837078871 / 50000) := by
  exact
    packedTile65536 3323166976 3323298048 14 6002 57646 32 _ _ (2192417 / 100000) (109621 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323298048 :
    ThetaLowerSegment 3323298048 3323429120 (166160837078871 / 50000)
      (332334822106479 / 100000) := by
  exact
    packedTile65536 3323298048 3323429120 14 5997 57648 32 _ _ (2192421 / 100000) (274053 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323429120 :
    ThetaLowerSegment 3323429120 3323560192 (332334822106479 / 100000)
      (332347836341279 / 100000) := by
  exact
    packedTile65536 3323429120 3323560192 14 5936 57649 32 _ _ (87697 / 4000) (548107 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323560192 :
    ThetaLowerSegment 3323560192 3323691264 (332347836341279 / 100000)
      (332360938296983 / 100000) := by
  exact
    packedTile65536 3323560192 3323691264 14 5976 57650 32 _ _ (2192429 / 100000) (137027 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323691264 :
    ThetaLowerSegment 3323691264 3323822336 (332360938296983 / 100000)
      (83093512809689 / 25000) := by
  exact
    packedTile65536 3323691264 3323822336 14 5981 57651 32 _ _ (2192433 / 100000) (548109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323822336 :
    ThetaLowerSegment 3323822336 3323953408 (83093512809689 / 25000) (166193613892563 / 50000) := by
  exact
    packedTile65536 3323822336 3323953408 14 6010 57652 32 _ _ (2192437 / 100000) (54811 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323953408 :
    ThetaLowerSegment 3323953408 3324084480 (166193613892563 / 50000)
      (332400367084039 / 100000) := by
  exact
    packedTile65536 3323953408 3324084480 14 5993 57653 32 _ _ (2192441 / 100000) (548111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3324084480 :
    ThetaLowerSegment 3324084480 3324215552 (332400367084039 / 100000)
      (83103363447061 / 25000) := by
  exact
    packedTile65536 3324084480 3324215552 14 5969 57654 32 _ _ (438489 / 20000) (68514 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3324215552 :
    ThetaLowerSegment 3324215552 3324346624 (83103363447061 / 25000) (83106628002133 / 25000) := by
  exact
    packedTile65536 3324215552 3324346624 14 5956 57656 32 _ _ (68514 / 3125) (2192451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3324346624 :
    ThetaLowerSegment 3324346624 3324477696 (83106628002133 / 25000) (41554959710349 / 12500) := by
  exact
    packedTile65536 3324346624 3324477696 14 6005 57657 32 _ _ (548113 / 25000) (438491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3324477696 :
    ThetaLowerSegment 3324477696 3324608768 (41554959710349 / 12500) (4155658569053 / 1250) := by
  exact
    packedTile65536 3324477696 3324608768 14 5933 57658 32 _ _ (274057 / 12500) (2192459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3324608768 :
    ThetaLowerSegment 3324608768 3324739840 (4155658569053 / 1250) (16623286861931 / 5000) := by
  exact
    packedTile65536 3324608768 3324739840 14 5953 57659 32 _ _ (109623 / 5000) (2192463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3324739840 :
    ThetaLowerSegment 3324739840 3324870912 (16623286861931 / 5000) (83119702177247 / 25000) := by
  exact
    packedTile65536 3324739840 3324870912 14 5962 57660 32 _ _ (137029 / 6250) (2192467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3324870912 :
    ThetaLowerSegment 3324870912 3325001984 (83119702177247 / 25000) (2078074621249 / 625) := by
  exact
    packedTile65536 3324870912 3325001984 14 5989 57661 32 _ _ (548117 / 25000) (2192471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3325001984 :
    ThetaLowerSegment 3325001984 3325133056 (2078074621249 / 625) (10390782276332 / 3125) := by
  exact
    packedTile65536 3325001984 3325133056 14 5972 57662 32 _ _ (274059 / 12500) (87699 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3325133056 :
    ThetaLowerSegment 3325133056 3325264128 (10390782276332 / 3125) (83129533221681 / 25000) := by
  exact
    packedTile65536 3325133056 3325264128 14 5975 57663 32 _ _ (548119 / 25000) (2192479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3325264128 :
    ThetaLowerSegment 3325264128 3325395200 (83129533221681 / 25000) (83132831807841 / 25000) := by
  exact
    packedTile65536 3325264128 3325395200 14 6018 57665 32 _ _ (13703 / 625) (2192483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3325395200 :
    ThetaLowerSegment 3325395200 3325526272 (83132831807841 / 25000) (16627220160297 / 5000) := by
  exact
    packedTile65536 3325395200 3325526272 14 5964 57666 32 _ _ (548121 / 25000) (2192487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3325526272 :
    ThetaLowerSegment 3325526272 3325657344 (16627220160297 / 5000) (83139412006487 / 25000) := by
  exact
    packedTile65536 3325526272 3325657344 14 6041 57667 32 _ _ (274061 / 12500) (2192491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3325657344 :
    ThetaLowerSegment 3325657344 3325788416 (83139412006487 / 25000) (10392839991099 / 3125) := by
  exact
    packedTile65536 3325657344 3325788416 14 6035 57668 32 _ _ (548123 / 25000) (438499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3325788416 :
    ThetaLowerSegment 3325788416 3325919488 (10392839991099 / 3125) (10393249713789 / 3125) := by
  exact
    packedTile65536 3325788416 3325919488 14 5980 57669 32 _ _ (137031 / 6250) (2192499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3325919488 :
    ThetaLowerSegment 3325919488 3326050560 (10393249713789 / 3125) (83149265083437 / 25000) := by
  exact
    packedTile65536 3325919488 3326050560 14 5961 57670 32 _ _ (877 / 40) (2192503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3326050560 :
    ThetaLowerSegment 3326050560 3326181632 (83149265083437 / 25000) (83152523692507 / 25000) := by
  exact
    packedTile65536 3326050560 3326181632 14 5945 57671 32 _ _ (274063 / 12500) (2192507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3326181632 :
    ThetaLowerSegment 3326181632 3326312704 (83152523692507 / 25000) (41577876902459 / 12500) := by
  exact
    packedTile65536 3326181632 3326312704 14 5893 57673 32 _ _ (548127 / 25000) (2192511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3326312704 :
    ThetaLowerSegment 3326312704 3326443776 (41577876902459 / 12500) (41579533071211 / 12500) := by
  exact
    packedTile65536 3326312704 3326443776 14 6043 57674 32 _ _ (68516 / 3125) (438503 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3326443776 :
    ThetaLowerSegment 3326443776 3326574848 (41579533071211 / 12500) (166324615551699 / 50000) := by
  exact
    packedTile65536 3326443776 3326574848 14 5914 57675 32 _ _ (438503 / 20000) (1096259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3326574848 :
    ThetaLowerSegment 3326574848 3326705920 (166324615551699 / 50000)
      (332662405950069 / 100000) := by
  exact
    packedTile65536 3326574848 3326705920 14 6009 57676 32 _ _ (2192519 / 100000) (1096261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3326705920 :
    ThetaLowerSegment 3326705920 3326836992 (332662405950069 / 100000)
      (166337871533739 / 50000) := by
  exact
    packedTile65536 3326705920 3326836992 14 6083 57677 32 _ _ (2192523 / 100000) (1096263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3326836992 :
    ThetaLowerSegment 3326836992 3326968064 (166337871533739 / 50000) (83172186188147 / 25000) := by
  exact
    packedTile65536 3326836992 3326968064 14 5930 57678 32 _ _ (2192527 / 100000) (219253 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3326968064 :
    ThetaLowerSegment 3326968064 3327099136 (83172186188147 / 25000) (66540365517013 / 20000) := by
  exact
    packedTile65536 3326968064 3327099136 14 5967 57679 32 _ _ (2192531 / 100000) (1096267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3327099136 :
    ThetaLowerSegment 3327099136 3327230208 (66540365517013 / 20000) (33271508584421 / 10000) := by
  exact
    packedTile65536 3327099136 3327230208 14 6047 57681 32 _ _ (438507 / 20000) (1096269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3327230208 :
    ThetaLowerSegment 3327230208 3327361280 (33271508584421 / 10000) (13309132712683 / 4000) := by
  exact
    packedTile65536 3327230208 3327361280 14 6035 57682 32 _ _ (2192539 / 100000) (1096271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3327361280 :
    ThetaLowerSegment 3327361280 3327492352 (13309132712683 / 4000) (6654826172687 / 2000) := by
  exact
    packedTile65536 3327361280 3327492352 14 5925 57683 32 _ _ (2192543 / 100000) (1096273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3327492352 :
    ThetaLowerSegment 3327492352 3327623424 (6654826172687 / 2000) (332754654667939 / 100000) := by
  exact
    packedTile65536 3327492352 3327623424 14 6087 57684 32 _ _ (2192547 / 100000) (43851 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3327623424 :
    ThetaLowerSegment 3327623424 3327754496 (332754654667939 / 100000)
      (166383721908961 / 50000) := by
  exact
    packedTile65536 3327623424 3327754496 14 5833 57685 32 _ _ (2192551 / 100000) (1096277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3327754496 :
    ThetaLowerSegment 3327754496 3327885568 (166383721908961 / 50000)
      (332780478557397 / 100000) := by
  exact
    packedTile65536 3327754496 3327885568 14 5945 57686 32 _ _ (438511 / 20000) (1096279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3327885568 :
    ThetaLowerSegment 3327885568 3328016640 (332780478557397 / 100000)
      (166396776393357 / 50000) := by
  exact
    packedTile65536 3327885568 3328016640 14 5963 57687 32 _ _ (2192559 / 100000) (1096281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3328016640 :
    ThetaLowerSegment 3328016640 3328147712 (166396776393357 / 50000)
      (332806653350639 / 100000) := by
  exact
    packedTile65536 3328016640 3328147712 14 5975 57688 32 _ _ (2192563 / 100000) (1096283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3328147712 :
    ThetaLowerSegment 3328147712 3328278784 (332806653350639 / 100000)
      (83204971373121 / 25000) := by
  exact
    packedTile65536 3328147712 3328278784 14 6035 57690 32 _ _ (2192567 / 100000) (219257 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3328278784 :
    ThetaLowerSegment 3328278784 3328409856 (83204971373121 / 25000) (83208308466183 / 25000) := by
  exact
    packedTile65536 3328278784 3328409856 14 6088 57691 32 _ _ (2192571 / 100000) (1096287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3328409856 :
    ThetaLowerSegment 3328409856 3328540928 (83208308466183 / 25000) (166423069680591 / 50000) := by
  exact
    packedTile65536 3328409856 3328540928 14 5886 57692 32 _ _ (87703 / 4000) (1096289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3328540928 :
    ThetaLowerSegment 3328540928 3328672000 (166423069680591 / 50000) (33285924220731 / 10000) := by
  exact
    packedTile65536 3328540928 3328672000 14 5976 57693 32 _ _ (1096289 / 50000) (2192581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3328672000 :
    ThetaLowerSegment 3328672000 3328803072 (33285924220731 / 10000) (166436157190597 / 50000) := by
  exact
    packedTile65536 3328672000 3328803072 14 5962 57694 32 _ _ (1096291 / 50000) (438517 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3328803072 :
    ThetaLowerSegment 3328803072 3328934144 (166436157190597 / 50000) (83221350481757 / 25000) := by
  exact
    packedTile65536 3328803072 3328934144 14 5969 57695 32 _ _ (1096293 / 50000) (2192589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3328934144 :
    ThetaLowerSegment 3328934144 3329065216 (83221350481757 / 25000) (166449317103839 / 50000) := by
  exact
    packedTile65536 3328934144 3329065216 14 6035 57696 32 _ _ (219259 / 10000) (2192593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3329065216 :
    ThetaLowerSegment 3329065216 3329196288 (166449317103839 / 50000) (83227899754 / 25) := by
  exact
    packedTile65536 3329065216 3329196288 14 5913 57698 32 _ _ (1096297 / 50000) (2192597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3329196288 :
    ThetaLowerSegment 3329196288 3329327360 (83227899754 / 25) (166462325775947 / 50000) := by
  exact
    packedTile65536 3329196288 3329327360 14 5953 57699 32 _ _ (1096299 / 50000) (2192601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3329327360 :
    ThetaLowerSegment 3329327360 3329458432 (166462325775947 / 50000) (10404298320133 / 3125) := by
  exact
    packedTile65536 3329327360 3329458432 14 5881 57700 32 _ _ (1096301 / 50000) (438521 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3329458432 :
    ThetaLowerSegment 3329458432 3329589504 (10404298320133 / 3125) (83237659025519 / 25000) := by
  exact
    packedTile65536 3329458432 3329589504 14 5970 57701 32 _ _ (1096303 / 50000) (2192609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3329589504 :
    ThetaLowerSegment 3329589504 3329720576 (83237659025519 / 25000) (10405116436993 / 3125) := by
  exact
    packedTile65536 3329589504 3329720576 14 5970 57702 32 _ _ (219261 / 10000) (2192613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3329720576 :
    ThetaLowerSegment 3329720576 3329851648 (10405116436993 / 3125) (8324421822433 / 2500) := by
  exact
    packedTile65536 3329720576 3329851648 14 5996 57703 32 _ _ (1096307 / 50000) (2192617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3329851648 :
    ThetaLowerSegment 3329851648 3329982720 (8324421822433 / 2500) (33298984223279 / 10000) := by
  exact
    packedTile65536 3329851648 3329982720 14 5915 57704 32 _ _ (1096309 / 50000) (2192621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3329982720 :
    ThetaLowerSegment 3329982720 3330113792 (33298984223279 / 10000) (166501604228251 / 50000) := by
  exact
    packedTile65536 3329982720 3330113792 14 6096 57706 32 _ _ (1096311 / 50000) (17541 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3330113792 :
    ThetaLowerSegment 3330113792 3330244864 (166501604228251 / 50000) (41627026067007 / 12500) := by
  exact
    packedTile65536 3330113792 3330244864 14 5929 57707 32 _ _ (1096313 / 50000) (2192629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3330244864 :
    ThetaLowerSegment 3330244864 3330375936 (41627026067007 / 12500) (20814331432651 / 6250) := by
  exact
    packedTile65536 3330244864 3330375936 14 5972 57708 32 _ _ (219263 / 10000) (2192633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3330375936 :
    ThetaLowerSegment 3330375936 3330507008 (20814331432651 / 6250) (166521151524701 / 50000) := by
  exact
    packedTile65536 3330375936 3330507008 14 5929 57709 32 _ _ (1096317 / 50000) (2192637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3330507008 :
    ThetaLowerSegment 3330507008 3330638080 (166521151524701 / 50000)
      (166527744787167 / 50000) := by
  exact
    packedTile65536 3330507008 3330638080 14 6014 57710 32 _ _ (1096319 / 50000) (2192641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3330638080 :
    ThetaLowerSegment 3330638080 3330769152 (166527744787167 / 50000) (20816790612851 / 6250) := by
  exact
    packedTile65536 3330638080 3330769152 14 6002 57711 32 _ _ (2192641 / 100000) (548161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3330769152 :
    ThetaLowerSegment 3330769152 3330900224 (20816790612851 / 6250) (166540918186323 / 50000) := by
  exact
    packedTile65536 3330769152 3330900224 14 6014 57712 32 _ _ (438529 / 20000) (274081 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3330900224 :
    ThetaLowerSegment 3330900224 3331031296 (166540918186323 / 50000) (10409218097211 / 3125) := by
  exact
    packedTile65536 3330900224 3331031296 14 5994 57713 32 _ _ (2192649 / 100000) (548163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3331031296 :
    ThetaLowerSegment 3331031296 3331162368 (10409218097211 / 3125) (41638501530023 / 12500) := by
  exact
    packedTile65536 3331031296 3331162368 14 5944 57715 32 _ _ (2192653 / 100000) (137041 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3331162368 :
    ThetaLowerSegment 3331162368 3331293440 (41638501530023 / 12500)
      (333121157218899 / 100000) := by
  exact
    packedTile65536 3331162368 3331293440 14 5995 57716 32 _ _ (2192657 / 100000) (109633 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3331293440 :
    ThetaLowerSegment 3331293440 3331424512 (333121157218899 / 100000)
      (333134168469273 / 100000) := by
  exact
    packedTile65536 3331293440 3331424512 14 5934 57717 32 _ _ (2192661 / 100000) (274083 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3331424512 :
    ThetaLowerSegment 3331424512 3331555584 (333134168469273 / 100000)
      (333147491101813 / 100000) := by
  exact
    packedTile65536 3331424512 3331555584 14 6076 57718 32 _ _ (438533 / 20000) (548167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3331555584 :
    ThetaLowerSegment 3331555584 3331686656 (333147491101813 / 100000)
      (333160673427841 / 100000) := by
  exact
    packedTile65536 3331555584 3331686656 14 6012 57719 32 _ _ (2192669 / 100000) (68521 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3331686656 :
    ThetaLowerSegment 3331686656 3331817728 (333160673427841 / 100000)
      (66634760630753 / 20000) := by
  exact
    packedTile65536 3331686656 3331817728 14 5988 57720 32 _ _ (2192673 / 100000) (548169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3331817728 :
    ThetaLowerSegment 3331817728 3331948800 (66634760630753 / 20000) (83296728292387 / 25000) := by
  exact
    packedTile65536 3331817728 3331948800 14 5979 57721 32 _ _ (2192677 / 100000) (54817 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3331948800 :
    ThetaLowerSegment 3331948800 3332079872 (83296728292387 / 25000) (20825007069323 / 6250) := by
  exact
    packedTile65536 3331948800 3332079872 14 6020 57723 32 _ _ (2192681 / 100000) (548171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3332079872 :
    ThetaLowerSegment 3332079872 3332210944 (20825007069323 / 6250) (166606540324129 / 50000) := by
  exact
    packedTile65536 3332079872 3332210944 14 5914 57724 32 _ _ (438537 / 20000) (137043 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3332210944 :
    ThetaLowerSegment 3332210944 3332342016 (166606540324129 / 50000)
      (333226300370239 / 100000) := by
  exact
    packedTile65536 3332210944 3332342016 14 6029 57725 32 _ _ (2192689 / 100000) (548173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3332342016 :
    ThetaLowerSegment 3332342016 3332473088 (333226300370239 / 100000)
      (166619718397001 / 50000) := by
  exact
    packedTile65536 3332342016 3332473088 14 5991 57726 32 _ _ (2192693 / 100000) (274087 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3332473088 :
    ThetaLowerSegment 3332473088 3332604160 (166619718397001 / 50000)
      (166626261404849 / 50000) := by
  exact
    packedTile65536 3332473088 3332604160 14 5968 57727 32 _ _ (2192697 / 100000) (21927 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3332604160 :
    ThetaLowerSegment 3332604160 3332735232 (166626261404849 / 50000)
      (166632703557449 / 50000) := by
  exact
    packedTile65536 3332604160 3332735232 14 5876 57728 32 _ _ (21927 / 1000) (2192703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3332735232 :
    ThetaLowerSegment 3332735232 3332866304 (166632703557449 / 50000)
      (166639316752713 / 50000) := by
  exact
    packedTile65536 3332735232 3332866304 14 6032 57729 32 _ _ (68522 / 3125) (2192707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3332866304 :
    ThetaLowerSegment 3332866304 3332997376 (166639316752713 / 50000)
      (166645911322023 / 50000) := by
  exact
    packedTile65536 3332866304 3332997376 14 6015 57730 32 _ _ (548177 / 25000) (2192711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3332997376 :
    ThetaLowerSegment 3332997376 3333128448 (166645911322023 / 50000)
      (166652533312263 / 50000) := by
  exact
    packedTile65536 3332997376 3333128448 14 6040 57732 32 _ _ (274089 / 12500) (438543 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3333128448 :
    ThetaLowerSegment 3333128448 3333259520 (166652533312263 / 50000)
      (166659014980759 / 50000) := by
  exact
    packedTile65536 3333128448 3333259520 14 5912 57733 32 _ _ (548179 / 25000) (2192719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3333259520 :
    ThetaLowerSegment 3333259520 3333390592 (166659014980759 / 50000)
      (166665574502639 / 50000) := by
  exact
    packedTile65536 3333259520 3333390592 14 5983 57734 32 _ _ (27409 / 1250) (2192723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3333390592 :
    ThetaLowerSegment 3333390592 3333521664 (166665574502639 / 50000)
      (166672146096467 / 50000) := by
  exact
    packedTile65536 3333390592 3333521664 14 5994 57735 32 _ _ (548181 / 25000) (2192727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3333521664 :
    ThetaLowerSegment 3333521664 3333652736 (166672146096467 / 50000)
      (166678654113171 / 50000) := by
  exact
    packedTile65536 3333521664 3333652736 14 5936 57736 32 _ _ (274091 / 12500) (2192731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3333652736 :
    ThetaLowerSegment 3333652736 3333783808 (166678654113171 / 50000)
      (166685281645641 / 50000) := by
  exact
    packedTile65536 3333652736 3333783808 14 6045 57737 32 _ _ (548183 / 25000) (438547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3333783808 :
    ThetaLowerSegment 3333783808 3333914880 (166685281645641 / 50000)
      (166691751313209 / 50000) := by
  exact
    packedTile65536 3333783808 3333914880 14 5901 57738 32 _ _ (68523 / 3125) (2192739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3333914880 :
    ThetaLowerSegment 3333914880 3334045952 (166691751313209 / 50000)
      (166698354749719 / 50000) := by
  exact
    packedTile65536 3333914880 3334045952 14 6023 57740 32 _ _ (109637 / 5000) (2192743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3334045952 :
    ThetaLowerSegment 3334045952 3334177024 (166698354749719 / 50000) (6668192846071 / 2000) := by
  exact
    packedTile65536 3334045952 3334177024 14 5898 57741 32 _ _ (274093 / 12500) (2192747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3334177024 :
    ThetaLowerSegment 3334177024 3334308096 (6668192846071 / 2000) (166711455310849 / 50000) := by
  exact
    packedTile65536 3334177024 3334308096 14 6051 57742 32 _ _ (548187 / 25000) (2192751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3334308096 :
    ThetaLowerSegment 3334308096 3334439168 (166711455310849 / 50000)
      (166717964495161 / 50000) := by
  exact
    packedTile65536 3334308096 3334439168 14 5937 57743 32 _ _ (137047 / 6250) (438551 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3334439168 :
    ThetaLowerSegment 3334439168 3334570240 (166717964495161 / 50000)
      (166724498908041 / 50000) := by
  exact
    packedTile65536 3334439168 3334570240 14 5960 57744 32 _ _ (548189 / 25000) (2192759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3334570240 :
    ThetaLowerSegment 3334570240 3334701312 (166724498908041 / 50000)
      (333462217960093 / 100000) := by
  exact
    packedTile65536 3334570240 3334701312 14 6029 57745 32 _ _ (2192759 / 100000) (1096381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3334701312 :
    ThetaLowerSegment 3334701312 3334832384 (333462217960093 / 100000)
      (333475247357839 / 100000) := by
  exact
    packedTile65536 3334701312 3334832384 14 5942 57746 32 _ _ (2192763 / 100000) (1096383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3334832384 :
    ThetaLowerSegment 3334832384 3334963456 (333475247357839 / 100000)
      (41686061184719 / 12500) := by
  exact
    packedTile65536 3334832384 3334963456 14 6039 57748 32 _ _ (2192767 / 100000) (219277 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3334963456 :
    ThetaLowerSegment 3334963456 3335094528 (41686061184719 / 12500)
      (333501490417011 / 100000) := by
  exact
    packedTile65536 3334963456 3335094528 14 5929 57749 32 _ _ (2192771 / 100000) (1096387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3335094528 :
    ThetaLowerSegment 3335094528 3335225600 (333501490417011 / 100000)
      (333514611982611 / 100000) := by
  exact
    packedTile65536 3335094528 3335225600 14 5984 57750 32 _ _ (87711 / 4000) (1096389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3335225600 :
    ThetaLowerSegment 3335225600 3335356672 (333514611982611 / 100000)
      (166763894195811 / 50000) := by
  exact
    packedTile65536 3335225600 3335356672 14 6009 57751 32 _ _ (2192779 / 100000) (1096391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3335356672 :
    ThetaLowerSegment 3335356672 3335487744 (166763894195811 / 50000)
      (333540899041179 / 100000) := by
  exact
    packedTile65536 3335356672 3335487744 14 5979 57752 32 _ _ (2192783 / 100000) (1096393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3335487744 :
    ThetaLowerSegment 3335487744 3335618816 (333540899041179 / 100000)
      (333553906653663 / 100000) := by
  exact
    packedTile65536 3335487744 3335618816 14 5932 57753 32 _ _ (2192787 / 100000) (219279 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3335618816 :
    ThetaLowerSegment 3335618816 3335749888 (333553906653663 / 100000)
      (41695878265277 / 12500) := by
  exact
    packedTile65536 3335618816 3335749888 14 5983 57754 32 _ _ (2192791 / 100000) (1096397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3335749888 :
    ThetaLowerSegment 3335749888 3335880960 (41695878265277 / 12500)
      (333580211398551 / 100000) := by
  exact
    packedTile65536 3335749888 3335880960 14 6013 57755 32 _ _ (438559 / 20000) (1096399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3335880960 :
    ThetaLowerSegment 3335880960 3336012032 (333580211398551 / 100000)
      (333593267323797 / 100000) := by
  exact
    packedTile65536 3335880960 3336012032 14 5954 57757 32 _ _ (2192799 / 100000) (1096401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3336012032 :
    ThetaLowerSegment 3336012032 3336143104 (333593267323797 / 100000)
      (66721256760481 / 20000) := by
  exact
    packedTile65536 3336012032 3336143104 14 5936 57758 32 _ _ (2192803 / 100000) (1096403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3336143104 :
    ThetaLowerSegment 3336143104 3336274176 (66721256760481 / 20000) (41702422679827 / 12500) := by
  exact
    packedTile65536 3336143104 3336274176 14 5973 57759 32 _ _ (2192807 / 100000) (219281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3336274176 :
    ThetaLowerSegment 3336274176 3336405248 (41702422679827 / 12500)
      (333632334373193 / 100000) := by
  exact
    packedTile65536 3336274176 3336405248 14 5907 57760 32 _ _ (2192811 / 100000) (1096407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3336405248 :
    ThetaLowerSegment 3336405248 3336536320 (333632334373193 / 100000)
      (333645521956589 / 100000) := by
  exact
    packedTile65536 3336405248 3336536320 14 6014 57761 32 _ _ (1096407 / 50000) (2192817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3336536320 :
    ThetaLowerSegment 3336536320 3336667392 (333645521956589 / 100000)
      (333658709564041 / 100000) := by
  exact
    packedTile65536 3336536320 3336667392 14 6014 57762 32 _ _ (1096409 / 50000) (2192821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3336667392 :
    ThetaLowerSegment 3336667392 3336798464 (333658709564041 / 100000)
      (333671842374999 / 100000) := by
  exact
    packedTile65536 3336667392 3336798464 14 5989 57763 32 _ _ (1096411 / 50000) (87713 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3336798464 :
    ThetaLowerSegment 3336798464 3336929536 (333671842374999 / 100000)
      (333684931353393 / 100000) := by
  exact
    packedTile65536 3336798464 3336929536 14 5969 57765 32 _ _ (1096413 / 50000) (2192829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3336929536 :
    ThetaLowerSegment 3336929536 3337060608 (333684931353393 / 100000)
      (333698037898303 / 100000) := by
  exact
    packedTile65536 3336929536 3337060608 14 5977 57766 32 _ _ (219283 / 10000) (2192833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337060608 :
    ThetaLowerSegment 3337060608 3337191680 (333698037898303 / 100000)
      (333711197095137 / 100000) := by
  exact
    packedTile65536 3337060608 3337191680 14 6001 57767 32 _ _ (1096417 / 50000) (2192837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337191680 :
    ThetaLowerSegment 3337191680 3337322752 (333711197095137 / 100000)
      (66744851527653 / 20000) := by
  exact
    packedTile65536 3337191680 3337322752 14 5956 57768 32 _ _ (1096419 / 50000) (2192841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337322752 :
    ThetaLowerSegment 3337322752 3337339136 (66744851527653 / 20000)
      (333725941740921 / 100000) := by
  exact
    packedTile65536 3337322752 3337339136 11 768 57769 32 _ _ (1096421 / 50000) (438569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337339136 :
    ThetaLowerSegment 3337339136 3337341184 (333725941740921 / 100000)
      (66745235275003 / 20000) := by
  exact
    packedTile65536 3337339136 3337341184 8 107 57769 32 _ _ (1096421 / 50000) (438569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3305341184_3337341184 :
    ThetaLowerSegment 3305341184 3337341184 (330525015691687 / 100000)
      (66745235275003 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3305341184 cell3305472256)
                  (ThetaLowerSegment.join cell3305603328 cell3305734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3305865472 cell3305996544)
                  (ThetaLowerSegment.join cell3306127616 cell3306258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3306389760 cell3306520832)
                  (ThetaLowerSegment.join cell3306651904 cell3306782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3306914048 cell3307045120)
                  (ThetaLowerSegment.join cell3307176192 cell3307307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3307438336 cell3307569408)
                  (ThetaLowerSegment.join cell3307700480 cell3307831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3307962624 cell3308093696)
                  (ThetaLowerSegment.join cell3308224768 cell3308355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3308486912 cell3308617984)
                  (ThetaLowerSegment.join cell3308749056 cell3308880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3309011200 cell3309142272)
                  (ThetaLowerSegment.join cell3309273344 cell3309404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3309535488 cell3309666560)
                  (ThetaLowerSegment.join cell3309797632 cell3309928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3310059776 cell3310190848)
                  (ThetaLowerSegment.join cell3310321920 cell3310452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3310584064 cell3310715136)
                  (ThetaLowerSegment.join cell3310846208 cell3310977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3311108352 cell3311239424)
                  (ThetaLowerSegment.join cell3311370496 cell3311501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3311632640 cell3311763712)
                  (ThetaLowerSegment.join cell3311894784 cell3312025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3312156928 cell3312288000)
                  (ThetaLowerSegment.join cell3312419072 cell3312550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3312681216 cell3312812288)
                  (ThetaLowerSegment.join cell3312943360 cell3313074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3313205504 cell3313336576)
                  (ThetaLowerSegment.join cell3313467648 cell3313598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3313729792 cell3313860864)
                  (ThetaLowerSegment.join cell3313991936 cell3314123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3314254080 cell3314385152)
                  (ThetaLowerSegment.join cell3314516224 cell3314647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3314778368 cell3314909440)
                  (ThetaLowerSegment.join cell3315040512 cell3315171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3315302656 cell3315433728)
                  (ThetaLowerSegment.join cell3315564800 cell3315695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3315826944 cell3315958016)
                  (ThetaLowerSegment.join cell3316089088 cell3316220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3316351232 cell3316482304)
                  (ThetaLowerSegment.join cell3316613376 cell3316744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3316875520 cell3317006592)
                  (ThetaLowerSegment.join cell3317137664 cell3317268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3317399808 cell3317530880)
                  (ThetaLowerSegment.join cell3317661952 cell3317793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3317924096 cell3318055168)
                  (ThetaLowerSegment.join cell3318186240 cell3318317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3318448384 cell3318579456)
                  (ThetaLowerSegment.join cell3318710528 cell3318841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3318972672 cell3319103744)
                  (ThetaLowerSegment.join cell3319234816 cell3319365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3319496960 cell3319628032)
                  (ThetaLowerSegment.join cell3319759104 cell3319890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3320021248 cell3320152320)
                  (ThetaLowerSegment.join cell3320283392 cell3320414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3320545536 cell3320676608)
                  (ThetaLowerSegment.join cell3320807680 cell3320938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3321069824 cell3321200896)
                  (ThetaLowerSegment.join cell3321331968 cell3321463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3321594112 cell3321725184)
                  (ThetaLowerSegment.join cell3321856256 cell3321987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3322118400 cell3322249472)
                  (ThetaLowerSegment.join cell3322380544 cell3322511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3322642688 cell3322773760)
                  (ThetaLowerSegment.join cell3322904832 cell3323035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3323166976 cell3323298048)
                  (ThetaLowerSegment.join cell3323429120 cell3323560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3323691264 cell3323822336)
                  (ThetaLowerSegment.join cell3323953408 cell3324084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3324215552 cell3324346624)
                  (ThetaLowerSegment.join cell3324477696 cell3324608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3324739840 cell3324870912)
                  (ThetaLowerSegment.join cell3325001984 cell3325133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3325264128 cell3325395200)
                  (ThetaLowerSegment.join cell3325526272 cell3325657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3325788416 cell3325919488)
                  (ThetaLowerSegment.join cell3326050560 cell3326181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3326312704 cell3326443776)
                  (ThetaLowerSegment.join cell3326574848 cell3326705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3326836992 cell3326968064)
                  (ThetaLowerSegment.join cell3327099136 cell3327230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3327361280 cell3327492352)
                  (ThetaLowerSegment.join cell3327623424 cell3327754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3327885568 cell3328016640)
                  (ThetaLowerSegment.join cell3328147712 cell3328278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3328409856 cell3328540928)
                  (ThetaLowerSegment.join cell3328672000 cell3328803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3328934144 cell3329065216)
                  (ThetaLowerSegment.join cell3329196288 cell3329327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3329458432 cell3329589504)
                  (ThetaLowerSegment.join cell3329720576 cell3329851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3329982720 cell3330113792)
                  (ThetaLowerSegment.join cell3330244864 cell3330375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3330507008 cell3330638080)
                  (ThetaLowerSegment.join cell3330769152 cell3330900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3331031296 cell3331162368)
                  (ThetaLowerSegment.join cell3331293440 cell3331424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3331555584 cell3331686656)
                  (ThetaLowerSegment.join cell3331817728 cell3331948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3332079872 cell3332210944)
                  (ThetaLowerSegment.join cell3332342016 cell3332473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3332604160 cell3332735232)
                  (ThetaLowerSegment.join cell3332866304 cell3332997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3333128448 cell3333259520)
                  (ThetaLowerSegment.join cell3333390592 cell3333521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3333652736 cell3333783808)
                  (ThetaLowerSegment.join cell3333914880 cell3334045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3334177024 cell3334308096)
                  (ThetaLowerSegment.join cell3334439168 cell3334570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3334701312 cell3334832384)
                  (ThetaLowerSegment.join cell3334963456 cell3335094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3335225600 cell3335356672)
                  (ThetaLowerSegment.join cell3335487744 cell3335618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3335749888 cell3335880960)
                  (ThetaLowerSegment.join cell3336012032 cell3336143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3336274176 cell3336405248)
                  (ThetaLowerSegment.join cell3336536320 cell3336667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3336798464 cell3336929536)
                (ThetaLowerSegment.join cell3337060608 cell3337191680))
              (ThetaLowerSegment.join cell3337322752 cell3337339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
