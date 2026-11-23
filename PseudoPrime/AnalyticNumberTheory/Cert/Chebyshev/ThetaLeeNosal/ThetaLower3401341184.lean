/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3401341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3369341184 :
    ThetaLowerSegment 3369341184 3369472256 (168462259715851 / 50000)
      (336937429927047 / 100000) := by
  exact
    packedTile65536 3369341184 3369472256 14 5885 58046 32 _ _ (2193797 / 100000) (10969 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369472256 :
    ThetaLowerSegment 3369472256 3369603328 (336937429927047 / 100000)
      (336950399678559 / 100000) := by
  exact
    packedTile65536 3369472256 3369603328 14 5912 58047 32 _ _ (2193801 / 100000) (548451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369603328 :
    ThetaLowerSegment 3369603328 3369734400 (336950399678559 / 100000)
      (336963518632459 / 100000) := by
  exact
    packedTile65536 3369603328 3369734400 14 5980 58048 32 _ _ (438761 / 20000) (137113 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369734400 :
    ThetaLowerSegment 3369734400 3369865472 (336963518632459 / 100000)
      (336976699030923 / 100000) := by
  exact
    packedTile65536 3369734400 3369865472 14 6008 58049 32 _ _ (137113 / 6250) (2193811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369865472 :
    ThetaLowerSegment 3369865472 3369996544 (336976699030923 / 100000)
      (336989934298719 / 100000) := by
  exact
    packedTile65536 3369865472 3369996544 14 6033 58050 32 _ _ (548453 / 25000) (438763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369996544 :
    ThetaLowerSegment 3369996544 3370127616 (336989934298719 / 100000)
      (67400619877707 / 20000) := by
  exact
    packedTile65536 3369996544 3370127616 14 6001 58051 32 _ _ (274227 / 12500) (2193819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3370127616 :
    ThetaLowerSegment 3370127616 3370258688 (67400619877707 / 20000) (67403214728003 / 20000) := by
  exact
    packedTile65536 3370127616 3370258688 14 5914 58052 32 _ _ (109691 / 5000) (2193823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3370258688 :
    ThetaLowerSegment 3370258688 3370389760 (67403214728003 / 20000)
      (337029227808719 / 100000) := by
  exact
    packedTile65536 3370258688 3370389760 14 5996 58053 32 _ _ (68557 / 3125) (2193827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3370389760 :
    ThetaLowerSegment 3370389760 3370520832 (337029227808719 / 100000)
      (67408481226703 / 20000) := by
  exact
    packedTile65536 3370389760 3370520832 14 6007 58055 32 _ _ (548457 / 25000) (2193831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3370520832 :
    ThetaLowerSegment 3370520832 3370651904 (67408481226703 / 20000)
      (337055564737851 / 100000) := by
  exact
    packedTile65536 3370520832 3370651904 14 5998 58056 32 _ _ (274229 / 12500) (438767 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3370651904 :
    ThetaLowerSegment 3370651904 3370782976 (337055564737851 / 100000)
      (337068668520279 / 100000) := by
  exact
    packedTile65536 3370651904 3370782976 14 5973 58057 32 _ _ (548459 / 25000) (2193839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3370782976 :
    ThetaLowerSegment 3370782976 3370914048 (337068668520279 / 100000)
      (337081743806679 / 100000) := by
  exact
    packedTile65536 3370782976 3370914048 14 5960 58058 32 _ _ (27423 / 1250) (2193843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3370914048 :
    ThetaLowerSegment 3370914048 3371045120 (337081743806679 / 100000)
      (337094924415423 / 100000) := by
  exact
    packedTile65536 3370914048 3371045120 14 6008 58059 32 _ _ (2193843 / 100000) (1096923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3371045120 :
    ThetaLowerSegment 3371045120 3371176192 (337094924415423 / 100000)
      (337108162088221 / 100000) := by
  exact
    packedTile65536 3371045120 3371176192 14 6034 58060 32 _ _ (2193847 / 100000) (43877 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3371176192 :
    ThetaLowerSegment 3371176192 3371307264 (337108162088221 / 100000)
      (337121347132731 / 100000) := by
  exact
    packedTile65536 3371176192 3371307264 14 6010 58061 32 _ _ (2193851 / 100000) (1096927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3371307264 :
    ThetaLowerSegment 3371307264 3371438336 (337121347132731 / 100000)
      (168567216738903 / 50000) := by
  exact
    packedTile65536 3371307264 3371438336 14 5965 58062 32 _ _ (438771 / 20000) (1096929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3371438336 :
    ThetaLowerSegment 3371438336 3371569408 (168567216738903 / 50000) (84286860765419 / 25000) := by
  exact
    packedTile65536 3371438336 3371569408 14 5930 58064 32 _ _ (2193859 / 100000) (1096931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3371569408 :
    ThetaLowerSegment 3371569408 3371700480 (84286860765419 / 25000) (67432105013349 / 20000) := by
  exact
    packedTile65536 3371569408 3371700480 14 5963 58065 32 _ _ (2193863 / 100000) (1096933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3371700480 :
    ThetaLowerSegment 3371700480 3371831552 (67432105013349 / 20000) (84293422615653 / 25000) := by
  exact
    packedTile65536 3371700480 3371831552 14 6001 58066 32 _ _ (2193867 / 100000) (219387 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3371831552 :
    ThetaLowerSegment 3371831552 3371962624 (84293422615653 / 25000) (10537091645874 / 3125) := by
  exact
    packedTile65536 3371831552 3371962624 14 6036 58067 32 _ _ (2193871 / 100000) (1096937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3371962624 :
    ThetaLowerSegment 3371962624 3372093696 (10537091645874 / 3125) (168600001887609 / 50000) := by
  exact
    packedTile65536 3371962624 3372093696 14 5958 58068 32 _ _ (17551 / 800) (1096939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3372093696 :
    ThetaLowerSegment 3372093696 3372224768 (168600001887609 / 50000) (42151628603613 / 12500) := by
  exact
    packedTile65536 3372093696 3372224768 14 5937 58069 32 _ _ (1096939 / 50000) (2193881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3372224768 :
    ThetaLowerSegment 3372224768 3372355840 (42151628603613 / 12500) (84306511831173 / 25000) := by
  exact
    packedTile65536 3372224768 3372355840 14 5934 58070 32 _ _ (1096941 / 50000) (438777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3372355840 :
    ThetaLowerSegment 3372355840 3372486912 (84306511831173 / 25000) (168619637131693 / 50000) := by
  exact
    packedTile65536 3372355840 3372486912 14 6029 58071 32 _ _ (1096943 / 50000) (2193889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3372486912 :
    ThetaLowerSegment 3372486912 3372617984 (168619637131693 / 50000) (84313098979869 / 25000) := by
  exact
    packedTile65536 3372486912 3372617984 14 5981 58073 32 _ _ (219389 / 10000) (2193893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3372617984 :
    ThetaLowerSegment 3372617984 3372749056 (84313098979869 / 25000) (168632771963109 / 50000) := by
  exact
    packedTile65536 3372617984 3372749056 14 5993 58074 32 _ _ (1096947 / 50000) (2193897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3372749056 :
    ThetaLowerSegment 3372749056 3372880128 (168632771963109 / 50000) (21079920166969 / 6250) := by
  exact
    packedTile65536 3372749056 3372880128 14 6007 58075 32 _ _ (1096949 / 50000) (2193901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3372880128 :
    ThetaLowerSegment 3372880128 3373011200 (21079920166969 / 6250) (168645893678957 / 50000) := by
  exact
    packedTile65536 3372880128 3373011200 14 5955 58076 32 _ _ (1096951 / 50000) (438781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3373011200 :
    ThetaLowerSegment 3373011200 3373142272 (168645893678957 / 50000)
      (168652501723829 / 50000) := by
  exact
    packedTile65536 3373011200 3373142272 14 6024 58077 32 _ _ (1096953 / 50000) (2193909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3373142272 :
    ThetaLowerSegment 3373142272 3373273344 (168652501723829 / 50000) (84329552147987 / 25000) := by
  exact
    packedTile65536 3373142272 3373273344 14 6019 58078 32 _ _ (219391 / 10000) (2193913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3373273344 :
    ThetaLowerSegment 3373273344 3373404416 (84329552147987 / 25000) (42166420411787 / 12500) := by
  exact
    packedTile65536 3373273344 3373404416 14 5996 58079 32 _ _ (2193913 / 100000) (548479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3373404416 :
    ThetaLowerSegment 3373404416 3373535488 (42166420411787 / 12500) (8433610537207 / 2500) := by
  exact
    packedTile65536 3373404416 3373535488 14 5952 58081 32 _ _ (2193917 / 100000) (13712 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3373535488 :
    ThetaLowerSegment 3373535488 3373666560 (8433610537207 / 2500) (42169728841679 / 12500) := by
  exact
    packedTile65536 3373535488 3373666560 14 6112 58082 32 _ _ (2193921 / 100000) (548481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3373666560 :
    ThetaLowerSegment 3373666560 3373797632 (42169728841679 / 12500)
      (337370978925957 / 100000) := by
  exact
    packedTile65536 3373666560 3373797632 14 5993 58083 32 _ _ (87757 / 4000) (274241 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3373797632 :
    ThetaLowerSegment 3373797632 3373928704 (337370978925957 / 100000)
      (337383966985637 / 100000) := by
  exact
    packedTile65536 3373797632 3373928704 14 5920 58084 32 _ _ (2193929 / 100000) (548483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3373928704 :
    ThetaLowerSegment 3373928704 3374059776 (337383966985637 / 100000)
      (168698562000919 / 50000) := by
  exact
    packedTile65536 3373928704 3374059776 14 5997 58085 32 _ _ (2193933 / 100000) (137121 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3374059776 :
    ThetaLowerSegment 3374059776 3374190848 (168698562000919 / 50000)
      (168705038502943 / 50000) := by
  exact
    packedTile65536 3374059776 3374190848 14 5904 58086 32 _ _ (2193937 / 100000) (109697 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3374190848 :
    ThetaLowerSegment 3374190848 3374321920 (168705038502943 / 50000) (84355756411417 / 25000) := by
  exact
    packedTile65536 3374190848 3374321920 14 5902 58087 32 _ _ (2193941 / 100000) (274243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3374321920 :
    ThetaLowerSegment 3374321920 3374452992 (84355756411417 / 25000)
      (337435941399883 / 100000) := by
  exact
    packedTile65536 3374321920 3374452992 14 5887 58088 32 _ _ (438789 / 20000) (548487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3374452992 :
    ThetaLowerSegment 3374452992 3374584064 (337435941399883 / 100000)
      (337449052433131 / 100000) := by
  exact
    packedTile65536 3374452992 3374584064 14 5976 58090 32 _ _ (548487 / 25000) (2193951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3374584064 :
    ThetaLowerSegment 3374584064 3374715136 (337449052433131 / 100000)
      (337461970422507 / 100000) := by
  exact
    packedTile65536 3374584064 3374715136 14 5888 58091 32 _ _ (68561 / 3125) (438791 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3374715136 :
    ThetaLowerSegment 3374715136 3374846208 (337461970422507 / 100000)
      (337474868689831 / 100000) := by
  exact
    packedTile65536 3374715136 3374846208 14 5879 58092 32 _ _ (548489 / 25000) (2193959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3374846208 :
    ThetaLowerSegment 3374846208 3374977280 (337474868689831 / 100000)
      (337487955661231 / 100000) := by
  exact
    packedTile65536 3374846208 3374977280 14 5965 58093 32 _ _ (54849 / 2500) (2193963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3374977280 :
    ThetaLowerSegment 3374977280 3375108352 (337487955661231 / 100000) (540001777071 / 160) := by
  exact
    packedTile65536 3374977280 3375108352 14 5996 58094 32 _ _ (548491 / 25000) (2193967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3375108352 :
    ThetaLowerSegment 3375108352 3375239424 (540001777071 / 160) (337514366624031 / 100000) := by
  exact
    packedTile65536 3375108352 3375239424 14 6042 58095 32 _ _ (137123 / 6250) (2193971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3375239424 :
    ThetaLowerSegment 3375239424 3375370496 (337514366624031 / 100000)
      (67505471865243 / 20000) := by
  exact
    packedTile65536 3375239424 3375370496 14 5922 58096 32 _ _ (548493 / 25000) (87759 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3375370496 :
    ThetaLowerSegment 3375370496 3375501568 (67505471865243 / 20000)
      (337540652626799 / 100000) := by
  exact
    packedTile65536 3375370496 3375501568 14 6059 58097 32 _ _ (274247 / 12500) (2193979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3375501568 :
    ThetaLowerSegment 3375501568 3375632640 (337540652626799 / 100000)
      (42194225691363 / 12500) := by
  exact
    packedTile65536 3375501568 3375632640 14 5995 58099 32 _ _ (2193979 / 100000) (1096991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3375632640 :
    ThetaLowerSegment 3375632640 3375763712 (42194225691363 / 12500) (33756692993721 / 10000) := by
  exact
    packedTile65536 3375632640 3375763712 14 5982 58100 32 _ _ (2193983 / 100000) (1096993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3375763712 :
    ThetaLowerSegment 3375763712 3375894784 (33756692993721 / 10000)
      (337580030233587 / 100000) := by
  exact
    packedTile65536 3375763712 3375894784 14 5971 58101 32 _ _ (2193987 / 100000) (219399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3375894784 :
    ThetaLowerSegment 3375894784 3376025856 (337580030233587 / 100000) (16879662232069 / 5000) := by
  exact
    packedTile65536 3375894784 3376025856 14 6023 58102 32 _ _ (2193991 / 100000) (1096997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376025856 :
    ThetaLowerSegment 3376025856 3376156928 (16879662232069 / 5000) (33760634279153 / 10000) := by
  exact
    packedTile65536 3376025856 3376156928 14 5970 58103 32 _ _ (438799 / 20000) (1096999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376156928 :
    ThetaLowerSegment 3376156928 3376288000 (33760634279153 / 10000) (21101216157347 / 6250) := by
  exact
    packedTile65536 3376156928 3376288000 14 5978 58104 32 _ _ (2193999 / 100000) (1097001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376288000 :
    ThetaLowerSegment 3376288000 3376419072 (21101216157347 / 6250) (337632488701369 / 100000) := by
  exact
    packedTile65536 3376288000 3376419072 14 5939 58105 32 _ _ (2194003 / 100000) (1097003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376419072 :
    ThetaLowerSegment 3376419072 3376550144 (337632488701369 / 100000)
      (337645617639257 / 100000) := by
  exact
    packedTile65536 3376419072 3376550144 14 5984 58106 32 _ _ (2194007 / 100000) (219401 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376550144 :
    ThetaLowerSegment 3376550144 3376681216 (337645617639257 / 100000)
      (67531777403557 / 20000) := by
  exact
    packedTile65536 3376550144 3376681216 14 6048 58108 32 _ _ (2194011 / 100000) (1097007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376681216 :
    ThetaLowerSegment 3376681216 3376812288 (67531777403557 / 20000)
      (337671844864469 / 100000) := by
  exact
    packedTile65536 3376681216 3376812288 14 5906 58109 32 _ _ (1097007 / 50000) (2194017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376812288 :
    ThetaLowerSegment 3376812288 3376943360 (337671844864469 / 100000)
      (337685223986233 / 100000) := by
  exact
    packedTile65536 3376812288 3376943360 14 6098 58110 32 _ _ (1097009 / 50000) (2194021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376943360 :
    ThetaLowerSegment 3376943360 3377074432 (337685223986233 / 100000) (13507927714011 / 4000) := by
  exact
    packedTile65536 3376943360 3377074432 14 5911 58111 32 _ _ (1097011 / 50000) (87761 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3377074432 :
    ThetaLowerSegment 3377074432 3377205504 (13507927714011 / 4000) (337711407468873 / 100000) := by
  exact
    packedTile65536 3377074432 3377205504 14 6023 58112 32 _ _ (1097013 / 50000) (2194029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3377205504 :
    ThetaLowerSegment 3377205504 3377336576 (337711407468873 / 100000)
      (337724415872743 / 100000) := by
  exact
    packedTile65536 3377205504 3377336576 14 5929 58113 32 _ _ (219403 / 10000) (2194033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3377336576 :
    ThetaLowerSegment 3377336576 3377467648 (337724415872743 / 100000)
      (337737518643791 / 100000) := by
  exact
    packedTile65536 3377336576 3377467648 14 5972 58114 32 _ _ (1097017 / 50000) (2194037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3377467648 :
    ThetaLowerSegment 3377467648 3377598720 (337737518643791 / 100000)
      (67550140084819 / 20000) := by
  exact
    packedTile65536 3377467648 3377598720 14 6008 58115 32 _ _ (1097019 / 50000) (2194041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3377598720 :
    ThetaLowerSegment 3377598720 3377729792 (67550140084819 / 20000)
      (337763588226803 / 100000) := by
  exact
    packedTile65536 3377598720 3377729792 14 5874 58117 32 _ _ (1097021 / 50000) (438809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3377729792 :
    ThetaLowerSegment 3377729792 3377860864 (337763588226803 / 100000)
      (168888344434749 / 50000) := by
  exact
    packedTile65536 3377729792 3377860864 14 5971 58118 32 _ _ (438809 / 20000) (68564 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3377860864 :
    ThetaLowerSegment 3377860864 3377991936 (168888344434749 / 50000) (16889490244721 / 5000) := by
  exact
    packedTile65536 3377860864 3377991936 14 5978 58119 32 _ _ (2194049 / 100000) (548513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3377991936 :
    ThetaLowerSegment 3377991936 3378123008 (16889490244721 / 5000) (168901456083521 / 50000) := by
  exact
    packedTile65536 3377991936 3378123008 14 5974 58120 32 _ _ (2194053 / 100000) (274257 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3378123008 :
    ThetaLowerSegment 3378123008 3378254080 (168901456083521 / 50000)
      (337815947059679 / 100000) := by
  exact
    packedTile65536 3378123008 3378254080 14 5941 58121 32 _ _ (2194057 / 100000) (109703 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3378254080 :
    ThetaLowerSegment 3378254080 3378385152 (337815947059679 / 100000)
      (84457265240569 / 25000) := by
  exact
    packedTile65536 3378254080 3378385152 14 5977 58122 32 _ _ (2194061 / 100000) (137129 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3378385152 :
    ThetaLowerSegment 3378385152 3378516224 (84457265240569 / 25000)
      (337842030080491 / 100000) := by
  exact
    packedTile65536 3378385152 3378516224 14 5911 58123 32 _ _ (438813 / 20000) (548517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3378516224 :
    ThetaLowerSegment 3378516224 3378647296 (337842030080491 / 100000)
      (337855269092837 / 100000) := by
  exact
    packedTile65536 3378516224 3378647296 14 6034 58125 32 _ _ (2194069 / 100000) (274259 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3378647296 :
    ThetaLowerSegment 3378647296 3378778368 (337855269092837 / 100000)
      (33786834796199 / 10000) := by
  exact
    packedTile65536 3378647296 3378778368 14 5961 58126 32 _ _ (2194073 / 100000) (548519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3378778368 :
    ThetaLowerSegment 3378778368 3378909440 (33786834796199 / 10000) (168940694777839 / 50000) := by
  exact
    packedTile65536 3378778368 3378909440 14 5944 58127 32 _ _ (2194077 / 100000) (13713 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3378909440 :
    ThetaLowerSegment 3378909440 3379040512 (168940694777839 / 50000)
      (168947258368159 / 50000) := by
  exact
    packedTile65536 3378909440 3379040512 14 5983 58128 32 _ _ (13713 / 625) (2194083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3379040512 :
    ThetaLowerSegment 3379040512 3379171584 (168947258368159 / 50000)
      (168953880113671 / 50000) := by
  exact
    packedTile65536 3379040512 3379171584 14 6036 58129 32 _ _ (548521 / 25000) (2194087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3379171584 :
    ThetaLowerSegment 3379171584 3379302656 (168953880113671 / 50000)
      (168960363643711 / 50000) := by
  exact
    packedTile65536 3379171584 3379302656 14 5910 58130 32 _ _ (274261 / 12500) (2194091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3379302656 :
    ThetaLowerSegment 3379302656 3379433728 (168960363643711 / 50000) (33793384576349 / 10000) := by
  exact
    packedTile65536 3379302656 3379433728 14 5979 58131 32 _ _ (548523 / 25000) (438819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3379433728 :
    ThetaLowerSegment 3379433728 3379564800 (33793384576349 / 10000) (168973522722513 / 50000) := by
  exact
    packedTile65536 3379433728 3379564800 14 6016 58132 32 _ _ (137131 / 6250) (2194099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3379564800 :
    ThetaLowerSegment 3379564800 3379695872 (168973522722513 / 50000)
      (168980112701863 / 50000) := by
  exact
    packedTile65536 3379564800 3379695872 14 6007 58134 32 _ _ (21941 / 1000) (2194103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3379695872 :
    ThetaLowerSegment 3379695872 3379826944 (168980112701863 / 50000)
      (168986656617043 / 50000) := by
  exact
    packedTile65536 3379695872 3379826944 14 5965 58135 32 _ _ (274263 / 12500) (2194107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3379826944 :
    ThetaLowerSegment 3379826944 3379958016 (168986656617043 / 50000)
      (168993141303237 / 50000) := by
  exact
    packedTile65536 3379826944 3379958016 14 5911 58136 32 _ _ (548527 / 25000) (2194111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3379958016 :
    ThetaLowerSegment 3379958016 3380089088 (168993141303237 / 50000)
      (337999396807921 / 100000) := by
  exact
    packedTile65536 3379958016 3380089088 14 5977 58137 32 _ _ (2194111 / 100000) (1097057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3380089088 :
    ThetaLowerSegment 3380089088 3380220160 (337999396807921 / 100000)
      (338012434239251 / 100000) := by
  exact
    packedTile65536 3380089088 3380220160 14 5942 58138 32 _ _ (438823 / 20000) (1097059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3380220160 :
    ThetaLowerSegment 3380220160 3380351232 (338012434239251 / 100000)
      (42253174362523 / 12500) := by
  exact
    packedTile65536 3380220160 3380351232 14 5907 58139 32 _ _ (2194119 / 100000) (1097061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3380351232 :
    ThetaLowerSegment 3380351232 3380482304 (42253174362523 / 12500) (10563701148978 / 3125) := by
  exact
    packedTile65536 3380351232 3380482304 14 5944 58140 32 _ _ (2194123 / 100000) (1097063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3380482304 :
    ThetaLowerSegment 3380482304 3380613376 (10563701148978 / 3125) (338051511570089 / 100000) := by
  exact
    packedTile65536 3380482304 3380613376 14 5959 58141 32 _ _ (2194127 / 100000) (219413 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3380613376 :
    ThetaLowerSegment 3380613376 3380744448 (338051511570089 / 100000)
      (338064680744351 / 100000) := by
  exact
    packedTile65536 3380613376 3380744448 14 6002 58143 32 _ _ (2194131 / 100000) (1097067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3380744448 :
    ThetaLowerSegment 3380744448 3380875520 (338064680744351 / 100000)
      (169038809779223 / 50000) := by
  exact
    packedTile65536 3380744448 3380875520 14 5897 58144 32 _ _ (438827 / 20000) (1097069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3380875520 :
    ThetaLowerSegment 3380875520 3381006592 (169038809779223 / 50000)
      (169045440467281 / 50000) := by
  exact
    packedTile65536 3380875520 3381006592 14 6044 58145 32 _ _ (2194139 / 100000) (1097071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3381006592 :
    ThetaLowerSegment 3381006592 3381137664 (169045440467281 / 50000)
      (169052011922571 / 50000) := by
  exact
    packedTile65536 3381006592 3381137664 14 5990 58146 32 _ _ (1097071 / 50000) (438829 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3381137664 :
    ThetaLowerSegment 3381137664 3381268736 (169052011922571 / 50000)
      (169058510983023 / 50000) := by
  exact
    packedTile65536 3381137664 3381268736 14 5924 58147 32 _ _ (1097073 / 50000) (2194149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3381268736 :
    ThetaLowerSegment 3381268736 3381399808 (169058510983023 / 50000)
      (169065067103223 / 50000) := by
  exact
    packedTile65536 3381268736 3381399808 14 5976 58148 32 _ _ (43883 / 2000) (2194153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3381399808 :
    ThetaLowerSegment 3381399808 3381530880 (169065067103223 / 50000) (10566977343586 / 3125) := by
  exact
    packedTile65536 3381399808 3381530880 14 5989 58149 32 _ _ (1097077 / 50000) (2194157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3381530880 :
    ThetaLowerSegment 3381530880 3381661952 (10566977343586 / 3125) (16907820461227 / 5000) := by
  exact
    packedTile65536 3381530880 3381661952 14 5986 58150 32 _ _ (1097079 / 50000) (2194161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3381661952 :
    ThetaLowerSegment 3381661952 3381793024 (16907820461227 / 5000) (169084656545631 / 50000) := by
  exact
    packedTile65536 3381661952 3381793024 14 5881 58152 32 _ _ (1097081 / 50000) (438833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3381793024 :
    ThetaLowerSegment 3381793024 3381924096 (169084656545631 / 50000)
      (169091155665323 / 50000) := by
  exact
    packedTile65536 3381793024 3381924096 14 5924 58153 32 _ _ (1097083 / 50000) (2194169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3381924096 :
    ThetaLowerSegment 3381924096 3382055168 (169091155665323 / 50000) (10568604864728 / 3125) := by
  exact
    packedTile65536 3381924096 3382055168 14 5945 58154 32 _ _ (219417 / 10000) (2194173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3382055168 :
    ThetaLowerSegment 3382055168 3382186240 (10568604864728 / 3125) (169104218665361 / 50000) := by
  exact
    packedTile65536 3382055168 3382186240 14 5962 58155 32 _ _ (2194173 / 100000) (68568 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3382186240 :
    ThetaLowerSegment 3382186240 3382317312 (169104218665361 / 50000)
      (338221604586899 / 100000) := by
  exact
    packedTile65536 3382186240 3382317312 14 6001 58156 32 _ _ (2194177 / 100000) (109709 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3382317312 :
    ThetaLowerSegment 3382317312 3382448384 (338221604586899 / 100000)
      (338234611691867 / 100000) := by
  exact
    packedTile65536 3382317312 3382448384 14 5928 58157 32 _ _ (2194181 / 100000) (274273 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3382448384 :
    ThetaLowerSegment 3382448384 3382579456 (338234611691867 / 100000)
      (338247684646097 / 100000) := by
  exact
    packedTile65536 3382448384 3382579456 14 5958 58158 32 _ _ (438837 / 20000) (548547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3382579456 :
    ThetaLowerSegment 3382579456 3382710528 (338247684646097 / 100000)
      (67652122561537 / 20000) := by
  exact
    packedTile65536 3382579456 3382710528 14 5892 58159 32 _ _ (2194189 / 100000) (137137 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3382710528 :
    ThetaLowerSegment 3382710528 3382841600 (67652122561537 / 20000) (10571059606971 / 3125) := by
  exact
    packedTile65536 3382710528 3382841600 14 6059 58161 32 _ _ (2194193 / 100000) (548549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3382841600 :
    ThetaLowerSegment 3382841600 3382972672 (10571059606971 / 3125) (84571761568677 / 25000) := by
  exact
    packedTile65536 3382841600 3382972672 14 5988 58162 32 _ _ (2194197 / 100000) (10971 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3382972672 :
    ThetaLowerSegment 3382972672 3383103744 (84571761568677 / 25000) (67660054144827 / 20000) := by
  exact
    packedTile65536 3382972672 3383103744 14 6027 58163 32 _ _ (2194201 / 100000) (548551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3383103744 :
    ThetaLowerSegment 3383103744 3383234816 (67660054144827 / 20000)
      (338313453501767 / 100000) := by
  exact
    packedTile65536 3383103744 3383234816 14 6008 58164 32 _ _ (548551 / 25000) (2194207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3383234816 :
    ThetaLowerSegment 3383234816 3383365888 (338313453501767 / 100000)
      (338326451989959 / 100000) := by
  exact
    packedTile65536 3383234816 3383365888 14 5924 58165 32 _ _ (68569 / 3125) (2194211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3383365888 :
    ThetaLowerSegment 3383365888 3383496960 (338326451989959 / 100000)
      (67667883078891 / 20000) := by
  exact
    packedTile65536 3383365888 3383496960 14 5908 58166 32 _ _ (548553 / 25000) (438843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3383496960 :
    ThetaLowerSegment 3383496960 3383628032 (67667883078891 / 20000)
      (338352609215263 / 100000) := by
  exact
    packedTile65536 3383496960 3383628032 14 6013 58167 32 _ _ (274277 / 12500) (2194219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3383628032 :
    ThetaLowerSegment 3383628032 3383759104 (338352609215263 / 100000)
      (338365750398843 / 100000) := by
  exact
    packedTile65536 3383628032 3383759104 14 5989 58168 32 _ _ (109711 / 5000) (2194223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3383759104 :
    ThetaLowerSegment 3383759104 3383890176 (338365750398843 / 100000)
      (338378841139227 / 100000) := by
  exact
    packedTile65536 3383759104 3383890176 14 5966 58170 32 _ _ (137139 / 6250) (2194227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3383890176 :
    ThetaLowerSegment 3383890176 3384021248 (338378841139227 / 100000)
      (338391918738107 / 100000) := by
  exact
    packedTile65536 3383890176 3384021248 14 5960 58171 32 _ _ (548557 / 25000) (2194231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384021248 :
    ThetaLowerSegment 3384021248 3384152320 (338391918738107 / 100000)
      (338405239920579 / 100000) := by
  exact
    packedTile65536 3384021248 3384152320 14 6071 58172 32 _ _ (274279 / 12500) (438847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384152320 :
    ThetaLowerSegment 3384152320 3384283392 (338405239920579 / 100000)
      (169209159877707 / 50000) := by
  exact
    packedTile65536 3384152320 3384283392 14 5961 58173 32 _ _ (438847 / 20000) (1097119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384283392 :
    ThetaLowerSegment 3384283392 3384414464 (169209159877707 / 50000)
      (338431469829741 / 100000) := by
  exact
    packedTile65536 3384283392 3384414464 14 5993 58174 32 _ _ (2194239 / 100000) (1097121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384414464 :
    ThetaLowerSegment 3384414464 3384545536 (338431469829741 / 100000)
      (338444556294993 / 100000) := by
  exact
    packedTile65536 3384414464 3384545536 14 5964 58175 32 _ _ (2194243 / 100000) (1097123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384545536 :
    ThetaLowerSegment 3384545536 3384676608 (338444556294993 / 100000)
      (84614433187057 / 25000) := by
  exact
    packedTile65536 3384545536 3384676608 14 6005 58176 32 _ _ (2194247 / 100000) (8777 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384676608 :
    ThetaLowerSegment 3384676608 3384807680 (84614433187057 / 25000)
      (338470685411881 / 100000) := by
  exact
    packedTile65536 3384676608 3384807680 14 5903 58177 32 _ _ (2194251 / 100000) (1097127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384807680 :
    ThetaLowerSegment 3384807680 3384938752 (338470685411881 / 100000)
      (169241854157653 / 50000) := by
  exact
    packedTile65536 3384807680 3384938752 14 5935 58179 32 _ _ (438851 / 20000) (1097129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384938752 :
    ThetaLowerSegment 3384938752 3385069824 (169241854157653 / 50000)
      (169248445711689 / 50000) := by
  exact
    packedTile65536 3384938752 3385069824 14 6008 58180 32 _ _ (2194259 / 100000) (1097131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3385069824 :
    ThetaLowerSegment 3385069824 3385200896 (169248445711689 / 50000)
      (338509909985757 / 100000) := by
  exact
    packedTile65536 3385069824 3385200896 14 5933 58181 32 _ _ (2194263 / 100000) (1097133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3385200896 :
    ThetaLowerSegment 3385200896 3385331968 (338509909985757 / 100000)
      (338523077776023 / 100000) := by
  exact
    packedTile65536 3385200896 3385331968 14 6001 58182 32 _ _ (1097133 / 50000) (2194269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3385331968 :
    ThetaLowerSegment 3385331968 3385463040 (338523077776023 / 100000)
      (338536350915253 / 100000) := by
  exact
    packedTile65536 3385331968 3385463040 14 6049 58183 32 _ _ (219427 / 10000) (2194273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3385463040 :
    ThetaLowerSegment 3385463040 3385594112 (338536350915253 / 100000)
      (338549323463141 / 100000) := by
  exact
    packedTile65536 3385463040 3385594112 14 5912 58184 32 _ _ (1097137 / 50000) (2194277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3385594112 :
    ThetaLowerSegment 3385594112 3385725184 (338549323463141 / 100000)
      (338562443051303 / 100000) := by
  exact
    packedTile65536 3385594112 3385725184 14 5979 58185 32 _ _ (1097139 / 50000) (2194281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3385725184 :
    ThetaLowerSegment 3385725184 3385856256 (338562443051303 / 100000)
      (338575652628943 / 100000) := by
  exact
    packedTile65536 3385725184 3385856256 14 6020 58186 32 _ _ (1097141 / 50000) (438857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3385856256 :
    ThetaLowerSegment 3385856256 3385987328 (338575652628943 / 100000)
      (338588653773493 / 100000) := by
  exact
    packedTile65536 3385856256 3385987328 14 5925 58188 32 _ _ (1097143 / 50000) (2194289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3385987328 :
    ThetaLowerSegment 3385987328 3386118400 (338588653773493 / 100000)
      (338601902896513 / 100000) := by
  exact
    packedTile65536 3385987328 3386118400 14 6038 58189 32 _ _ (219429 / 10000) (2194293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3386118400 :
    ThetaLowerSegment 3386118400 3386249472 (338601902896513 / 100000)
      (338614947974343 / 100000) := by
  exact
    packedTile65536 3386118400 3386249472 14 5945 58190 32 _ _ (1097147 / 50000) (2194297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3386249472 :
    ThetaLowerSegment 3386249472 3386380544 (338614947974343 / 100000)
      (169314064558211 / 50000) := by
  exact
    packedTile65536 3386249472 3386380544 14 6007 58191 32 _ _ (2194297 / 100000) (21943 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3386380544 :
    ThetaLowerSegment 3386380544 3386511616 (169314064558211 / 50000)
      (169320660627017 / 50000) := by
  exact
    packedTile65536 3386380544 3386511616 14 6012 58192 32 _ _ (2194301 / 100000) (68572 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3386511616 :
    ThetaLowerSegment 3386511616 3386642688 (169320660627017 / 50000)
      (338654379563089 / 100000) := by
  exact
    packedTile65536 3386511616 3386642688 14 5951 58193 32 _ _ (438861 / 20000) (548577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3386642688 :
    ThetaLowerSegment 3386642688 3386773760 (338654379563089 / 100000)
      (338667505919527 / 100000) := by
  exact
    packedTile65536 3386642688 3386773760 14 5982 58194 32 _ _ (2194309 / 100000) (274289 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3386773760 :
    ThetaLowerSegment 3386773760 3386904832 (338667505919527 / 100000)
      (338680610356763 / 100000) := by
  exact
    packedTile65536 3386773760 3386904832 14 5972 58195 32 _ _ (2194313 / 100000) (548579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3386904832 :
    ThetaLowerSegment 3386904832 3387035904 (338680610356763 / 100000)
      (338693802590567 / 100000) := by
  exact
    packedTile65536 3386904832 3387035904 14 6012 58197 32 _ _ (2194317 / 100000) (27429 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3387035904 :
    ThetaLowerSegment 3387035904 3387166976 (338693802590567 / 100000)
      (338707012402987 / 100000) := by
  exact
    packedTile65536 3387035904 3387166976 14 6020 58198 32 _ _ (2194321 / 100000) (548581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3387166976 :
    ThetaLowerSegment 3387166976 3387298048 (338707012402987 / 100000)
      (338720009384039 / 100000) := by
  exact
    packedTile65536 3387166976 3387298048 14 5923 58199 32 _ _ (548581 / 25000) (2194327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3387298048 :
    ThetaLowerSegment 3387298048 3387429120 (338720009384039 / 100000)
      (67746620587843 / 20000) := by
  exact
    packedTile65536 3387298048 3387429120 14 5967 58200 32 _ _ (274291 / 12500) (2194331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3387429120 :
    ThetaLowerSegment 3387429120 3387560192 (67746620587843 / 20000) (67749251591911 / 20000) := by
  exact
    packedTile65536 3387429120 3387560192 14 5995 58201 32 _ _ (548583 / 25000) (438867 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3387560192 :
    ThetaLowerSegment 3387560192 3387691264 (67749251591911 / 20000)
      (338759305481411 / 100000) := by
  exact
    packedTile65536 3387560192 3387691264 14 5946 58202 32 _ _ (68573 / 3125) (2194339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3387691264 :
    ThetaLowerSegment 3387691264 3387822336 (338759305481411 / 100000)
      (338772405691211 / 100000) := by
  exact
    packedTile65536 3387691264 3387822336 14 5970 58203 32 _ _ (109717 / 5000) (2194343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3387822336 :
    ThetaLowerSegment 3387822336 3387953408 (338772405691211 / 100000)
      (338785488370139 / 100000) := by
  exact
    packedTile65536 3387822336 3387953408 14 5962 58205 32 _ _ (274293 / 12500) (2194347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3387953408 :
    ThetaLowerSegment 3387953408 3388084480 (338785488370139 / 100000)
      (338798665429879 / 100000) := by
  exact
    packedTile65536 3387953408 3388084480 14 6005 58206 32 _ _ (548587 / 25000) (2194351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3388084480 :
    ThetaLowerSegment 3388084480 3388215552 (338798665429879 / 100000)
      (338811899566791 / 100000) := by
  exact
    packedTile65536 3388084480 3388215552 14 6031 58207 32 _ _ (137147 / 6250) (438871 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3388215552 :
    ThetaLowerSegment 3388215552 3388346624 (338811899566791 / 100000)
      (42353140618047 / 12500) := by
  exact
    packedTile65536 3388215552 3388346624 14 6027 58208 32 _ _ (438871 / 20000) (1097179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3388346624 :
    ThetaLowerSegment 3388346624 3388477696 (42353140618047 / 12500)
      (338838179186067 / 100000) := by
  exact
    packedTile65536 3388346624 3388477696 14 5949 58209 32 _ _ (2194359 / 100000) (1097181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3388477696 :
    ThetaLowerSegment 3388477696 3388608768 (338838179186067 / 100000)
      (169425533339983 / 50000) := by
  exact
    packedTile65536 3388477696 3388608768 14 5873 58210 32 _ _ (2194363 / 100000) (1097183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3388608768 :
    ThetaLowerSegment 3388608768 3388739840 (169425533339983 / 50000)
      (338864199966461 / 100000) := by
  exact
    packedTile65536 3388608768 3388739840 14 5985 58211 32 _ _ (2194367 / 100000) (219437 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3388739840 :
    ThetaLowerSegment 3388739840 3388870912 (338864199966461 / 100000)
      (169438721497723 / 50000) := by
  exact
    packedTile65536 3388739840 3388870912 14 6035 58212 32 _ _ (2194371 / 100000) (1097187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3388870912 :
    ThetaLowerSegment 3388870912 3389001984 (169438721497723 / 50000)
      (169445238791473 / 50000) := by
  exact
    packedTile65536 3388870912 3389001984 14 5940 58214 32 _ _ (3511 / 160) (1097189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3389001984 :
    ThetaLowerSegment 3389001984 3389133056 (169445238791473 / 50000) (67780698488959 / 20000) := by
  exact
    packedTile65536 3389001984 3389133056 14 5931 58215 32 _ _ (2194379 / 100000) (1097191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3389133056 :
    ThetaLowerSegment 3389133056 3389264128 (67780698488959 / 20000)
      (338916667514323 / 100000) := by
  exact
    packedTile65536 3389133056 3389264128 14 6004 58216 32 _ _ (1097191 / 50000) (438877 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3389264128 :
    ThetaLowerSegment 3389264128 3389395200 (338916667514323 / 100000)
      (338929853579797 / 100000) := by
  exact
    packedTile65536 3389264128 3389395200 14 6009 58217 32 _ _ (1097193 / 50000) (2194389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3389395200 :
    ThetaLowerSegment 3389395200 3389526272 (338929853579797 / 100000)
      (338942969448827 / 100000) := by
  exact
    packedTile65536 3389395200 3389526272 14 5977 58218 32 _ _ (219439 / 10000) (2194393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3389526272 :
    ThetaLowerSegment 3389526272 3389657344 (338942969448827 / 100000)
      (338956269670861 / 100000) := by
  exact
    packedTile65536 3389526272 3389657344 14 6061 58219 32 _ _ (1097197 / 50000) (2194397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3389657344 :
    ThetaLowerSegment 3389657344 3389788416 (338956269670861 / 100000)
      (338969466780433 / 100000) := by
  exact
    packedTile65536 3389657344 3389788416 14 6014 58220 32 _ _ (1097199 / 50000) (2194401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3389788416 :
    ThetaLowerSegment 3389788416 3389919488 (338969466780433 / 100000)
      (67796500744543 / 20000) := by
  exact
    packedTile65536 3389788416 3389919488 14 5941 58221 32 _ _ (1097201 / 50000) (438881 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3389919488 :
    ThetaLowerSegment 3389919488 3390050560 (67796500744543 / 20000)
      (338995641631437 / 100000) := by
  exact
    packedTile65536 3389919488 3390050560 14 5987 58223 32 _ _ (1097203 / 50000) (2194409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3390050560 :
    ThetaLowerSegment 3390050560 3390181632 (338995641631437 / 100000)
      (339008887090197 / 100000) := by
  exact
    packedTile65536 3390050560 3390181632 14 6036 58224 32 _ _ (219441 / 10000) (2194413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3390181632 :
    ThetaLowerSegment 3390181632 3390312704 (339008887090197 / 100000)
      (42377747644071 / 12500) := by
  exact
    packedTile65536 3390181632 3390312704 14 5967 58225 32 _ _ (2194413 / 100000) (137151 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3390312704 :
    ThetaLowerSegment 3390312704 3390443776 (42377747644071 / 12500)
      (339035255181001 / 100000) := by
  exact
    packedTile65536 3390312704 3390443776 14 6049 58226 32 _ _ (2194417 / 100000) (109721 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3390443776 :
    ThetaLowerSegment 3390443776 3390574848 (339035255181001 / 100000)
      (339048325152477 / 100000) := by
  exact
    packedTile65536 3390443776 3390574848 14 5956 58227 32 _ _ (2194421 / 100000) (274303 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3390574848 :
    ThetaLowerSegment 3390574848 3390705920 (339048325152477 / 100000)
      (339061548757527 / 100000) := by
  exact
    packedTile65536 3390574848 3390705920 14 6026 58228 32 _ _ (87777 / 4000) (548607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3390705920 :
    ThetaLowerSegment 3390705920 3390836992 (339061548757527 / 100000)
      (169537325846543 / 50000) := by
  exact
    packedTile65536 3390705920 3390836992 14 5971 58229 32 _ _ (2194429 / 100000) (68576 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3390836992 :
    ThetaLowerSegment 3390836992 3390968064 (169537325846543 / 50000)
      (339087859985313 / 100000) := by
  exact
    packedTile65536 3390836992 3390968064 14 6019 58230 32 _ _ (2194433 / 100000) (548609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3390968064 :
    ThetaLowerSegment 3390968064 3391099136 (339087859985313 / 100000)
      (339100899329967 / 100000) := by
  exact
    packedTile65536 3390968064 3391099136 14 5942 58232 32 _ _ (2194437 / 100000) (54861 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3391099136 :
    ThetaLowerSegment 3391099136 3391230208 (339100899329967 / 100000)
      (339113899192527 / 100000) := by
  exact
    packedTile65536 3391099136 3391230208 14 5924 58233 32 _ _ (54861 / 2500) (2194443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3391230208 :
    ThetaLowerSegment 3391230208 3391361280 (339113899192527 / 100000)
      (339126956134327 / 100000) := by
  exact
    packedTile65536 3391230208 3391361280 14 5950 58234 32 _ _ (548611 / 25000) (2194447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3391361280 :
    ThetaLowerSegment 3391361280 3391492352 (339126956134327 / 100000)
      (339139789266231 / 100000) := by
  exact
    packedTile65536 3391361280 3391492352 14 5848 58235 32 _ _ (137153 / 6250) (2194451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3391492352 :
    ThetaLowerSegment 3391492352 3391623424 (339139789266231 / 100000)
      (339152925255903 / 100000) := by
  exact
    packedTile65536 3391492352 3391623424 14 5986 58236 32 _ _ (548613 / 25000) (438891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3391623424 :
    ThetaLowerSegment 3391623424 3391754496 (339152925255903 / 100000)
      (339165892296407 / 100000) := by
  exact
    packedTile65536 3391623424 3391754496 14 5909 58237 32 _ _ (274307 / 12500) (2194459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3391754496 :
    ThetaLowerSegment 3391754496 3391885568 (339165892296407 / 100000)
      (339178835221487 / 100000) := by
  exact
    packedTile65536 3391754496 3391885568 14 5898 58238 32 _ _ (109723 / 5000) (2194463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3391885568 :
    ThetaLowerSegment 3391885568 3392016640 (339178835221487 / 100000)
      (67838333250499 / 20000) := by
  exact
    packedTile65536 3391885568 3392016640 14 5847 58239 32 _ _ (68577 / 3125) (2194467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392016640 :
    ThetaLowerSegment 3392016640 3392147712 (67838333250499 / 20000)
      (339204808921347 / 100000) := by
  exact
    packedTile65536 3392016640 3392147712 14 5989 58241 32 _ _ (548617 / 25000) (2194471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392147712 :
    ThetaLowerSegment 3392147712 3392278784 (339204808921347 / 100000)
      (339217923080043 / 100000) := by
  exact
    packedTile65536 3392147712 3392278784 14 5976 58242 32 _ _ (2194471 / 100000) (1097237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392278784 :
    ThetaLowerSegment 3392278784 3392409856 (339217923080043 / 100000)
      (169615427560609 / 50000) := by
  exact
    packedTile65536 3392278784 3392409856 14 5893 58243 32 _ _ (87779 / 4000) (1097239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392409856 :
    ThetaLowerSegment 3392409856 3392540928 (169615427560609 / 50000)
      (169622059276147 / 50000) := by
  exact
    packedTile65536 3392409856 3392540928 14 6044 58244 32 _ _ (2194479 / 100000) (1097241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392540928 :
    ThetaLowerSegment 3392540928 3392672000 (169622059276147 / 50000)
      (339257199865457 / 100000) := by
  exact
    packedTile65536 3392540928 3392672000 14 5961 58245 32 _ _ (2194483 / 100000) (1097243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392672000 :
    ThetaLowerSegment 3392672000 3392803072 (339257199865457 / 100000)
      (169635186685459 / 50000) := by
  exact
    packedTile65536 3392672000 3392803072 14 6003 58246 32 _ _ (2194487 / 100000) (219449 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392803072 :
    ThetaLowerSegment 3392803072 3392934144 (169635186685459 / 50000)
      (169641691156783 / 50000) := by
  exact
    packedTile65536 3392803072 3392934144 14 5928 58247 32 _ _ (2194491 / 100000) (1097247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392934144 :
    ThetaLowerSegment 3392934144 3393065216 (169641691156783 / 50000)
      (339296389085431 / 100000) := by
  exact
    packedTile65536 3392934144 3393065216 14 5927 58248 32 _ _ (438899 / 20000) (1097249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3393065216 :
    ThetaLowerSegment 3393065216 3393196288 (339296389085431 / 100000)
      (339309619713873 / 100000) := by
  exact
    packedTile65536 3393065216 3393196288 14 6029 58250 32 _ _ (1097249 / 50000) (2194501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3393196288 :
    ThetaLowerSegment 3393196288 3393327360 (339309619713873 / 100000) (13572907167811 / 4000) := by
  exact
    packedTile65536 3393196288 3393327360 14 5951 58251 32 _ _ (1097251 / 50000) (438901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3393327360 :
    ThetaLowerSegment 3393327360 3393458432 (13572907167811 / 4000) (339335765034553 / 100000) := by
  exact
    packedTile65536 3393327360 3393458432 14 5963 58252 32 _ _ (1097253 / 50000) (2194509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3393458432 :
    ThetaLowerSegment 3393458432 3393589504 (339335765034553 / 100000)
      (339348890398863 / 100000) := by
  exact
    packedTile65536 3393458432 3393589504 14 5981 58253 32 _ _ (219451 / 10000) (2194513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3393589504 :
    ThetaLowerSegment 3393589504 3393720576 (339348890398863 / 100000)
      (339362033343209 / 100000) := by
  exact
    packedTile65536 3393589504 3393720576 14 5989 58254 32 _ _ (1097257 / 50000) (2194517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3393720576 :
    ThetaLowerSegment 3393720576 3393851648 (339362033343209 / 100000)
      (339375283842893 / 100000) := by
  exact
    packedTile65536 3393720576 3393851648 14 6038 58255 32 _ _ (1097259 / 50000) (2194521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3393851648 :
    ThetaLowerSegment 3393851648 3393982720 (339375283842893 / 100000)
      (339388499254377 / 100000) := by
  exact
    packedTile65536 3393851648 3393982720 14 6022 58256 32 _ _ (1097261 / 50000) (87781 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3393982720 :
    ThetaLowerSegment 3393982720 3394113792 (339388499254377 / 100000)
      (42425198150869 / 12500) := by
  exact
    packedTile65536 3393982720 3394113792 14 5963 58257 32 _ _ (87781 / 4000) (68579 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3394113792 :
    ThetaLowerSegment 3394113792 3394244864 (42425198150869 / 12500) (21213412148429 / 6250) := by
  exact
    packedTile65536 3394113792 3394244864 14 5928 58259 32 _ _ (2194529 / 100000) (548633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3394244864 :
    ThetaLowerSegment 3394244864 3394375936 (21213412148429 / 6250) (21214224125639 / 6250) := by
  exact
    packedTile65536 3394244864 3394375936 14 5920 58260 32 _ _ (2194533 / 100000) (274317 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3394375936 :
    ThetaLowerSegment 3394375936 3394507008 (21214224125639 / 6250) (13577627759189 / 4000) := by
  exact
    packedTile65536 3394375936 3394507008 14 5973 58261 32 _ _ (2194537 / 100000) (109727 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3394507008 :
    ThetaLowerSegment 3394507008 3394638080 (13577627759189 / 4000) (13578154449029 / 4000) := by
  exact
    packedTile65536 3394507008 3394638080 14 6000 58262 32 _ _ (2194541 / 100000) (137159 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3394638080 :
    ThetaLowerSegment 3394638080 3394769152 (13578154449029 / 4000) (4243338377401 / 1250) := by
  exact
    packedTile65536 3394638080 3394769152 14 6019 58263 32 _ _ (438909 / 20000) (548637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3394769152 :
    ThetaLowerSegment 3394769152 3394900224 (4243338377401 / 1250) (10608755226891 / 3125) := by
  exact
    packedTile65536 3394769152 3394900224 14 5968 58264 32 _ _ (2194549 / 100000) (274319 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3394900224 :
    ThetaLowerSegment 3394900224 3395031296 (10608755226891 / 3125) (339493240212733 / 100000) := by
  exact
    packedTile65536 3394900224 3395031296 14 5957 58265 32 _ _ (2194553 / 100000) (548639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3395031296 :
    ThetaLowerSegment 3395031296 3395162368 (339493240212733 / 100000)
      (339506420716069 / 100000) := by
  exact
    packedTile65536 3395031296 3395162368 14 6006 58266 32 _ _ (548639 / 25000) (2194559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3395162368 :
    ThetaLowerSegment 3395162368 3395293440 (339506420716069 / 100000)
      (339519798753829 / 100000) := by
  exact
    packedTile65536 3395162368 3395293440 14 6096 58268 32 _ _ (13716 / 625) (2194563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3395293440 :
    ThetaLowerSegment 3395293440 3395424512 (339519798753829 / 100000)
      (67906614734293 / 20000) := by
  exact
    packedTile65536 3395293440 3395424512 14 6049 58269 32 _ _ (548641 / 25000) (2194567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3395424512 :
    ThetaLowerSegment 3395424512 3395555584 (67906614734293 / 20000)
      (339546168658721 / 100000) := by
  exact
    packedTile65536 3395424512 3395555584 14 5967 58270 32 _ _ (274321 / 12500) (2194571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3395555584 :
    ThetaLowerSegment 3395555584 3395686656 (339546168658721 / 100000)
      (67911841761109 / 20000) := by
  exact
    packedTile65536 3395555584 3395686656 14 5942 58271 32 _ _ (548643 / 25000) (87783 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3395686656 :
    ThetaLowerSegment 3395686656 3395817728 (67911841761109 / 20000)
      (339572400401881 / 100000) := by
  exact
    packedTile65536 3395686656 3395817728 14 6011 58272 32 _ _ (137161 / 6250) (2194579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3395817728 :
    ThetaLowerSegment 3395817728 3395948800 (339572400401881 / 100000)
      (339585436207081 / 100000) := by
  exact
    packedTile65536 3395817728 3395948800 14 5940 58273 32 _ _ (109729 / 5000) (2194583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3395948800 :
    ThetaLowerSegment 3395948800 3396079872 (339585436207081 / 100000)
      (42449827932041 / 12500) := by
  exact
    packedTile65536 3395948800 3396079872 14 6009 58274 32 _ _ (2194583 / 100000) (1097293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396079872 :
    ThetaLowerSegment 3396079872 3396210944 (42449827932041 / 12500)
      (339611578103389 / 100000) := by
  exact
    packedTile65536 3396079872 3396210944 14 5903 58275 32 _ _ (2194587 / 100000) (219459 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396210944 :
    ThetaLowerSegment 3396210944 3396342016 (339611578103389 / 100000)
      (84906200128541 / 25000) := by
  exact
    packedTile65536 3396210944 3396342016 14 6025 58277 32 _ _ (2194591 / 100000) (1097297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396342016 :
    ThetaLowerSegment 3396342016 3396473088 (84906200128541 / 25000)
      (339637860549009 / 100000) := by
  exact
    packedTile65536 3396342016 3396473088 14 5951 58278 32 _ _ (438919 / 20000) (1097299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396473088 :
    ThetaLowerSegment 3396473088 3396604160 (339637860549009 / 100000)
      (169825460303829 / 50000) := by
  exact
    packedTile65536 3396473088 3396604160 14 5951 58279 32 _ _ (2194599 / 100000) (1097301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396604160 :
    ThetaLowerSegment 3396604160 3396735232 (169825460303829 / 50000) (2717311634839 / 800) := by
  exact
    packedTile65536 3396604160 3396735232 14 5939 58280 32 _ _ (2194603 / 100000) (1097303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396735232 :
    ThetaLowerSegment 3396735232 3396866304 (2717311634839 / 800) (339676889368533 / 100000) := by
  exact
    packedTile65536 3396735232 3396866304 14 5894 58281 32 _ _ (2194607 / 100000) (219461 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396866304 :
    ThetaLowerSegment 3396866304 3396997376 (339676889368533 / 100000)
      (339690021914773 / 100000) := by
  exact
    packedTile65536 3396866304 3396997376 14 5984 58282 32 _ _ (219461 / 10000) (2194613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396997376 :
    ThetaLowerSegment 3396997376 3397128448 (339690021914773 / 100000)
      (339703235685667 / 100000) := by
  exact
    packedTile65536 3396997376 3397128448 14 6021 58283 32 _ _ (1097307 / 50000) (2194617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3397128448 :
    ThetaLowerSegment 3397128448 3397259520 (339703235685667 / 100000)
      (339716403393667 / 100000) := by
  exact
    packedTile65536 3397128448 3397259520 14 6000 58284 32 _ _ (1097309 / 50000) (2194621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3397259520 :
    ThetaLowerSegment 3397259520 3397390592 (339716403393667 / 100000)
      (339729551374069 / 100000) := by
  exact
    packedTile65536 3397259520 3397390592 14 5991 58286 32 _ _ (1097311 / 50000) (17557 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3397390592 :
    ThetaLowerSegment 3397390592 3397521664 (339729551374069 / 100000)
      (339742558922371 / 100000) := by
  exact
    packedTile65536 3397390592 3397521664 14 5927 58287 32 _ _ (1097313 / 50000) (2194629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3397521664 :
    ThetaLowerSegment 3397521664 3397652736 (339742558922371 / 100000)
      (339755783762751 / 100000) := by
  exact
    packedTile65536 3397521664 3397652736 14 6026 58288 32 _ _ (219463 / 10000) (2194633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3397652736 :
    ThetaLowerSegment 3397652736 3397783808 (339755783762751 / 100000)
      (339768863781391 / 100000) := by
  exact
    packedTile65536 3397652736 3397783808 14 5960 58289 32 _ _ (1097317 / 50000) (2194637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3397783808 :
    ThetaLowerSegment 3397783808 3397914880 (339768863781391 / 100000) (10618177857333 / 3125) := by
  exact
    packedTile65536 3397783808 3397914880 14 5845 58290 32 _ _ (2194637 / 100000) (27433 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3397914880 :
    ThetaLowerSegment 3397914880 3398045952 (10618177857333 / 3125) (339794633232633 / 100000) := by
  exact
    packedTile65536 3397914880 3398045952 14 5897 58291 32 _ _ (2194641 / 100000) (548661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3398045952 :
    ThetaLowerSegment 3398045952 3398177024 (339794633232633 / 100000)
      (339807888888433 / 100000) := by
  exact
    packedTile65536 3398045952 3398177024 14 6040 58292 32 _ _ (438929 / 20000) (274331 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3398177024 :
    ThetaLowerSegment 3398177024 3398308096 (339807888888433 / 100000)
      (339820903157003 / 100000) := by
  exact
    packedTile65536 3398177024 3398308096 14 5930 58293 32 _ _ (2194649 / 100000) (548663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3398308096 :
    ThetaLowerSegment 3398308096 3398439168 (339820903157003 / 100000) (2123963067668 / 625) := by
  exact
    packedTile65536 3398308096 3398439168 14 6009 58295 32 _ _ (2194653 / 100000) (68583 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3398439168 :
    ThetaLowerSegment 3398439168 3398570240 (2123963067668 / 625) (2124044269977 / 625) := by
  exact
    packedTile65536 3398439168 3398570240 14 5920 58296 32 _ _ (2194657 / 100000) (109733 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3398570240 :
    ThetaLowerSegment 3398570240 3398701312 (2124044269977 / 625) (339860165570541 / 100000) := by
  exact
    packedTile65536 3398570240 3398701312 14 5961 58297 32 _ _ (2194661 / 100000) (274333 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3398701312 :
    ThetaLowerSegment 3398701312 3398832384 (339860165570541 / 100000)
      (339873388421141 / 100000) := by
  exact
    packedTile65536 3398701312 3398832384 14 6025 58298 32 _ _ (274333 / 12500) (2194667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3398832384 :
    ThetaLowerSegment 3398832384 3398963456 (339873388421141 / 100000)
      (339886437917069 / 100000) := by
  exact
    packedTile65536 3398832384 3398963456 14 5946 58299 32 _ _ (548667 / 25000) (2194671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3398963456 :
    ThetaLowerSegment 3398963456 3399094528 (339886437917069 / 100000)
      (339899682762589 / 100000) := by
  exact
    packedTile65536 3398963456 3399094528 14 6035 58300 32 _ _ (137167 / 6250) (87787 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3399094528 :
    ThetaLowerSegment 3399094528 3399225600 (339899682762589 / 100000)
      (339912839845209 / 100000) := by
  exact
    packedTile65536 3399094528 3399225600 14 5995 58301 32 _ _ (548669 / 25000) (2194679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3399225600 :
    ThetaLowerSegment 3399225600 3399356672 (339912839845209 / 100000)
      (339925964031609 / 100000) := by
  exact
    packedTile65536 3399225600 3399356672 14 5980 58302 32 _ _ (54867 / 2500) (2194683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3399356672 :
    ThetaLowerSegment 3399356672 3399487744 (339925964031609 / 100000)
      (339939110188769 / 100000) := by
  exact
    packedTile65536 3399356672 3399487744 14 5990 58304 32 _ _ (548671 / 25000) (2194687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3399487744 :
    ThetaLowerSegment 3399487744 3399618816 (339939110188769 / 100000)
      (339952265148641 / 100000) := by
  exact
    packedTile65536 3399487744 3399618816 14 5994 58305 32 _ _ (68584 / 3125) (2194691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3399618816 :
    ThetaLowerSegment 3399618816 3399749888 (339952265148641 / 100000)
      (169982640930481 / 50000) := by
  exact
    packedTile65536 3399618816 3399749888 14 5931 58306 32 _ _ (2194691 / 100000) (1097347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3399749888 :
    ThetaLowerSegment 3399749888 3399880960 (169982640930481 / 50000)
      (339978333712127 / 100000) := by
  exact
    packedTile65536 3399749888 3399880960 14 5947 58307 32 _ _ (438939 / 20000) (1097349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3399880960 :
    ThetaLowerSegment 3399880960 3400012032 (339978333712127 / 100000)
      (169995694988239 / 50000) := by
  exact
    packedTile65536 3399880960 3400012032 14 5949 58308 32 _ _ (2194699 / 100000) (1097351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400012032 :
    ThetaLowerSegment 3400012032 3400143104 (169995694988239 / 50000) (68000937536391 / 20000) := by
  exact
    packedTile65536 3400012032 3400143104 14 6059 58309 32 _ _ (2194703 / 100000) (1097353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400143104 :
    ThetaLowerSegment 3400143104 3400274176 (68000937536391 / 20000)
      (340017785693331 / 100000) := by
  exact
    packedTile65536 3400143104 3400274176 14 5968 58310 32 _ _ (2194707 / 100000) (219471 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400274176 :
    ThetaLowerSegment 3400274176 3400405248 (340017785693331 / 100000)
      (170015482466443 / 50000) := by
  exact
    packedTile65536 3400274176 3400405248 14 6005 58311 32 _ _ (2194711 / 100000) (1097357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400405248 :
    ThetaLowerSegment 3400405248 3400536320 (170015482466443 / 50000)
      (340044157364751 / 100000) := by
  exact
    packedTile65536 3400405248 3400536320 14 6011 58312 32 _ _ (438943 / 20000) (1097359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400536320 :
    ThetaLowerSegment 3400536320 3400667392 (340044157364751 / 100000)
      (340057312504443 / 100000) := by
  exact
    packedTile65536 3400536320 3400667392 14 5994 58314 32 _ _ (1097359 / 50000) (2194721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400667392 :
    ThetaLowerSegment 3400667392 3400798464 (340057312504443 / 100000)
      (340070388658119 / 100000) := by
  exact
    packedTile65536 3400667392 3400798464 14 5958 58315 32 _ _ (1097361 / 50000) (87789 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400798464 :
    ThetaLowerSegment 3400798464 3400929536 (340070388658119 / 100000)
      (340083488977613 / 100000) := by
  exact
    packedTile65536 3400798464 3400929536 14 5969 58316 32 _ _ (1097363 / 50000) (2194729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400929536 :
    ThetaLowerSegment 3400929536 3401060608 (340083488977613 / 100000)
      (340096536647463 / 100000) := by
  exact
    packedTile65536 3400929536 3401060608 14 5945 58317 32 _ _ (219473 / 10000) (2194733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401060608 :
    ThetaLowerSegment 3401060608 3401191680 (340096536647463 / 100000)
      (68021922574527 / 20000) := by
  exact
    packedTile65536 3401060608 3401191680 14 5958 58318 32 _ _ (1097367 / 50000) (2194737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401191680 :
    ThetaLowerSegment 3401191680 3401322752 (68021922574527 / 20000) (68024551870651 / 20000) := by
  exact
    packedTile65536 3401191680 3401322752 14 5990 58319 32 _ _ (1097369 / 50000) (2194741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401322752 :
    ThetaLowerSegment 3401322752 3401339136 (68024551870651 / 20000)
      (340124392241303 / 100000) := by
  exact
    packedTile65536 3401322752 3401339136 11 744 58320 32 _ _ (1097371 / 50000) (438949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3401339136 :
    ThetaLowerSegment 3401339136 3401341184 (340124392241303 / 100000)
      (340124585378599 / 100000) := by
  exact
    packedTile65536 3401339136 3401341184 8 88 58321 32 _ _ (1097371 / 50000) (438949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3369341184_3401341184 :
    ThetaLowerSegment 3369341184 3401341184 (168462259715851 / 50000)
      (340124585378599 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3369341184 cell3369472256)
                  (ThetaLowerSegment.join cell3369603328 cell3369734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3369865472 cell3369996544)
                  (ThetaLowerSegment.join cell3370127616 cell3370258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3370389760 cell3370520832)
                  (ThetaLowerSegment.join cell3370651904 cell3370782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3370914048 cell3371045120)
                  (ThetaLowerSegment.join cell3371176192 cell3371307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3371438336 cell3371569408)
                  (ThetaLowerSegment.join cell3371700480 cell3371831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3371962624 cell3372093696)
                  (ThetaLowerSegment.join cell3372224768 cell3372355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3372486912 cell3372617984)
                  (ThetaLowerSegment.join cell3372749056 cell3372880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3373011200 cell3373142272)
                  (ThetaLowerSegment.join cell3373273344 cell3373404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3373535488 cell3373666560)
                  (ThetaLowerSegment.join cell3373797632 cell3373928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3374059776 cell3374190848)
                  (ThetaLowerSegment.join cell3374321920 cell3374452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3374584064 cell3374715136)
                  (ThetaLowerSegment.join cell3374846208 cell3374977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3375108352 cell3375239424)
                  (ThetaLowerSegment.join cell3375370496 cell3375501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3375632640 cell3375763712)
                  (ThetaLowerSegment.join cell3375894784 cell3376025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3376156928 cell3376288000)
                  (ThetaLowerSegment.join cell3376419072 cell3376550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3376681216 cell3376812288)
                  (ThetaLowerSegment.join cell3376943360 cell3377074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3377205504 cell3377336576)
                  (ThetaLowerSegment.join cell3377467648 cell3377598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3377729792 cell3377860864)
                  (ThetaLowerSegment.join cell3377991936 cell3378123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3378254080 cell3378385152)
                  (ThetaLowerSegment.join cell3378516224 cell3378647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3378778368 cell3378909440)
                  (ThetaLowerSegment.join cell3379040512 cell3379171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3379302656 cell3379433728)
                  (ThetaLowerSegment.join cell3379564800 cell3379695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3379826944 cell3379958016)
                  (ThetaLowerSegment.join cell3380089088 cell3380220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3380351232 cell3380482304)
                  (ThetaLowerSegment.join cell3380613376 cell3380744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3380875520 cell3381006592)
                  (ThetaLowerSegment.join cell3381137664 cell3381268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3381399808 cell3381530880)
                  (ThetaLowerSegment.join cell3381661952 cell3381793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3381924096 cell3382055168)
                  (ThetaLowerSegment.join cell3382186240 cell3382317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3382448384 cell3382579456)
                  (ThetaLowerSegment.join cell3382710528 cell3382841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3382972672 cell3383103744)
                  (ThetaLowerSegment.join cell3383234816 cell3383365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3383496960 cell3383628032)
                  (ThetaLowerSegment.join cell3383759104 cell3383890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3384021248 cell3384152320)
                  (ThetaLowerSegment.join cell3384283392 cell3384414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3384545536 cell3384676608)
                  (ThetaLowerSegment.join cell3384807680 cell3384938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3385069824 cell3385200896)
                  (ThetaLowerSegment.join cell3385331968 cell3385463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3385594112 cell3385725184)
                  (ThetaLowerSegment.join cell3385856256 cell3385987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3386118400 cell3386249472)
                  (ThetaLowerSegment.join cell3386380544 cell3386511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3386642688 cell3386773760)
                  (ThetaLowerSegment.join cell3386904832 cell3387035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3387166976 cell3387298048)
                  (ThetaLowerSegment.join cell3387429120 cell3387560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3387691264 cell3387822336)
                  (ThetaLowerSegment.join cell3387953408 cell3388084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3388215552 cell3388346624)
                  (ThetaLowerSegment.join cell3388477696 cell3388608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3388739840 cell3388870912)
                  (ThetaLowerSegment.join cell3389001984 cell3389133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3389264128 cell3389395200)
                  (ThetaLowerSegment.join cell3389526272 cell3389657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3389788416 cell3389919488)
                  (ThetaLowerSegment.join cell3390050560 cell3390181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3390312704 cell3390443776)
                  (ThetaLowerSegment.join cell3390574848 cell3390705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3390836992 cell3390968064)
                  (ThetaLowerSegment.join cell3391099136 cell3391230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3391361280 cell3391492352)
                  (ThetaLowerSegment.join cell3391623424 cell3391754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3391885568 cell3392016640)
                  (ThetaLowerSegment.join cell3392147712 cell3392278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3392409856 cell3392540928)
                  (ThetaLowerSegment.join cell3392672000 cell3392803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3392934144 cell3393065216)
                  (ThetaLowerSegment.join cell3393196288 cell3393327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3393458432 cell3393589504)
                  (ThetaLowerSegment.join cell3393720576 cell3393851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3393982720 cell3394113792)
                  (ThetaLowerSegment.join cell3394244864 cell3394375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3394507008 cell3394638080)
                  (ThetaLowerSegment.join cell3394769152 cell3394900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3395031296 cell3395162368)
                  (ThetaLowerSegment.join cell3395293440 cell3395424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3395555584 cell3395686656)
                  (ThetaLowerSegment.join cell3395817728 cell3395948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3396079872 cell3396210944)
                  (ThetaLowerSegment.join cell3396342016 cell3396473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3396604160 cell3396735232)
                  (ThetaLowerSegment.join cell3396866304 cell3396997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3397128448 cell3397259520)
                  (ThetaLowerSegment.join cell3397390592 cell3397521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3397652736 cell3397783808)
                  (ThetaLowerSegment.join cell3397914880 cell3398045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3398177024 cell3398308096)
                  (ThetaLowerSegment.join cell3398439168 cell3398570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3398701312 cell3398832384)
                  (ThetaLowerSegment.join cell3398963456 cell3399094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3399225600 cell3399356672)
                  (ThetaLowerSegment.join cell3399487744 cell3399618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3399749888 cell3399880960)
                  (ThetaLowerSegment.join cell3400012032 cell3400143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3400274176 cell3400405248)
                  (ThetaLowerSegment.join cell3400536320 cell3400667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3400798464 cell3400929536)
                (ThetaLowerSegment.join cell3401060608 cell3401191680))
              (ThetaLowerSegment.join cell3401322752 cell3401339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
