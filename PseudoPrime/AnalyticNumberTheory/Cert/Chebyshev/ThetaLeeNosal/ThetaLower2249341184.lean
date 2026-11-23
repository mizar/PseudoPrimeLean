/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2249341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2217341184 :
    ThetaLowerSegment 2217341184 2217472256 (221727109576867 / 100000)
      (44348070112427 / 20000) := by
  exact
    packedTile65536 2217341184 2217472256 14 6153 47088 31 _ _ (537989 / 25000) (2151959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217472256 :
    ThetaLowerSegment 2217472256 2217603328 (44348070112427 / 20000)
      (221753451706791 / 100000) := by
  exact
    packedTile65536 2217472256 2217603328 14 6088 47090 31 _ _ (1075981 / 50000) (430393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217603328 :
    ThetaLowerSegment 2217603328 2217734400 (221753451706791 / 100000)
      (221766290347879 / 100000) := by
  exact
    packedTile65536 2217603328 2217734400 14 5966 47091 31 _ _ (67249 / 3125) (2151971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217734400 :
    ThetaLowerSegment 2217734400 2217865472 (221766290347879 / 100000)
      (221779484100473 / 100000) := by
  exact
    packedTile65536 2217734400 2217865472 14 6131 47092 31 _ _ (1075987 / 50000) (2151977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217865472 :
    ThetaLowerSegment 2217865472 2217996544 (221779484100473 / 100000)
      (221792406740373 / 100000) := by
  exact
    packedTile65536 2217865472 2217996544 14 6005 47094 31 _ _ (107599 / 5000) (2151983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217996544 :
    ThetaLowerSegment 2217996544 2218127616 (221792406740373 / 100000)
      (44361111935761 / 20000) := by
  exact
    packedTile65536 2217996544 2218127616 14 6112 47095 31 _ _ (1075993 / 50000) (2151989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2218127616 :
    ThetaLowerSegment 2218127616 2218258688 (44361111935761 / 20000)
      (221818678215941 / 100000) := by
  exact
    packedTile65536 2218127616 2218258688 14 6096 47097 31 _ _ (2151991 / 100000) (1075997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2218258688 :
    ThetaLowerSegment 2218258688 2218389760 (221818678215941 / 100000) (5545796587539 / 2500) := by
  exact
    packedTile65536 2218258688 2218389760 14 6127 47098 31 _ _ (2151997 / 100000) (538 / 25)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2218389760 :
    ThetaLowerSegment 2218389760 2218520832 (5545796587539 / 2500) (27730614155969 / 12500) := by
  exact
    packedTile65536 2218389760 2218520832 14 6064 47099 31 _ _ (2152003 / 100000) (1076003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2218520832 :
    ThetaLowerSegment 2218520832 2218651904 (27730614155969 / 12500)
      (221857930750193 / 100000) := by
  exact
    packedTile65536 2218520832 2218651904 14 6049 47101 31 _ _ (2152009 / 100000) (538003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2218651904 :
    ThetaLowerSegment 2218651904 2218782976 (221857930750193 / 100000)
      (110935515032749 / 50000) := by
  exact
    packedTile65536 2218651904 2218782976 14 6087 47102 31 _ _ (430403 / 20000) (1076009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2218782976 :
    ThetaLowerSegment 2218782976 2218914048 (110935515032749 / 50000)
      (110942117433177 / 50000) := by
  exact
    packedTile65536 2218782976 2218914048 14 6136 47103 31 _ _ (2152021 / 100000) (269003 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2218914048 :
    ThetaLowerSegment 2218914048 2219045120 (110942117433177 / 50000) (27737165436821 / 12500) := by
  exact
    packedTile65536 2218914048 2219045120 14 6082 47105 31 _ _ (2152027 / 100000) (215203 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2219045120 :
    ThetaLowerSegment 2219045120 2219176192 (27737165436821 / 12500) (110955227599967 / 50000) := by
  exact
    packedTile65536 2219045120 2219176192 14 6102 47106 31 _ _ (2152033 / 100000) (538009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2219176192 :
    ThetaLowerSegment 2219176192 2219307264 (110955227599967 / 50000)
      (221923726824447 / 100000) := by
  exact
    packedTile65536 2219176192 2219307264 14 6167 47108 31 _ _ (2152039 / 100000) (1076021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2219307264 :
    ThetaLowerSegment 2219307264 2219438336 (221923726824447 / 100000)
      (55484224872973 / 25000) := by
  exact
    packedTile65536 2219307264 2219438336 14 6121 47109 31 _ _ (430409 / 20000) (134503 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2219438336 :
    ThetaLowerSegment 2219438336 2219569408 (55484224872973 / 25000) (27743752836599 / 12500) := by
  exact
    packedTile65536 2219438336 2219569408 14 6098 47110 31 _ _ (43041 / 2000) (2152053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2219569408 :
    ThetaLowerSegment 2219569408 2219700480 (27743752836599 / 12500) (6936344073461 / 3125) := by
  exact
    packedTile65536 2219569408 2219700480 14 6035 47112 31 _ _ (269007 / 12500) (2152059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2219700480 :
    ThetaLowerSegment 2219700480 2219831552 (6936344073461 / 3125) (110988087257003 / 50000) := by
  exact
    packedTile65536 2219700480 2219831552 14 6117 47113 31 _ _ (1076031 / 50000) (430413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2219831552 :
    ThetaLowerSegment 2219831552 2219962624 (110988087257003 / 50000)
      (110994661824743 / 50000) := by
  exact
    packedTile65536 2219831552 2219962624 14 6110 47115 31 _ _ (538017 / 25000) (2152071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2219962624 :
    ThetaLowerSegment 2219962624 2220093696 (110994661824743 / 50000)
      (111001245019109 / 50000) := by
  exact
    packedTile65536 2219962624 2220093696 14 6118 47116 31 _ _ (1076037 / 50000) (2152077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2220093696 :
    ThetaLowerSegment 2220093696 2220224768 (111001245019109 / 50000)
      (111007803482909 / 50000) := by
  exact
    packedTile65536 2220093696 2220224768 14 6095 47117 31 _ _ (26901 / 1250) (2152083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2220224768 :
    ThetaLowerSegment 2220224768 2220355840 (111007803482909 / 50000) (6938397219296 / 3125) := by
  exact
    packedTile65536 2220224768 2220355840 14 6089 47119 31 _ _ (1076043 / 50000) (2152089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2220355840 :
    ThetaLowerSegment 2220355840 2220486912 (6938397219296 / 3125) (55510501122439 / 25000) := by
  exact
    packedTile65536 2220355840 2220486912 14 6177 47120 31 _ _ (538023 / 25000) (430419 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2220486912 :
    ThetaLowerSegment 2220486912 2220617984 (55510501122439 / 25000) (55513804592869 / 25000) := by
  exact
    packedTile65536 2220486912 2220617984 14 6140 47122 31 _ _ (1076049 / 50000) (2152101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2220617984 :
    ThetaLowerSegment 2220617984 2220749056 (55513804592869 / 25000) (55517053731883 / 25000) := by
  exact
    packedTile65536 2220617984 2220749056 14 6039 47123 31 _ _ (269013 / 12500) (2152107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2220749056 :
    ThetaLowerSegment 2220749056 2220880128 (55517053731883 / 25000) (55520322786973 / 25000) := by
  exact
    packedTile65536 2220749056 2220880128 14 6076 47124 31 _ _ (215211 / 10000) (2152113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2220880128 :
    ThetaLowerSegment 2220880128 2221011200 (55520322786973 / 25000) (55523559567933 / 25000) := by
  exact
    packedTile65536 2220880128 2221011200 14 6016 47126 31 _ _ (430423 / 20000) (1076059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221011200 :
    ThetaLowerSegment 2221011200 2221142272 (55523559567933 / 25000) (6940858960269 / 3125) := by
  exact
    packedTile65536 2221011200 2221142272 14 6156 47127 31 _ _ (2152121 / 100000) (538031 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221142272 :
    ThetaLowerSegment 2221142272 2221273344 (6940858960269 / 3125) (55530110633287 / 25000) := by
  exact
    packedTile65536 2221142272 2221273344 14 6020 47128 31 _ _ (2152127 / 100000) (215213 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221273344 :
    ThetaLowerSegment 2221273344 2221404416 (55530110633287 / 25000) (111066834771283 / 50000) := by
  exact
    packedTile65536 2221273344 2221404416 14 6146 47130 31 _ _ (2152133 / 100000) (269017 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221404416 :
    ThetaLowerSegment 2221404416 2221535488 (111066834771283 / 50000)
      (111073407403789 / 50000) := by
  exact
    packedTile65536 2221404416 2221535488 14 6108 47131 31 _ _ (2152139 / 100000) (1076071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221535488 :
    ThetaLowerSegment 2221535488 2221666560 (111073407403789 / 50000)
      (222159889088453 / 100000) := by
  exact
    packedTile65536 2221535488 2221666560 14 6075 47133 31 _ _ (430429 / 20000) (538037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221666560 :
    ThetaLowerSegment 2221666560 2221797632 (222159889088453 / 100000)
      (222173025818157 / 100000) := by
  exact
    packedTile65536 2221666560 2221797632 14 6104 47134 31 _ _ (2152151 / 100000) (1076077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221797632 :
    ThetaLowerSegment 2221797632 2221928704 (222173025818157 / 100000)
      (222186046368007 / 100000) := by
  exact
    packedTile65536 2221797632 2221928704 14 6050 47135 31 _ _ (2152157 / 100000) (13451 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221928704 :
    ThetaLowerSegment 2221928704 2222059776 (222186046368007 / 100000)
      (222199234822871 / 100000) := by
  exact
    packedTile65536 2221928704 2222059776 14 6128 47137 31 _ _ (2152163 / 100000) (1076083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2222059776 :
    ThetaLowerSegment 2222059776 2222190848 (222199234822871 / 100000)
      (222212307097377 / 100000) := by
  exact
    packedTile65536 2222059776 2222190848 14 6074 47138 31 _ _ (2152169 / 100000) (538043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2222190848 :
    ThetaLowerSegment 2222190848 2222321920 (222212307097377 / 100000)
      (222225329902251 / 100000) := by
  exact
    packedTile65536 2222190848 2222321920 14 6051 47140 31 _ _ (1076087 / 50000) (2152177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2222321920 :
    ThetaLowerSegment 2222321920 2222452992 (222225329902251 / 100000)
      (222238378569591 / 100000) := by
  exact
    packedTile65536 2222321920 2222452992 14 6063 47141 31 _ _ (107609 / 5000) (2152183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2222452992 :
    ThetaLowerSegment 2222452992 2222584064 (222238378569591 / 100000)
      (222251541339167 / 100000) := by
  exact
    packedTile65536 2222452992 2222584064 14 6116 47142 31 _ _ (1076093 / 50000) (2152189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2222584064 :
    ThetaLowerSegment 2222584064 2222715136 (222251541339167 / 100000)
      (222264587927071 / 100000) := by
  exact
    packedTile65536 2222584064 2222715136 14 6062 47144 31 _ _ (67256 / 3125) (430439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2222715136 :
    ThetaLowerSegment 2222715136 2222846208 (222264587927071 / 100000)
      (44455538101699 / 20000) := by
  exact
    packedTile65536 2222715136 2222846208 14 6088 47145 31 _ _ (1076099 / 50000) (2152201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2222846208 :
    ThetaLowerSegment 2222846208 2222977280 (44455538101699 / 20000)
      (222290821105099 / 100000) := by
  exact
    packedTile65536 2222846208 2222977280 14 6101 47147 31 _ _ (538051 / 25000) (2152207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2222977280 :
    ThetaLowerSegment 2222977280 2223108352 (222290821105099 / 100000)
      (222303869954329 / 100000) := by
  exact
    packedTile65536 2222977280 2223108352 14 6063 47148 31 _ _ (215221 / 10000) (2152213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2223108352 :
    ThetaLowerSegment 2223108352 2223239424 (222303869954329 / 100000)
      (222316951123177 / 100000) := by
  exact
    packedTile65536 2223108352 2223239424 14 6078 47149 31 _ _ (269027 / 12500) (2152219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2223239424 :
    ThetaLowerSegment 2223239424 2223370496 (222316951123177 / 100000)
      (222329903195173 / 100000) := by
  exact
    packedTile65536 2223239424 2223370496 14 6018 47151 31 _ _ (1076111 / 50000) (86089 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2223370496 :
    ThetaLowerSegment 2223370496 2223501568 (222329903195173 / 100000)
      (222343049003797 / 100000) := by
  exact
    packedTile65536 2223370496 2223501568 14 6108 47152 31 _ _ (538057 / 25000) (2152231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2223501568 :
    ThetaLowerSegment 2223501568 2223632640 (222343049003797 / 100000)
      (111178038235073 / 50000) := by
  exact
    packedTile65536 2223501568 2223632640 14 6053 47154 31 _ _ (2152233 / 100000) (538059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2223632640 :
    ThetaLowerSegment 2223632640 2223763712 (111178038235073 / 50000) (55592289444697 / 25000) := by
  exact
    packedTile65536 2223632640 2223763712 14 6078 47155 31 _ _ (2152239 / 100000) (1076121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2223763712 :
    ThetaLowerSegment 2223763712 2223894784 (55592289444697 / 25000)
      (222382305843493 / 100000) := by
  exact
    packedTile65536 2223763712 2223894784 14 6109 47156 31 _ _ (430449 / 20000) (269031 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2223894784 :
    ThetaLowerSegment 2223894784 2224025856 (222382305843493 / 100000)
      (111197621512127 / 50000) := by
  exact
    packedTile65536 2223894784 2224025856 14 6011 47158 31 _ _ (2152251 / 100000) (1076127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2224025856 :
    ThetaLowerSegment 2224025856 2224156928 (111197621512127 / 50000) (22240834596487 / 10000) := by
  exact
    packedTile65536 2224025856 2224156928 14 6088 47159 31 _ _ (2152257 / 100000) (107613 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2224156928 :
    ThetaLowerSegment 2224156928 2224288000 (22240834596487 / 10000)
      (222421455398803 / 100000) := by
  exact
    packedTile65536 2224156928 2224288000 14 6091 47160 31 _ _ (2152263 / 100000) (1076133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2224288000 :
    ThetaLowerSegment 2224288000 2224419072 (222421455398803 / 100000)
      (111217308261869 / 50000) := by
  exact
    packedTile65536 2224288000 2224419072 14 6115 47162 31 _ _ (2152269 / 100000) (134517 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2224419072 :
    ThetaLowerSegment 2224419072 2224550144 (111217308261869 / 50000)
      (222447756162613 / 100000) := by
  exact
    packedTile65536 2224419072 2224550144 14 6105 47163 31 _ _ (86091 / 4000) (1076139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2224550144 :
    ThetaLowerSegment 2224550144 2224681216 (222447756162613 / 100000)
      (222460626802993 / 100000) := by
  exact
    packedTile65536 2224550144 2224681216 14 5980 47165 31 _ _ (2152281 / 100000) (538071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2224681216 :
    ThetaLowerSegment 2224681216 2224812288 (222460626802993 / 100000)
      (222473725615589 / 100000) := by
  exact
    packedTile65536 2224681216 2224812288 14 6086 47166 31 _ _ (1076143 / 50000) (2152289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2224812288 :
    ThetaLowerSegment 2224812288 2224943360 (222473725615589 / 100000)
      (222486949297637 / 100000) := by
  exact
    packedTile65536 2224812288 2224943360 14 6144 47167 31 _ _ (538073 / 25000) (430459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2224943360 :
    ThetaLowerSegment 2224943360 2225074432 (222486949297637 / 100000)
      (222500089076927 / 100000) := by
  exact
    packedTile65536 2224943360 2225074432 14 6105 47169 31 _ _ (1076149 / 50000) (2152301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225074432 :
    ThetaLowerSegment 2225074432 2225205504 (222500089076927 / 100000)
      (222513403229471 / 100000) := by
  exact
    packedTile65536 2225074432 2225205504 14 6186 47170 31 _ _ (134519 / 6250) (2152307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225205504 :
    ThetaLowerSegment 2225205504 2225336576 (222513403229471 / 100000)
      (222526497883511 / 100000) := by
  exact
    packedTile65536 2225205504 2225336576 14 6084 47172 31 _ _ (215231 / 10000) (2152313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225336576 :
    ThetaLowerSegment 2225336576 2225467648 (222526497883511 / 100000)
      (222539648534271 / 100000) := by
  exact
    packedTile65536 2225336576 2225467648 14 6110 47173 31 _ _ (538079 / 25000) (2152319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225467648 :
    ThetaLowerSegment 2225467648 2225598720 (222539648534271 / 100000)
      (222552730347387 / 100000) := by
  exact
    packedTile65536 2225467648 2225598720 14 6078 47174 31 _ _ (1076161 / 50000) (86093 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225598720 :
    ThetaLowerSegment 2225598720 2225729792 (222552730347387 / 100000)
      (44513142207511 / 20000) := by
  exact
    packedTile65536 2225598720 2225729792 14 6031 47176 31 _ _ (269041 / 12500) (2152331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225729792 :
    ThetaLowerSegment 2225729792 2225860864 (44513142207511 / 20000)
      (222578734810589 / 100000) := by
  exact
    packedTile65536 2225729792 2225860864 14 6051 47177 31 _ _ (1076167 / 50000) (2152337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225860864 :
    ThetaLowerSegment 2225860864 2225991936 (222578734810589 / 100000)
      (44518391756281 / 20000) := by
  exact
    packedTile65536 2225860864 2225991936 14 6144 47179 31 _ _ (2152339 / 100000) (1076171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225991936 :
    ThetaLowerSegment 2225991936 2226123008 (44518391756281 / 20000) (44520976292157 / 20000) := by
  exact
    packedTile65536 2225991936 2226123008 14 6004 47180 31 _ _ (430469 / 20000) (538087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2226123008 :
    ThetaLowerSegment 2226123008 2226254080 (44520976292157 / 20000)
      (222618006497183 / 100000) := by
  exact
    packedTile65536 2226123008 2226254080 14 6098 47181 31 _ _ (2152351 / 100000) (1076177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2226254080 :
    ThetaLowerSegment 2226254080 2226385152 (222618006497183 / 100000)
      (55657790963881 / 25000) := by
  exact
    packedTile65536 2226254080 2226385152 14 6113 47183 31 _ _ (2152357 / 100000) (53809 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2226385152 :
    ThetaLowerSegment 2226385152 2226516224 (55657790963881 / 25000) (22264425452729 / 10000) := by
  exact
    packedTile65536 2226385152 2226516224 14 6082 47184 31 _ _ (2152363 / 100000) (1076183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2226516224 :
    ThetaLowerSegment 2226516224 2226647296 (22264425452729 / 10000) (8906296650549 / 4000) := by
  exact
    packedTile65536 2226516224 2226647296 14 6115 47185 31 _ _ (2152369 / 100000) (538093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2226647296 :
    ThetaLowerSegment 2226647296 2226778368 (8906296650549 / 4000) (2226706598271 / 1000) := by
  exact
    packedTile65536 2226647296 2226778368 14 6153 47187 31 _ _ (17219 / 800) (1076189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2226778368 :
    ThetaLowerSegment 2226778368 2226909440 (2226706598271 / 1000) (27835471516519 / 12500) := by
  exact
    packedTile65536 2226778368 2226909440 14 6092 47188 31 _ _ (2152381 / 100000) (67262 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2226909440 :
    ThetaLowerSegment 2226909440 2227040512 (27835471516519 / 12500)
      (222696908150013 / 100000) := by
  exact
    packedTile65536 2226909440 2227040512 14 6103 47190 31 _ _ (2152387 / 100000) (215239 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2227040512 :
    ThetaLowerSegment 2227040512 2227171584 (222696908150013 / 100000)
      (222709794520917 / 100000) := by
  exact
    packedTile65536 2227040512 2227171584 14 5987 47191 31 _ _ (269049 / 12500) (430479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2227171584 :
    ThetaLowerSegment 2227171584 2227302656 (222709794520917 / 100000)
      (222722919843921 / 100000) := by
  exact
    packedTile65536 2227171584 2227302656 14 6098 47192 31 _ _ (1076199 / 50000) (2152401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2227302656 :
    ThetaLowerSegment 2227302656 2227433728 (222722919843921 / 100000)
      (222735961259757 / 100000) := by
  exact
    packedTile65536 2227302656 2227433728 14 6059 47194 31 _ _ (538101 / 25000) (2152407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2227433728 :
    ThetaLowerSegment 2227433728 2227564800 (222735961259757 / 100000)
      (222749284677657 / 100000) := by
  exact
    packedTile65536 2227433728 2227564800 14 6190 47195 31 _ _ (215241 / 10000) (2152413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2227564800 :
    ThetaLowerSegment 2227564800 2227695872 (222749284677657 / 100000)
      (222762311099289 / 100000) := by
  exact
    packedTile65536 2227564800 2227695872 14 6052 47197 31 _ _ (67263 / 3125) (2152419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2227695872 :
    ThetaLowerSegment 2227695872 2227826944 (222762311099289 / 100000)
      (222775567866387 / 100000) := by
  exact
    packedTile65536 2227695872 2227826944 14 6159 47198 31 _ _ (1076211 / 50000) (86097 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2227826944 :
    ThetaLowerSegment 2227826944 2227958016 (222775567866387 / 100000)
      (222788684762619 / 100000) := by
  exact
    packedTile65536 2227826944 2227958016 14 6094 47199 31 _ _ (538107 / 25000) (2152431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2227958016 :
    ThetaLowerSegment 2227958016 2228089088 (222788684762619 / 100000)
      (222801752189433 / 100000) := by
  exact
    packedTile65536 2227958016 2228089088 14 6071 47201 31 _ _ (1076217 / 50000) (2152437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2228089088 :
    ThetaLowerSegment 2228089088 2228220160 (222801752189433 / 100000)
      (222814735707513 / 100000) := by
  exact
    packedTile65536 2228089088 2228220160 14 6032 47202 31 _ _ (53811 / 2500) (2152443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2228220160 :
    ThetaLowerSegment 2228220160 2228351232 (222814735707513 / 100000)
      (222827930195363 / 100000) := by
  exact
    packedTile65536 2228220160 2228351232 14 6130 47204 31 _ _ (430489 / 20000) (67264 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2228351232 :
    ThetaLowerSegment 2228351232 2228482304 (222827930195363 / 100000)
      (111420539759261 / 50000) := by
  exact
    packedTile65536 2228351232 2228482304 14 6109 47205 31 _ _ (2152451 / 100000) (1076227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2228482304 :
    ThetaLowerSegment 2228482304 2228613376 (111420539759261 / 50000)
      (222854060986689 / 100000) := by
  exact
    packedTile65536 2228482304 2228613376 14 6031 47206 31 _ _ (2152457 / 100000) (107623 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2228613376 :
    ThetaLowerSegment 2228613376 2228744448 (222854060986689 / 100000)
      (111433577209559 / 50000) := by
  exact
    packedTile65536 2228613376 2228744448 14 6083 47208 31 _ _ (2152463 / 100000) (1076233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2228744448 :
    ThetaLowerSegment 2228744448 2228875520 (111433577209559 / 50000) (4457606894983 / 2000) := by
  exact
    packedTile65536 2228744448 2228875520 14 6128 47209 31 _ _ (2152469 / 100000) (269059 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2228875520 :
    ThetaLowerSegment 2228875520 2229006592 (4457606894983 / 2000) (8915736152599 / 4000) := by
  exact
    packedTile65536 2228875520 2229006592 14 6067 47210 31 _ _ (86099 / 4000) (1076239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229006592 :
    ThetaLowerSegment 2229006592 2229137664 (8915736152599 / 4000) (222906482289531 / 100000) := by
  exact
    packedTile65536 2229006592 2229137664 14 6076 47212 31 _ _ (2152481 / 100000) (538121 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229137664 :
    ThetaLowerSegment 2229137664 2229268736 (222906482289531 / 100000)
      (222919707169659 / 100000) := by
  exact
    packedTile65536 2229137664 2229268736 14 6144 47213 31 _ _ (2152487 / 100000) (215249 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229268736 :
    ThetaLowerSegment 2229268736 2229399808 (222919707169659 / 100000)
      (44586629035443 / 20000) := by
  exact
    packedTile65536 2229268736 2229399808 14 6243 47215 31 _ _ (538123 / 25000) (430499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229399808 :
    ThetaLowerSegment 2229399808 2229530880 (44586629035443 / 20000)
      (222946288330003 / 100000) := by
  exact
    packedTile65536 2229399808 2229530880 14 6106 47216 31 _ _ (1076249 / 50000) (2152501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229530880 :
    ThetaLowerSegment 2229530880 2229661952 (222946288330003 / 100000)
      (222959429366923 / 100000) := by
  exact
    packedTile65536 2229530880 2229661952 14 6105 47217 31 _ _ (269063 / 12500) (2152507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229661952 :
    ThetaLowerSegment 2229661952 2229793024 (222959429366923 / 100000)
      (222972533847803 / 100000) := by
  exact
    packedTile65536 2229661952 2229793024 14 6088 47219 31 _ _ (215251 / 10000) (2152513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229793024 :
    ThetaLowerSegment 2229793024 2229924096 (222972533847803 / 100000)
      (222985515671799 / 100000) := by
  exact
    packedTile65536 2229793024 2229924096 14 6031 47220 31 _ _ (538129 / 25000) (2152519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229924096 :
    ThetaLowerSegment 2229924096 2230055168 (222985515671799 / 100000) (8919946531047 / 4000) := by
  exact
    packedTile65536 2229924096 2230055168 14 6108 47222 31 _ _ (1076261 / 50000) (86101 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2230055168 :
    ThetaLowerSegment 2230055168 2230186240 (8919946531047 / 4000) (223011701138271 / 100000) := by
  exact
    packedTile65536 2230055168 2230186240 14 6057 47223 31 _ _ (134533 / 6250) (2152531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2230186240 :
    ThetaLowerSegment 2230186240 2230317312 (223011701138271 / 100000)
      (223024751951913 / 100000) := by
  exact
    packedTile65536 2230186240 2230317312 14 6063 47224 31 _ _ (1076267 / 50000) (2152537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2230317312 :
    ThetaLowerSegment 2230317312 2230448384 (223024751951913 / 100000)
      (223037869524579 / 100000) := by
  exact
    packedTile65536 2230317312 2230448384 14 6094 47226 31 _ _ (2152539 / 100000) (1076271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2230448384 :
    ThetaLowerSegment 2230448384 2230579456 (223037869524579 / 100000)
      (223050922557459 / 100000) := by
  exact
    packedTile65536 2230448384 2230579456 14 6064 47227 31 _ _ (430509 / 20000) (538137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2230579456 :
    ThetaLowerSegment 2230579456 2230710528 (223050922557459 / 100000) (4461282827463 / 2000) := by
  exact
    packedTile65536 2230579456 2230710528 14 6141 47229 31 _ _ (2152551 / 100000) (1076277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2230710528 :
    ThetaLowerSegment 2230710528 2230841600 (4461282827463 / 2000) (223077243987609 / 100000) := by
  exact
    packedTile65536 2230710528 2230841600 14 6087 47230 31 _ _ (2152557 / 100000) (26907 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2230841600 :
    ThetaLowerSegment 2230841600 2230972672 (223077243987609 / 100000)
      (22309051884363 / 10000) := by
  exact
    packedTile65536 2230841600 2230972672 14 6167 47231 31 _ _ (2152563 / 100000) (1076283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2230972672 :
    ThetaLowerSegment 2230972672 2231103744 (22309051884363 / 10000) (55775887624089 / 25000) := by
  exact
    packedTile65536 2230972672 2231103744 14 6054 47233 31 _ _ (2152569 / 100000) (538143 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2231103744 :
    ThetaLowerSegment 2231103744 2231234816 (55775887624089 / 25000)
      (223116679051281 / 100000) := by
  exact
    packedTile65536 2231103744 2231234816 14 6099 47234 31 _ _ (86103 / 4000) (1076289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2231234816 :
    ThetaLowerSegment 2231234816 2231365888 (223116679051281 / 100000)
      (223129650504387 / 100000) := by
  exact
    packedTile65536 2231234816 2231365888 14 6026 47235 31 _ _ (2152581 / 100000) (269073 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2231365888 :
    ThetaLowerSegment 2231365888 2231496960 (223129650504387 / 100000)
      (223142725311751 / 100000) := by
  exact
    packedTile65536 2231365888 2231496960 14 6074 47237 31 _ _ (1076293 / 50000) (2152589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2231496960 :
    ThetaLowerSegment 2231496960 2231628032 (223142725311751 / 100000)
      (223155950836999 / 100000) := by
  exact
    packedTile65536 2231496960 2231628032 14 6144 47238 31 _ _ (134537 / 6250) (430519 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2231628032 :
    ThetaLowerSegment 2231628032 2231759104 (223155950836999 / 100000)
      (223169036480241 / 100000) := by
  exact
    packedTile65536 2231628032 2231759104 14 6079 47240 31 _ _ (1076299 / 50000) (2152601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2231759104 :
    ThetaLowerSegment 2231759104 2231890176 (223169036480241 / 100000)
      (44636425293033 / 20000) := by
  exact
    packedTile65536 2231759104 2231890176 14 6081 47241 31 _ _ (538151 / 25000) (2152607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2231890176 :
    ThetaLowerSegment 2231890176 2232021248 (44636425293033 / 20000) (44639044158359 / 20000) := by
  exact
    packedTile65536 2231890176 2232021248 14 6083 47242 31 _ _ (215261 / 10000) (2152613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2232021248 :
    ThetaLowerSegment 2232021248 2232152320 (44639044158359 / 20000) (44641663892031 / 20000) := by
  exact
    packedTile65536 2232021248 2232152320 14 6085 47244 31 _ _ (269077 / 12500) (2152619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2232152320 :
    ThetaLowerSegment 2232152320 2232283392 (44641663892031 / 20000)
      (223221263176241 / 100000) := by
  exact
    packedTile65536 2232152320 2232283392 14 6013 47245 31 _ _ (1076311 / 50000) (17221 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2232283392 :
    ThetaLowerSegment 2232283392 2232414464 (223221263176241 / 100000)
      (44646877980357 / 20000) := by
  exact
    packedTile65536 2232283392 2232414464 14 6098 47247 31 _ _ (538157 / 25000) (2152631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2232414464 :
    ThetaLowerSegment 2232414464 2232545536 (44646877980357 / 20000) (111623718505199 / 50000) := by
  exact
    packedTile65536 2232414464 2232545536 14 6061 47248 31 _ _ (2152633 / 100000) (538159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2232545536 :
    ThetaLowerSegment 2232545536 2232676608 (111623718505199 / 50000)
      (223260415270929 / 100000) := by
  exact
    packedTile65536 2232545536 2232676608 14 6029 47249 31 _ _ (2152639 / 100000) (1076321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2232676608 :
    ThetaLowerSegment 2232676608 2232807680 (223260415270929 / 100000)
      (223273352667379 / 100000) := by
  exact
    packedTile65536 2232676608 2232807680 14 6010 47251 31 _ _ (430529 / 20000) (269081 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2232807680 :
    ThetaLowerSegment 2232807680 2232938752 (223273352667379 / 100000)
      (22328661515019 / 10000) := by
  exact
    packedTile65536 2232807680 2232938752 14 6161 47252 31 _ _ (2152651 / 100000) (1076327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2232938752 :
    ThetaLowerSegment 2232938752 2233069824 (22328661515019 / 10000) (111649933453341 / 50000) := by
  exact
    packedTile65536 2232938752 2233069824 14 6156 47253 31 _ _ (2152657 / 100000) (107633 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2233069824 :
    ThetaLowerSegment 2233069824 2233200896 (111649933453341 / 50000)
      (223312823785279 / 100000) := by
  exact
    packedTile65536 2233069824 2233200896 14 6019 47255 31 _ _ (2152663 / 100000) (1076333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2233200896 :
    ThetaLowerSegment 2233200896 2233331968 (223312823785279 / 100000) (2233257591733 / 1000) := by
  exact
    packedTile65536 2233200896 2233331968 14 6009 47256 31 _ _ (2152669 / 100000) (67271 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2233331968 :
    ThetaLowerSegment 2233331968 2233463040 (2233257591733 / 1000) (893354993657 / 400) := by
  exact
    packedTile65536 2233331968 2233463040 14 6034 47258 31 _ _ (86107 / 4000) (1076339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2233463040 :
    ThetaLowerSegment 2233463040 2233594112 (893354993657 / 400) (22335187545689 / 10000) := by
  exact
    packedTile65536 2233463040 2233594112 14 6098 47259 31 _ _ (53817 / 2500) (2152683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2233594112 :
    ThetaLowerSegment 2233594112 2233725184 (22335187545689 / 10000) (111682410855247 / 50000) := by
  exact
    packedTile65536 2233594112 2233725184 14 6014 47260 31 _ _ (1076343 / 50000) (2152689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2233725184 :
    ThetaLowerSegment 2233725184 2233856256 (111682410855247 / 50000)
      (111689073436987 / 50000) := by
  exact
    packedTile65536 2233725184 2233856256 14 6190 47262 31 _ _ (538173 / 25000) (430539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2233856256 :
    ThetaLowerSegment 2233856256 2233987328 (111689073436987 / 50000)
      (111695697288733 / 50000) := by
  exact
    packedTile65536 2233856256 2233987328 14 6154 47263 31 _ _ (1076349 / 50000) (2152701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2233987328 :
    ThetaLowerSegment 2233987328 2234118400 (111695697288733 / 50000) (22340443135289 / 10000) := by
  exact
    packedTile65536 2233987328 2234118400 14 6056 47265 31 _ _ (67272 / 3125) (2152707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2234118400 :
    ThetaLowerSegment 2234118400 2234249472 (22340443135289 / 10000) (22341773079527 / 10000) := by
  exact
    packedTile65536 2234118400 2234249472 14 6178 47266 31 _ _ (215271 / 10000) (2152713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2234249472 :
    ThetaLowerSegment 2234249472 2234380544 (22341773079527 / 10000) (111715390279831 / 50000) := by
  exact
    packedTile65536 2234249472 2234380544 14 6062 47267 31 _ _ (538179 / 25000) (2152719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2234380544 :
    ThetaLowerSegment 2234380544 2234511616 (111715390279831 / 50000)
      (111721913024461 / 50000) := by
  exact
    packedTile65536 2234380544 2234511616 14 6060 47269 31 _ _ (2152721 / 100000) (538181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2234511616 :
    ThetaLowerSegment 2234511616 2234642688 (111721913024461 / 50000)
      (223457028723613 / 100000) := by
  exact
    packedTile65536 2234511616 2234642688 14 6133 47270 31 _ _ (2152727 / 100000) (215273 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2234642688 :
    ThetaLowerSegment 2234642688 2234773760 (223457028723613 / 100000)
      (44694042412101 / 20000) := by
  exact
    packedTile65536 2234642688 2234773760 14 6124 47272 31 _ _ (2152733 / 100000) (67273 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2234773760 :
    ThetaLowerSegment 2234773760 2234904832 (44694042412101 / 20000) (27935418240143 / 12500) := by
  exact
    packedTile65536 2234773760 2234904832 14 6101 47273 31 _ _ (2152739 / 100000) (1076371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2234904832 :
    ThetaLowerSegment 2234904832 2235035904 (27935418240143 / 12500)
      (223496410930549 / 100000) := by
  exact
    packedTile65536 2234904832 2235035904 14 6069 47274 31 _ _ (430549 / 20000) (538187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2235035904 :
    ThetaLowerSegment 2235035904 2235166976 (223496410930549 / 100000)
      (27938699566303 / 12500) := by
  exact
    packedTile65536 2235035904 2235166976 14 6125 47276 31 _ _ (2152751 / 100000) (1076377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2235166976 :
    ThetaLowerSegment 2235166976 2235298048 (27938699566303 / 12500) (2235226594599 / 1000) := by
  exact
    packedTile65536 2235166976 2235298048 14 6068 47277 31 _ _ (2152757 / 100000) (53819 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2235298048 :
    ThetaLowerSegment 2235298048 2235429120 (2235226594599 / 1000) (111767889198811 / 50000) := by
  exact
    packedTile65536 2235298048 2235429120 14 6094 47278 31 _ _ (2152763 / 100000) (1076383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2235429120 :
    ThetaLowerSegment 2235429120 2235560192 (111767889198811 / 50000)
      (111774385176251 / 50000) := by
  exact
    packedTile65536 2235429120 2235560192 14 6035 47280 31 _ _ (67274 / 3125) (2152771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2235560192 :
    ThetaLowerSegment 2235560192 2235691264 (111774385176251 / 50000)
      (111780936067533 / 50000) := by
  exact
    packedTile65536 2235560192 2235691264 14 6086 47281 31 _ _ (1076387 / 50000) (2152777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2235691264 :
    ThetaLowerSegment 2235691264 2235822336 (111780936067533 / 50000)
      (111787534338233 / 50000) := by
  exact
    packedTile65536 2235691264 2235822336 14 6130 47283 31 _ _ (107639 / 5000) (2152783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2235822336 :
    ThetaLowerSegment 2235822336 2235953408 (111787534338233 / 50000) (2235881339347 / 1000) := by
  exact
    packedTile65536 2235822336 2235953408 14 6069 47284 31 _ _ (1076393 / 50000) (2152789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2235953408 :
    ThetaLowerSegment 2235953408 2236084480 (2235881339347 / 1000) (11180067065681 / 5000) := by
  exact
    packedTile65536 2235953408 2236084480 14 6135 47285 31 _ _ (269099 / 12500) (430559 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2236084480 :
    ThetaLowerSegment 2236084480 2236215552 (11180067065681 / 5000) (55903652790123 / 25000) := by
  exact
    packedTile65536 2236084480 2236215552 14 6164 47287 31 _ _ (1076399 / 50000) (2152801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2236215552 :
    ThetaLowerSegment 2236215552 2236346624 (55903652790123 / 25000) (55906940121831 / 25000) := by
  exact
    packedTile65536 2236215552 2236346624 14 6108 47288 31 _ _ (538201 / 25000) (2152807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2236346624 :
    ThetaLowerSegment 2236346624 2236477696 (55906940121831 / 25000) (111820422630213 / 50000) := by
  exact
    packedTile65536 2236346624 2236477696 14 6078 47290 31 _ _ (2152809 / 100000) (538203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2236477696 :
    ThetaLowerSegment 2236477696 2236608768 (111820422630213 / 50000)
      (111827040383523 / 50000) := by
  exact
    packedTile65536 2236477696 2236608768 14 6148 47291 31 _ _ (430563 / 20000) (1076409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2236608768 :
    ThetaLowerSegment 2236608768 2236739840 (111827040383523 / 50000)
      (223667240961819 / 100000) := by
  exact
    packedTile65536 2236608768 2236739840 14 6113 47292 31 _ _ (2152821 / 100000) (269103 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2236739840 :
    ThetaLowerSegment 2236739840 2236870912 (223667240961819 / 100000)
      (111840187679673 / 50000) := by
  exact
    packedTile65536 2236739840 2236870912 14 6101 47294 31 _ _ (2152827 / 100000) (215283 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2236870912 :
    ThetaLowerSegment 2236870912 2237001984 (111840187679673 / 50000) (55923380139411 / 25000) := by
  exact
    packedTile65536 2236870912 2237001984 14 6106 47295 31 _ _ (2152833 / 100000) (538209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237001984 :
    ThetaLowerSegment 2237001984 2237133056 (55923380139411 / 25000) (1398166903398 / 625) := by
  exact
    packedTile65536 2237001984 2237133056 14 6124 47296 31 _ _ (2152839 / 100000) (1076421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237133056 :
    ThetaLowerSegment 2237133056 2237264128 (1398166903398 / 625) (5592996998877 / 2500) := by
  exact
    packedTile65536 2237133056 2237264128 14 6120 47298 31 _ _ (430569 / 20000) (134553 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237264128 :
    ThetaLowerSegment 2237264128 2237395200 (5592996998877 / 2500) (22373295851883 / 10000) := by
  exact
    packedTile65536 2237264128 2237395200 14 6075 47299 31 _ _ (43057 / 2000) (2152853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237395200 :
    ThetaLowerSegment 2237395200 2237526272 (22373295851883 / 10000) (22374596176907 / 10000) := by
  exact
    packedTile65536 2237395200 2237526272 14 6040 47301 31 _ _ (269107 / 12500) (2152859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237526272 :
    ThetaLowerSegment 2237526272 2237657344 (22374596176907 / 10000) (111879476069189 / 50000) := by
  exact
    packedTile65536 2237526272 2237657344 14 6034 47302 31 _ _ (1076431 / 50000) (430573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237657344 :
    ThetaLowerSegment 2237657344 2237788416 (111879476069189 / 50000) (22377196407257 / 10000) := by
  exact
    packedTile65536 2237657344 2237788416 14 6044 47303 31 _ _ (538217 / 25000) (2152871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237788416 :
    ThetaLowerSegment 2237788416 2237919488 (22377196407257 / 10000) (22378490284531 / 10000) := by
  exact
    packedTile65536 2237788416 2237919488 14 6010 47305 31 _ _ (1076437 / 50000) (2152877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237919488 :
    ThetaLowerSegment 2237919488 2238050560 (22378490284531 / 10000) (22379799666147 / 10000) := by
  exact
    packedTile65536 2237919488 2238050560 14 6082 47306 31 _ _ (26911 / 1250) (2152883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2238050560 :
    ThetaLowerSegment 2238050560 2238181632 (22379799666147 / 10000) (55952800077827 / 25000) := by
  exact
    packedTile65536 2238050560 2238181632 14 6133 47308 31 _ _ (1076443 / 50000) (2152889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2238181632 :
    ThetaLowerSegment 2238181632 2238312704 (55952800077827 / 25000) (44764848074419 / 20000) := by
  exact
    packedTile65536 2238181632 2238312704 14 6057 47309 31 _ _ (2152891 / 100000) (1076447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2238312704 :
    ThetaLowerSegment 2238312704 2238443776 (44764848074419 / 20000)
      (223837274010533 / 100000) := by
  exact
    packedTile65536 2238312704 2238443776 14 6054 47310 31 _ _ (2152897 / 100000) (21529 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2238443776 :
    ThetaLowerSegment 2238443776 2238574848 (223837274010533 / 100000)
      (111925150613293 / 50000) := by
  exact
    packedTile65536 2238443776 2238574848 14 6051 47312 31 _ _ (2152903 / 100000) (1076453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2238574848 :
    ThetaLowerSegment 2238574848 2238705920 (111925150613293 / 50000)
      (111931682539199 / 50000) := by
  exact
    packedTile65536 2238574848 2238705920 14 6068 47313 31 _ _ (2152909 / 100000) (134557 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2238705920 :
    ThetaLowerSegment 2238705920 2238836992 (111931682539199 / 50000)
      (223876521541963 / 100000) := by
  exact
    packedTile65536 2238705920 2238836992 14 6111 47314 31 _ _ (430583 / 20000) (1076459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2238836992 :
    ThetaLowerSegment 2238836992 2238968064 (223876521541963 / 100000)
      (111944873467833 / 50000) := by
  exact
    packedTile65536 2238836992 2238968064 14 6143 47316 31 _ _ (2152921 / 100000) (538231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2238968064 :
    ThetaLowerSegment 2238968064 2239099136 (111944873467833 / 50000)
      (223902950836957 / 100000) := by
  exact
    packedTile65536 2238968064 2239099136 14 6133 47317 31 _ _ (2152927 / 100000) (215293 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2239099136 :
    ThetaLowerSegment 2239099136 2239230208 (223902950836957 / 100000)
      (223915978228489 / 100000) := by
  exact
    packedTile65536 2239099136 2239230208 14 6051 47319 31 _ _ (538233 / 25000) (430587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2239230208 :
    ThetaLowerSegment 2239230208 2239361280 (223915978228489 / 100000)
      (223929294150019 / 100000) := by
  exact
    packedTile65536 2239230208 2239361280 14 6185 47320 31 _ _ (1076469 / 50000) (2152941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2239361280 :
    ThetaLowerSegment 2239361280 2239492352 (223929294150019 / 100000)
      (223942293625891 / 100000) := by
  exact
    packedTile65536 2239361280 2239492352 14 6038 47321 31 _ _ (134559 / 6250) (2152947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2239492352 :
    ThetaLowerSegment 2239492352 2239623424 (223942293625891 / 100000)
      (223955265149641 / 100000) := by
  exact
    packedTile65536 2239492352 2239623424 14 6025 47323 31 _ _ (43059 / 2000) (2152953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2239623424 :
    ThetaLowerSegment 2239623424 2239754496 (223955265149641 / 100000)
      (223968361580989 / 100000) := by
  exact
    packedTile65536 2239623424 2239754496 14 6083 47324 31 _ _ (538239 / 25000) (2152959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2239754496 :
    ThetaLowerSegment 2239754496 2239885568 (223968361580989 / 100000)
      (223981625979871 / 100000) := by
  exact
    packedTile65536 2239754496 2239885568 14 6161 47326 31 _ _ (1076481 / 50000) (430593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2239885568 :
    ThetaLowerSegment 2239885568 2240016640 (223981625979871 / 100000)
      (223994720331247 / 100000) := by
  exact
    packedTile65536 2239885568 2240016640 14 6082 47327 31 _ _ (269121 / 12500) (2152971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2240016640 :
    ThetaLowerSegment 2240016640 2240147712 (223994720331247 / 100000)
      (224007775959519 / 100000) := by
  exact
    packedTile65536 2240016640 2240147712 14 6064 47328 31 _ _ (2152973 / 100000) (134561 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2240147712 :
    ThetaLowerSegment 2240147712 2240278784 (224007775959519 / 100000)
      (224020943579083 / 100000) := by
  exact
    packedTile65536 2240147712 2240278784 14 6116 47330 31 _ _ (2152979 / 100000) (1076491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2240278784 :
    ThetaLowerSegment 2240278784 2240409856 (224020943579083 / 100000)
      (224034033727883 / 100000) := by
  exact
    packedTile65536 2240278784 2240409856 14 6080 47331 31 _ _ (430597 / 20000) (538247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2240409856 :
    ThetaLowerSegment 2240409856 2240540928 (224034033727883 / 100000)
      (224047016263613 / 100000) := by
  exact
    packedTile65536 2240409856 2240540928 14 6030 47332 31 _ _ (2152991 / 100000) (1076497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2240540928 :
    ThetaLowerSegment 2240540928 2240672000 (224047016263613 / 100000)
      (224060196911247 / 100000) := by
  exact
    packedTile65536 2240540928 2240672000 14 6122 47334 31 _ _ (2152997 / 100000) (2153 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2240672000 :
    ThetaLowerSegment 2240672000 2240803072 (224060196911247 / 100000)
      (112036571459143 / 50000) := by
  exact
    packedTile65536 2240672000 2240803072 14 6013 47335 31 _ _ (2153003 / 100000) (1076503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2240803072 :
    ThetaLowerSegment 2240803072 2240934144 (112036571459143 / 50000)
      (224086312874339 / 100000) := by
  exact
    packedTile65536 2240803072 2240934144 14 6117 47337 31 _ _ (2153009 / 100000) (538253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2240934144 :
    ThetaLowerSegment 2240934144 2241065216 (224086312874339 / 100000)
      (224099459177823 / 100000) := by
  exact
    packedTile65536 2240934144 2241065216 14 6106 47338 31 _ _ (1076507 / 50000) (2153017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241065216 :
    ThetaLowerSegment 2241065216 2241196288 (224099459177823 / 100000)
      (224112717474983 / 100000) := by
  exact
    packedTile65536 2241065216 2241196288 14 6158 47339 31 _ _ (107651 / 5000) (2153023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241196288 :
    ThetaLowerSegment 2241196288 2241327360 (224112717474983 / 100000)
      (44825175353979 / 20000) := by
  exact
    packedTile65536 2241196288 2241327360 14 6112 47341 31 _ _ (1076513 / 50000) (2153029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241327360 :
    ThetaLowerSegment 2241327360 2241458432 (44825175353979 / 20000) (8965559549391 / 4000) := by
  exact
    packedTile65536 2241327360 2241458432 14 6090 47342 31 _ _ (269129 / 12500) (430607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241458432 :
    ThetaLowerSegment 2241458432 2241589504 (8965559549391 / 4000) (224152232071513 / 100000) := by
  exact
    packedTile65536 2241458432 2241589504 14 6151 47344 31 _ _ (1076519 / 50000) (2153041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241589504 :
    ThetaLowerSegment 2241589504 2241720576 (224152232071513 / 100000)
      (224165335497297 / 100000) := by
  exact
    packedTile65536 2241589504 2241720576 14 6086 47345 31 _ _ (538261 / 25000) (2153047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241720576 :
    ThetaLowerSegment 2241720576 2241851648 (224165335497297 / 100000) (1401115256916 / 625) := by
  exact
    packedTile65536 2241720576 2241851648 14 6087 47346 31 _ _ (2153049 / 100000) (538263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241851648 :
    ThetaLowerSegment 2241851648 2241982720 (1401115256916 / 625) (8967646884831 / 4000) := by
  exact
    packedTile65536 2241851648 2241982720 14 5913 47348 31 _ _ (430611 / 20000) (1076529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241982720 :
    ThetaLowerSegment 2241982720 2242113792 (8967646884831 / 4000) (224204245507167 / 100000) := by
  exact
    packedTile65536 2241982720 2242113792 14 6072 47349 31 _ _ (2153061 / 100000) (269133 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2242113792 :
    ThetaLowerSegment 2242113792 2242244864 (224204245507167 / 100000)
      (44843468953359 / 20000) := by
  exact
    packedTile65536 2242113792 2242244864 14 6084 47350 31 _ _ (2153067 / 100000) (215307 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2242244864 :
    ThetaLowerSegment 2242244864 2242375936 (44843468953359 / 20000) (112115208036489 / 50000) := by
  exact
    packedTile65536 2242244864 2242375936 14 6071 47352 31 _ _ (2153073 / 100000) (538269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2242375936 :
    ThetaLowerSegment 2242375936 2242507008 (112115208036489 / 50000)
      (224243694111171 / 100000) := by
  exact
    packedTile65536 2242375936 2242507008 14 6167 47353 31 _ _ (2153079 / 100000) (1076541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2242507008 :
    ThetaLowerSegment 2242507008 2242638080 (224243694111171 / 100000)
      (224256939890091 / 100000) := by
  exact
    packedTile65536 2242507008 2242638080 14 6152 47355 31 _ _ (430617 / 20000) (67284 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2242638080 :
    ThetaLowerSegment 2242638080 2242769152 (224256939890091 / 100000)
      (224269888573351 / 100000) := by
  exact
    packedTile65536 2242638080 2242769152 14 6014 47356 31 _ _ (215309 / 10000) (2153093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2242769152 :
    ThetaLowerSegment 2242769152 2242900224 (224269888573351 / 100000)
      (224282947100591 / 100000) := by
  exact
    packedTile65536 2242769152 2242900224 14 6065 47357 31 _ _ (269137 / 12500) (2153099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2242900224 :
    ThetaLowerSegment 2242900224 2243031296 (224282947100591 / 100000)
      (224296057338669 / 100000) := by
  exact
    packedTile65536 2242900224 2243031296 14 6089 47359 31 _ _ (1076551 / 50000) (430621 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2243031296 :
    ThetaLowerSegment 2243031296 2243162368 (224296057338669 / 100000)
      (224309115938689 / 100000) := by
  exact
    packedTile65536 2243031296 2243162368 14 6065 47360 31 _ _ (538277 / 25000) (2153111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2243162368 :
    ThetaLowerSegment 2243162368 2243293440 (224309115938689 / 100000)
      (44864432331283 / 20000) := by
  exact
    packedTile65536 2243162368 2243293440 14 6059 47362 31 _ _ (1076557 / 50000) (2153117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2243293440 :
    ThetaLowerSegment 2243293440 2243424512 (44864432331283 / 20000) (44867018228403 / 20000) := by
  exact
    packedTile65536 2243293440 2243424512 14 6005 47363 31 _ _ (13457 / 625) (2153123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2243424512 :
    ThetaLowerSegment 2243424512 2243555584 (44867018228403 / 20000) (44869679490903 / 20000) := by
  exact
    packedTile65536 2243424512 2243555584 14 6180 47364 31 _ _ (689 / 32) (269141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2243555584 :
    ThetaLowerSegment 2243555584 2243686656 (44869679490903 / 20000)
      (224361286096681 / 100000) := by
  exact
    packedTile65536 2243555584 2243686656 14 5986 47366 31 _ _ (2153131 / 100000) (1076567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2243686656 :
    ThetaLowerSegment 2243686656 2243817728 (224361286096681 / 100000) (11218726071491 / 5000) := by
  exact
    packedTile65536 2243686656 2243817728 14 6147 47367 31 _ _ (2153137 / 100000) (107657 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2243817728 :
    ThetaLowerSegment 2243817728 2243948800 (11218726071491 / 5000) (224387700818123 / 100000) := by
  exact
    packedTile65536 2243817728 2243948800 14 6121 47368 31 _ _ (2153143 / 100000) (1076573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2243948800 :
    ThetaLowerSegment 2243948800 2244079872 (224387700818123 / 100000)
      (22440084148647 / 10000) := by
  exact
    packedTile65536 2243948800 2244079872 14 6103 47370 31 _ _ (2153149 / 100000) (67286 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2244079872 :
    ThetaLowerSegment 2244079872 2244210944 (22440084148647 / 10000) (1795311823081 / 800) := by
  exact
    packedTile65536 2244079872 2244210944 14 6101 47371 31 _ _ (430631 / 20000) (1076579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2244210944 :
    ThetaLowerSegment 2244210944 2244342016 (1795311823081 / 800) (44885413388953 / 20000) := by
  exact
    packedTile65536 2244210944 2244342016 14 6079 47373 31 _ _ (53829 / 2500) (2153163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2244342016 :
    ThetaLowerSegment 2244342016 2244473088 (44885413388953 / 20000)
      (224440199104199 / 100000) := by
  exact
    packedTile65536 2244342016 2244473088 14 6099 47374 31 _ _ (1076583 / 50000) (2153169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2244473088 :
    ThetaLowerSegment 2244473088 2244604160 (224440199104199 / 100000)
      (224453137514747 / 100000) := by
  exact
    packedTile65536 2244473088 2244604160 14 6009 47375 31 _ _ (538293 / 25000) (86127 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2244604160 :
    ThetaLowerSegment 2244604160 2244735232 (224453137514747 / 100000)
      (224466379559447 / 100000) := by
  exact
    packedTile65536 2244604160 2244735232 14 6150 47377 31 _ _ (1076589 / 50000) (2153181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2244735232 :
    ThetaLowerSegment 2244735232 2244866304 (224466379559447 / 100000)
      (224479479530903 / 100000) := by
  exact
    packedTile65536 2244735232 2244866304 14 6084 47378 31 _ _ (67287 / 3125) (2153187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2244866304 :
    ThetaLowerSegment 2244866304 2244997376 (224479479530903 / 100000)
      (224492484798503 / 100000) := by
  exact
    packedTile65536 2244866304 2244997376 14 6040 47380 31 _ _ (215319 / 10000) (2153193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2244997376 :
    ThetaLowerSegment 2244997376 2245128448 (224492484798503 / 100000)
      (224505714034727 / 100000) := by
  exact
    packedTile65536 2244997376 2245128448 14 6144 47381 31 _ _ (538299 / 25000) (2153199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2245128448 :
    ThetaLowerSegment 2245128448 2245259520 (224505714034727 / 100000)
      (56129704065703 / 25000) := by
  exact
    packedTile65536 2245128448 2245259520 14 6085 47382 31 _ _ (2153201 / 100000) (538301 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2245259520 :
    ThetaLowerSegment 2245259520 2245390592 (56129704065703 / 25000) (112265999098033 / 50000) := by
  exact
    packedTile65536 2245259520 2245390592 14 6122 47384 31 _ _ (2153207 / 100000) (215321 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2245390592 :
    ThetaLowerSegment 2245390592 2245521664 (112265999098033 / 50000)
      (224545113416449 / 100000) := by
  exact
    packedTile65536 2245390592 2245521664 14 6091 47385 31 _ _ (2153213 / 100000) (67288 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2245521664 :
    ThetaLowerSegment 2245521664 2245652736 (224545113416449 / 100000)
      (224558260971663 / 100000) := by
  exact
    packedTile65536 2245521664 2245652736 14 6106 47386 31 _ _ (2153219 / 100000) (1076611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2245652736 :
    ThetaLowerSegment 2245652736 2245783808 (224558260971663 / 100000)
      (112285645068069 / 50000) := by
  exact
    packedTile65536 2245652736 2245783808 14 6051 47388 31 _ _ (86129 / 4000) (538307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2245783808 :
    ThetaLowerSegment 2245783808 2245914880 (112285645068069 / 50000)
      (112292255487239 / 50000) := by
  exact
    packedTile65536 2245783808 2245914880 14 6140 47389 31 _ _ (2153231 / 100000) (1076617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2245914880 :
    ThetaLowerSegment 2245914880 2246045952 (112292255487239 / 50000) (4491955153647 / 2000) := by
  exact
    packedTile65536 2245914880 2246045952 14 6152 47391 31 _ _ (538309 / 25000) (2153239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2246045952 :
    ThetaLowerSegment 2246045952 2246177024 (4491955153647 / 2000) (56152716116601 / 25000) := by
  exact
    packedTile65536 2246045952 2246177024 14 6087 47392 31 _ _ (1076621 / 50000) (430649 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2246177024 :
    ThetaLowerSegment 2246177024 2246308096 (56152716116601 / 25000) (56156004126297 / 25000) := by
  exact
    packedTile65536 2246177024 2246308096 14 6108 47393 31 _ _ (67289 / 3125) (2153251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2246308096 :
    ThetaLowerSegment 2246308096 2246439168 (56156004126297 / 25000) (112318591826699 / 50000) := by
  exact
    packedTile65536 2246308096 2246439168 14 6115 47395 31 _ _ (1076627 / 50000) (2153257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2246439168 :
    ThetaLowerSegment 2246439168 2246570240 (112318591826699 / 50000)
      (112325221714239 / 50000) := by
  exact
    packedTile65536 2246439168 2246570240 14 6158 47396 31 _ _ (107663 / 5000) (2153263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2246570240 :
    ThetaLowerSegment 2246570240 2246701312 (112325221714239 / 50000) (28082943256511 / 12500) := by
  exact
    packedTile65536 2246570240 2246701312 14 6085 47397 31 _ _ (1076633 / 50000) (2153269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2246701312 :
    ThetaLowerSegment 2246701312 2246832384 (28082943256511 / 12500) (22467659918089 / 10000) := by
  exact
    packedTile65536 2246701312 2246832384 14 6062 47399 31 _ _ (2153271 / 100000) (1076637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2246832384 :
    ThetaLowerSegment 2246832384 2246963456 (22467659918089 / 10000) (112344914457389 / 50000) := by
  exact
    packedTile65536 2246832384 2246963456 14 6144 47400 31 _ _ (2153277 / 100000) (13458 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2246963456 :
    ThetaLowerSegment 2246963456 2247094528 (112344914457389 / 50000)
      (224702793831721 / 100000) := by
  exact
    packedTile65536 2246963456 2247094528 14 6021 47402 31 _ _ (2153283 / 100000) (1076643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2247094528 :
    ThetaLowerSegment 2247094528 2247225600 (224702793831721 / 100000)
      (224715907361731 / 100000) := by
  exact
    packedTile65536 2247094528 2247225600 14 6090 47403 31 _ _ (2153289 / 100000) (538323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2247225600 :
    ThetaLowerSegment 2247225600 2247356672 (224715907361731 / 100000)
      (224729081220541 / 100000) := by
  exact
    packedTile65536 2247225600 2247356672 14 6118 47404 31 _ _ (430659 / 20000) (1076649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2247356672 :
    ThetaLowerSegment 2247356672 2247487744 (224729081220541 / 100000)
      (224742250809457 / 100000) := by
  exact
    packedTile65536 2247356672 2247487744 14 6116 47406 31 _ _ (2153301 / 100000) (269163 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2247487744 :
    ThetaLowerSegment 2247487744 2247618816 (224742250809457 / 100000)
      (224755293383899 / 100000) := by
  exact
    packedTile65536 2247487744 2247618816 14 6057 47407 31 _ _ (1076653 / 50000) (2153309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2247618816 :
    ThetaLowerSegment 2247618816 2247749888 (224755293383899 / 100000)
      (44953682702783 / 20000) := by
  exact
    packedTile65536 2247618816 2247749888 14 6093 47409 31 _ _ (67291 / 3125) (430663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2247749888 :
    ThetaLowerSegment 2247749888 2247880960 (44953682702783 / 20000) (44956314057379 / 20000) := by
  exact
    packedTile65536 2247749888 2247880960 14 6110 47410 31 _ _ (1076659 / 50000) (2153321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2247880960 :
    ThetaLowerSegment 2247880960 2248012032 (44956314057379 / 20000)
      (224794744323127 / 100000) := by
  exact
    packedTile65536 2247880960 2248012032 14 6118 47411 31 _ _ (538331 / 25000) (2153327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2248012032 :
    ThetaLowerSegment 2248012032 2248143104 (224794744323127 / 100000)
      (224807845182847 / 100000) := by
  exact
    packedTile65536 2248012032 2248143104 14 6084 47413 31 _ _ (215333 / 10000) (2153333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2248143104 :
    ThetaLowerSegment 2248143104 2248274176 (224807845182847 / 100000)
      (224820875018983 / 100000) := by
  exact
    packedTile65536 2248143104 2248274176 14 6051 47414 31 _ _ (269167 / 12500) (2153339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2248274176 :
    ThetaLowerSegment 2248274176 2248405248 (224820875018983 / 100000)
      (44966751260969 / 20000) := by
  exact
    packedTile65536 2248274176 2248405248 14 5982 47415 31 _ _ (2153341 / 100000) (67292 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2248405248 :
    ThetaLowerSegment 2248405248 2248536320 (44966751260969 / 20000)
      (224846844347911 / 100000) := by
  exact
    packedTile65536 2248405248 2248536320 14 6078 47417 31 _ _ (2153347 / 100000) (43067 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2248536320 :
    ThetaLowerSegment 2248536320 2248667392 (224846844347911 / 100000)
      (224860065935331 / 100000) := by
  exact
    packedTile65536 2248536320 2248667392 14 6140 47418 31 _ _ (2153353 / 100000) (538339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2248667392 :
    ThetaLowerSegment 2248667392 2248798464 (224860065935331 / 100000)
      (56218314891481 / 25000) := by
  exact
    packedTile65536 2248667392 2248798464 14 6127 47420 31 _ _ (2153359 / 100000) (1076681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2248798464 :
    ThetaLowerSegment 2248798464 2248929536 (56218314891481 / 25000) (7027701461662 / 3125) := by
  exact
    packedTile65536 2248798464 2248929536 14 6124 47421 31 _ _ (430673 / 20000) (269171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2248929536 :
    ThetaLowerSegment 2248929536 2249060608 (7027701461662 / 3125) (112449702879931 / 50000) := by
  exact
    packedTile65536 2248929536 2249060608 14 6018 47422 31 _ _ (2153371 / 100000) (1076687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249060608 :
    ThetaLowerSegment 2249060608 2249191680 (112449702879931 / 50000)
      (112456296517243 / 50000) := by
  exact
    packedTile65536 2249060608 2249191680 14 6124 47424 31 _ _ (67293 / 3125) (2153379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249191680 :
    ThetaLowerSegment 2249191680 2249322752 (112456296517243 / 50000) (2811570181693 / 1250) := by
  exact
    packedTile65536 2249191680 2249322752 14 6047 47425 31 _ _ (1076691 / 50000) (430677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249322752 :
    ThetaLowerSegment 2249322752 2249339136 (2811570181693 / 1250) (2811590638879 / 1250) := by
  exact
    packedTile65536 2249322752 2249339136 11 760 47427 31 _ _ (538347 / 25000) (2153391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249339136 :
    ThetaLowerSegment 2249339136 2249341184 (2811590638879 / 1250) (8997098227291 / 4000) := by
  exact
    packedTile65536 2249339136 2249341184 8 95 47427 31 _ _ (2153389 / 100000) (134587 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2217341184_2249341184 :
    ThetaLowerSegment 2217341184 2249341184 (221727109576867 / 100000) (8997098227291 / 4000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2217341184 cell2217472256)
                  (ThetaLowerSegment.join cell2217603328 cell2217734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2217865472 cell2217996544)
                  (ThetaLowerSegment.join cell2218127616 cell2218258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2218389760 cell2218520832)
                  (ThetaLowerSegment.join cell2218651904 cell2218782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2218914048 cell2219045120)
                  (ThetaLowerSegment.join cell2219176192 cell2219307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2219438336 cell2219569408)
                  (ThetaLowerSegment.join cell2219700480 cell2219831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2219962624 cell2220093696)
                  (ThetaLowerSegment.join cell2220224768 cell2220355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2220486912 cell2220617984)
                  (ThetaLowerSegment.join cell2220749056 cell2220880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2221011200 cell2221142272)
                  (ThetaLowerSegment.join cell2221273344 cell2221404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2221535488 cell2221666560)
                  (ThetaLowerSegment.join cell2221797632 cell2221928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2222059776 cell2222190848)
                  (ThetaLowerSegment.join cell2222321920 cell2222452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2222584064 cell2222715136)
                  (ThetaLowerSegment.join cell2222846208 cell2222977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2223108352 cell2223239424)
                  (ThetaLowerSegment.join cell2223370496 cell2223501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2223632640 cell2223763712)
                  (ThetaLowerSegment.join cell2223894784 cell2224025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2224156928 cell2224288000)
                  (ThetaLowerSegment.join cell2224419072 cell2224550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2224681216 cell2224812288)
                  (ThetaLowerSegment.join cell2224943360 cell2225074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2225205504 cell2225336576)
                  (ThetaLowerSegment.join cell2225467648 cell2225598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2225729792 cell2225860864)
                  (ThetaLowerSegment.join cell2225991936 cell2226123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2226254080 cell2226385152)
                  (ThetaLowerSegment.join cell2226516224 cell2226647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2226778368 cell2226909440)
                  (ThetaLowerSegment.join cell2227040512 cell2227171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2227302656 cell2227433728)
                  (ThetaLowerSegment.join cell2227564800 cell2227695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2227826944 cell2227958016)
                  (ThetaLowerSegment.join cell2228089088 cell2228220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2228351232 cell2228482304)
                  (ThetaLowerSegment.join cell2228613376 cell2228744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2228875520 cell2229006592)
                  (ThetaLowerSegment.join cell2229137664 cell2229268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2229399808 cell2229530880)
                  (ThetaLowerSegment.join cell2229661952 cell2229793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2229924096 cell2230055168)
                  (ThetaLowerSegment.join cell2230186240 cell2230317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2230448384 cell2230579456)
                  (ThetaLowerSegment.join cell2230710528 cell2230841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2230972672 cell2231103744)
                  (ThetaLowerSegment.join cell2231234816 cell2231365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2231496960 cell2231628032)
                  (ThetaLowerSegment.join cell2231759104 cell2231890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2232021248 cell2232152320)
                  (ThetaLowerSegment.join cell2232283392 cell2232414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2232545536 cell2232676608)
                  (ThetaLowerSegment.join cell2232807680 cell2232938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2233069824 cell2233200896)
                  (ThetaLowerSegment.join cell2233331968 cell2233463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2233594112 cell2233725184)
                  (ThetaLowerSegment.join cell2233856256 cell2233987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2234118400 cell2234249472)
                  (ThetaLowerSegment.join cell2234380544 cell2234511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2234642688 cell2234773760)
                  (ThetaLowerSegment.join cell2234904832 cell2235035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2235166976 cell2235298048)
                  (ThetaLowerSegment.join cell2235429120 cell2235560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2235691264 cell2235822336)
                  (ThetaLowerSegment.join cell2235953408 cell2236084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2236215552 cell2236346624)
                  (ThetaLowerSegment.join cell2236477696 cell2236608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2236739840 cell2236870912)
                  (ThetaLowerSegment.join cell2237001984 cell2237133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2237264128 cell2237395200)
                  (ThetaLowerSegment.join cell2237526272 cell2237657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2237788416 cell2237919488)
                  (ThetaLowerSegment.join cell2238050560 cell2238181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2238312704 cell2238443776)
                  (ThetaLowerSegment.join cell2238574848 cell2238705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2238836992 cell2238968064)
                  (ThetaLowerSegment.join cell2239099136 cell2239230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2239361280 cell2239492352)
                  (ThetaLowerSegment.join cell2239623424 cell2239754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2239885568 cell2240016640)
                  (ThetaLowerSegment.join cell2240147712 cell2240278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2240409856 cell2240540928)
                  (ThetaLowerSegment.join cell2240672000 cell2240803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2240934144 cell2241065216)
                  (ThetaLowerSegment.join cell2241196288 cell2241327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2241458432 cell2241589504)
                  (ThetaLowerSegment.join cell2241720576 cell2241851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2241982720 cell2242113792)
                  (ThetaLowerSegment.join cell2242244864 cell2242375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2242507008 cell2242638080)
                  (ThetaLowerSegment.join cell2242769152 cell2242900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2243031296 cell2243162368)
                  (ThetaLowerSegment.join cell2243293440 cell2243424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2243555584 cell2243686656)
                  (ThetaLowerSegment.join cell2243817728 cell2243948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2244079872 cell2244210944)
                  (ThetaLowerSegment.join cell2244342016 cell2244473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2244604160 cell2244735232)
                  (ThetaLowerSegment.join cell2244866304 cell2244997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2245128448 cell2245259520)
                  (ThetaLowerSegment.join cell2245390592 cell2245521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2245652736 cell2245783808)
                  (ThetaLowerSegment.join cell2245914880 cell2246045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2246177024 cell2246308096)
                  (ThetaLowerSegment.join cell2246439168 cell2246570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2246701312 cell2246832384)
                  (ThetaLowerSegment.join cell2246963456 cell2247094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2247225600 cell2247356672)
                  (ThetaLowerSegment.join cell2247487744 cell2247618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2247749888 cell2247880960)
                  (ThetaLowerSegment.join cell2248012032 cell2248143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2248274176 cell2248405248)
                  (ThetaLowerSegment.join cell2248536320 cell2248667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2248798464 cell2248929536)
                (ThetaLowerSegment.join cell2249060608 cell2249191680))
              (ThetaLowerSegment.join cell2249322752 cell2249339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
