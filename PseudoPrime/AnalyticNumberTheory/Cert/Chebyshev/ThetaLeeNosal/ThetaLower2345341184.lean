/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2345341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2313341184 :
    ThetaLowerSegment 2313341184 2313472256 (115664835976187 / 50000) (14458923446457 / 6250) := by
  exact
    packedTile65536 2313341184 2313472256 14 6077 48097 31 _ _ (1078097 / 50000) (2156197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313472256 :
    ThetaLowerSegment 2313472256 2313603328 (14458923446457 / 6250) (7229872883616 / 3125) := by
  exact
    packedTile65536 2313472256 2313603328 14 6102 48098 31 _ _ (10781 / 500) (2156203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313603328 :
    ThetaLowerSegment 2313603328 2313734400 (7229872883616 / 3125) (115684463864637 / 50000) := by
  exact
    packedTile65536 2313603328 2313734400 14 6027 48099 31 _ _ (1078103 / 50000) (2156209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313734400 :
    ThetaLowerSegment 2313734400 2313865472 (115684463864637 / 50000)
      (231381871463907 / 100000) := by
  exact
    packedTile65536 2313734400 2313865472 14 6003 48101 31 _ _ (2156211 / 100000) (1078107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313865472 :
    ThetaLowerSegment 2313865472 2313996544 (231381871463907 / 100000)
      (57848810541381 / 25000) := by
  exact
    packedTile65536 2313865472 2313996544 14 6201 48102 31 _ _ (2156217 / 100000) (107811 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313996544 :
    ThetaLowerSegment 2313996544 2314127616 (57848810541381 / 25000) (14463022539141 / 6250) := by
  exact
    packedTile65536 2313996544 2314127616 14 6084 48104 31 _ _ (2156223 / 100000) (1078113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2314127616 :
    ThetaLowerSegment 2314127616 2314258688 (14463022539141 / 6250) (57855404279 / 25) := by
  exact
    packedTile65536 2314127616 2314258688 14 6148 48105 31 _ _ (539057 / 25000) (2156231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2314258688 :
    ThetaLowerSegment 2314258688 2314389760 (57855404279 / 25) (57858689301499 / 25000) := by
  exact
    packedTile65536 2314258688 2314389760 14 6094 48106 31 _ _ (1078117 / 50000) (2156237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2314389760 :
    ThetaLowerSegment 2314389760 2314520832 (57858689301499 / 25000) (57862008832979 / 25000) := by
  exact
    packedTile65536 2314389760 2314520832 14 6158 48108 31 _ _ (26953 / 1250) (2156243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2314520832 :
    ThetaLowerSegment 2314520832 2314651904 (57862008832979 / 25000)
      (231461100020371 / 100000) := by
  exact
    packedTile65536 2314520832 2314651904 14 6059 48109 31 _ _ (431249 / 20000) (269531 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2314651904 :
    ThetaLowerSegment 2314651904 2314782976 (231461100020371 / 100000)
      (231474253151471 / 100000) := by
  exact
    packedTile65536 2314651904 2314782976 14 6100 48110 31 _ _ (2156251 / 100000) (1078127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2314782976 :
    ThetaLowerSegment 2314782976 2314914048 (231474253151471 / 100000)
      (115743749519111 / 50000) := by
  exact
    packedTile65536 2314782976 2314914048 14 6143 48112 31 _ _ (2156257 / 100000) (107813 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2314914048 :
    ThetaLowerSegment 2314914048 2315045120 (115743749519111 / 50000) (11575027113353 / 5000) := by
  exact
    packedTile65536 2314914048 2315045120 14 6049 48113 31 _ _ (1078131 / 50000) (431253 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315045120 :
    ThetaLowerSegment 2315045120 2315176192 (11575027113353 / 5000) (11575678306289 / 5000) := by
  exact
    packedTile65536 2315045120 2315176192 14 6040 48114 31 _ _ (539067 / 25000) (2156271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315176192 :
    ThetaLowerSegment 2315176192 2315307264 (11575678306289 / 5000) (115763390964563 / 50000) := by
  exact
    packedTile65536 2315176192 2315307264 14 6129 48116 31 _ _ (1078137 / 50000) (2156277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315307264 :
    ThetaLowerSegment 2315307264 2315438336 (115763390964563 / 50000)
      (231539769197543 / 100000) := by
  exact
    packedTile65536 2315307264 2315438336 14 6023 48117 31 _ _ (2156279 / 100000) (1078141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315438336 :
    ThetaLowerSegment 2315438336 2315569408 (231539769197543 / 100000)
      (115776516253289 / 50000) := by
  exact
    packedTile65536 2315438336 2315569408 14 6151 48119 31 _ _ (431257 / 20000) (67384 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315569408 :
    ThetaLowerSegment 2315569408 2315700480 (115776516253289 / 50000) (57891530298237 / 25000) := by
  exact
    packedTile65536 2315569408 2315700480 14 6070 48120 31 _ _ (2156291 / 100000) (1078147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315700480 :
    ThetaLowerSegment 2315700480 2315831552 (57891530298237 / 25000) (57894836439079 / 25000) := by
  exact
    packedTile65536 2315700480 2315831552 14 6133 48121 31 _ _ (269537 / 12500) (2156299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315831552 :
    ThetaLowerSegment 2315831552 2315962624 (57894836439079 / 25000) (23159236335149 / 10000) := by
  exact
    packedTile65536 2315831552 2315962624 14 6037 48123 31 _ _ (1078151 / 50000) (431261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315962624 :
    ThetaLowerSegment 2315962624 2316093696 (23159236335149 / 10000) (115802778900071 / 50000) := by
  exact
    packedTile65536 2315962624 2316093696 14 6119 48124 31 _ _ (539077 / 25000) (2156311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2316093696 :
    ThetaLowerSegment 2316093696 2316224768 (115802778900071 / 50000)
      (115809299590583 / 50000) := by
  exact
    packedTile65536 2316093696 2316224768 14 6048 48125 31 _ _ (2156313 / 100000) (539079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2316224768 :
    ThetaLowerSegment 2316224768 2316355840 (115809299590583 / 50000)
      (231631858386697 / 100000) := by
  exact
    packedTile65536 2316224768 2316355840 14 6149 48127 31 _ _ (2156319 / 100000) (1078161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2316355840 :
    ThetaLowerSegment 2316355840 2316486912 (231631858386697 / 100000)
      (115822468248911 / 50000) := by
  exact
    packedTile65536 2316355840 2316486912 14 6065 48128 31 _ _ (86253 / 4000) (269541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2316486912 :
    ThetaLowerSegment 2316486912 2316617984 (115822468248911 / 50000) (28957249673579 / 12500) := by
  exact
    packedTile65536 2316486912 2316617984 14 6057 48129 31 _ _ (215633 / 10000) (2156333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2316617984 :
    ThetaLowerSegment 2316617984 2316749056 (28957249673579 / 12500) (28958895766573 / 12500) := by
  exact
    packedTile65536 2316617984 2316749056 14 6107 48131 31 _ _ (134771 / 6250) (2156339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2316749056 :
    ThetaLowerSegment 2316749056 2316880128 (28958895766573 / 12500) (115842100609987 / 50000) := by
  exact
    packedTile65536 2316749056 2316880128 14 6045 48132 31 _ _ (1078171 / 50000) (431269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2316880128 :
    ThetaLowerSegment 2316880128 2317011200 (115842100609987 / 50000) (7240544093803 / 3125) := by
  exact
    packedTile65536 2316880128 2317011200 14 6126 48133 31 _ _ (2156347 / 100000) (43127 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2317011200 :
    ThetaLowerSegment 2317011200 2317142272 (7240544093803 / 3125) (46342092681281 / 20000) := by
  exact
    packedTile65536 2317011200 2317142272 14 6053 48135 31 _ _ (2156353 / 100000) (539089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2317142272 :
    ThetaLowerSegment 2317142272 2317273344 (46342092681281 / 20000) (23172347703297 / 10000) := by
  exact
    packedTile65536 2317142272 2317273344 14 6035 48136 31 _ _ (2156359 / 100000) (1078181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2317273344 :
    ThetaLowerSegment 2317273344 2317404416 (23172347703297 / 10000) (115868294941227 / 50000) := by
  exact
    packedTile65536 2317273344 2317404416 14 6081 48138 31 _ _ (539091 / 25000) (2156367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2317404416 :
    ThetaLowerSegment 2317404416 2317535488 (115868294941227 / 50000) (14484344023899 / 6250) := by
  exact
    packedTile65536 2317404416 2317535488 14 5989 48139 31 _ _ (215637 / 10000) (2156373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2317535488 :
    ThetaLowerSegment 2317535488 2317666560 (14484344023899 / 6250) (28970311529379 / 12500) := by
  exact
    packedTile65536 2317535488 2317666560 14 6023 48140 31 _ _ (269547 / 12500) (2156379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2317666560 :
    ThetaLowerSegment 2317666560 2317797632 (28970311529379 / 12500)
      (231775424051889 / 100000) := by
  exact
    packedTile65536 2317666560 2317797632 14 5997 48142 31 _ _ (2156381 / 100000) (67387 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2317797632 :
    ThetaLowerSegment 2317797632 2317928704 (231775424051889 / 100000)
      (231788565074267 / 100000) := by
  exact
    packedTile65536 2317797632 2317928704 14 6094 48143 31 _ _ (2156387 / 100000) (215639 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2317928704 :
    ThetaLowerSegment 2317928704 2318059776 (231788565074267 / 100000)
      (231801622027827 / 100000) := by
  exact
    packedTile65536 2317928704 2318059776 14 6055 48144 31 _ _ (269549 / 12500) (431279 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2318059776 :
    ThetaLowerSegment 2318059776 2318190848 (231801622027827 / 100000)
      (231814694112503 / 100000) := by
  exact
    packedTile65536 2318059776 2318190848 14 6062 48146 31 _ _ (1078199 / 50000) (2156401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2318190848 :
    ThetaLowerSegment 2318190848 2318321920 (231814694112503 / 100000)
      (231827591564827 / 100000) := by
  exact
    packedTile65536 2318190848 2318321920 14 5981 48147 31 _ _ (539101 / 25000) (2156407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2318321920 :
    ThetaLowerSegment 2318321920 2318452992 (231827591564827 / 100000)
      (231840780162271 / 100000) := by
  exact
    packedTile65536 2318321920 2318452992 14 6116 48148 31 _ _ (2156409 / 100000) (539103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2318452992 :
    ThetaLowerSegment 2318452992 2318584064 (231840780162271 / 100000)
      (115926963912263 / 50000) := by
  exact
    packedTile65536 2318452992 2318584064 14 6097 48150 31 _ _ (431283 / 20000) (1078209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2318584064 :
    ThetaLowerSegment 2318584064 2318715136 (115926963912263 / 50000)
      (231866881445473 / 100000) := by
  exact
    packedTile65536 2318584064 2318715136 14 6007 48151 31 _ _ (2156421 / 100000) (269553 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2318715136 :
    ThetaLowerSegment 2318715136 2318846208 (231866881445473 / 100000)
      (231879841565733 / 100000) := by
  exact
    packedTile65536 2318715136 2318846208 14 6010 48153 31 _ _ (1078213 / 50000) (2156429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2318846208 :
    ThetaLowerSegment 2318846208 2318977280 (231879841565733 / 100000)
      (46378575870721 / 20000) := by
  exact
    packedTile65536 2318846208 2318977280 14 6046 48154 31 _ _ (134777 / 6250) (431287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2318977280 :
    ThetaLowerSegment 2318977280 2319108352 (46378575870721 / 20000)
      (231905923647067 / 100000) := by
  exact
    packedTile65536 2318977280 2319108352 14 6049 48155 31 _ _ (1078219 / 50000) (2156441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2319108352 :
    ThetaLowerSegment 2319108352 2319239424 (231905923647067 / 100000)
      (231918987378761 / 100000) := by
  exact
    packedTile65536 2319108352 2319239424 14 6058 48157 31 _ _ (2156443 / 100000) (1078223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2319239424 :
    ThetaLowerSegment 2319239424 2319370496 (231918987378761 / 100000)
      (57983017638711 / 25000) := by
  exact
    packedTile65536 2319239424 2319370496 14 6067 48158 31 _ _ (2156449 / 100000) (539113 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2319370496 :
    ThetaLowerSegment 2319370496 2319501568 (57983017638711 / 25000)
      (231944972625109 / 100000) := by
  exact
    packedTile65536 2319370496 2319501568 14 5983 48159 31 _ _ (431291 / 20000) (1078229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2319501568 :
    ThetaLowerSegment 2319501568 2319632640 (231944972625109 / 100000)
      (231958047242089 / 100000) := by
  exact
    packedTile65536 2319501568 2319632640 14 6063 48161 31 _ _ (107823 / 5000) (2156463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2319632640 :
    ThetaLowerSegment 2319632640 2319763712 (231958047242089 / 100000)
      (231971156398903 / 100000) := by
  exact
    packedTile65536 2319632640 2319763712 14 6079 48162 31 _ _ (1078233 / 50000) (2156469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2319763712 :
    ThetaLowerSegment 2319763712 2319894784 (231971156398903 / 100000)
      (231984220306279 / 100000) := by
  exact
    packedTile65536 2319763712 2319894784 14 6058 48163 31 _ _ (269559 / 12500) (86259 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2319894784 :
    ThetaLowerSegment 2319894784 2320025856 (231984220306279 / 100000) (4639948488299 / 2000) := by
  exact
    packedTile65536 2319894784 2320025856 14 6123 48165 31 _ _ (2156477 / 100000) (13478 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2320025856 :
    ThetaLowerSegment 2320025856 2320156928 (4639948488299 / 2000) (46402135200597 / 20000) := by
  exact
    packedTile65536 2320025856 2320156928 14 6145 48166 31 _ _ (2156483 / 100000) (1078243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2320156928 :
    ThetaLowerSegment 2320156928 2320288000 (46402135200597 / 20000) (116011968126923 / 50000) := by
  exact
    packedTile65536 2320156928 2320288000 14 6149 48168 31 _ _ (2156489 / 100000) (539123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2320288000 :
    ThetaLowerSegment 2320288000 2320419072 (116011968126923 / 50000) (58009271099441 / 25000) := by
  exact
    packedTile65536 2320288000 2320419072 14 6097 48169 31 _ _ (1078247 / 50000) (2156497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2320419072 :
    ThetaLowerSegment 2320419072 2320550144 (58009271099441 / 25000) (7251568824602 / 3125) := by
  exact
    packedTile65536 2320419072 2320550144 14 6083 48170 31 _ _ (4313 / 200) (2156503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2320550144 :
    ThetaLowerSegment 2320550144 2320681216 (7251568824602 / 3125) (58015868381297 / 25000) := by
  exact
    packedTile65536 2320550144 2320681216 14 6154 48172 31 _ _ (1078253 / 50000) (2156509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2320681216 :
    ThetaLowerSegment 2320681216 2320812288 (58015868381297 / 25000)
      (232076695094129 / 100000) := by
  exact
    packedTile65536 2320681216 2320812288 14 6131 48173 31 _ _ (2156511 / 100000) (1078257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2320812288 :
    ThetaLowerSegment 2320812288 2320943360 (232076695094129 / 100000)
      (232089858473897 / 100000) := by
  exact
    packedTile65536 2320812288 2320943360 14 6104 48174 31 _ _ (2156517 / 100000) (53913 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2320943360 :
    ThetaLowerSegment 2320943360 2321074432 (232089858473897 / 100000)
      (232103006788531 / 100000) := by
  exact
    packedTile65536 2320943360 2321074432 14 6097 48176 31 _ _ (1078261 / 50000) (86261 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2321074432 :
    ThetaLowerSegment 2321074432 2321205504 (232103006788531 / 100000)
      (232116036530707 / 100000) := by
  exact
    packedTile65536 2321074432 2321205504 14 6042 48177 31 _ _ (134783 / 6250) (2156531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2321205504 :
    ThetaLowerSegment 2321205504 2321336576 (232116036530707 / 100000)
      (232129031804591 / 100000) := by
  exact
    packedTile65536 2321205504 2321336576 14 6026 48178 31 _ _ (1078267 / 50000) (2156537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2321336576 :
    ThetaLowerSegment 2321336576 2321467648 (232129031804591 / 100000)
      (232142238449427 / 100000) := by
  exact
    packedTile65536 2321336576 2321467648 14 6124 48180 31 _ _ (2156539 / 100000) (1078271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2321467648 :
    ThetaLowerSegment 2321467648 2321598720 (232142238449427 / 100000)
      (29019402875859 / 12500) := by
  exact
    packedTile65536 2321467648 2321598720 14 6021 48181 31 _ _ (431309 / 20000) (539137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2321598720 :
    ThetaLowerSegment 2321598720 2321729792 (29019402875859 / 12500) (14510526318687 / 6250) := by
  exact
    packedTile65536 2321598720 2321729792 14 6120 48182 31 _ _ (2156551 / 100000) (1078277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2321729792 :
    ThetaLowerSegment 2321729792 2321860864 (14510526318687 / 6250) (2902267221093 / 1250) := by
  exact
    packedTile65536 2321729792 2321860864 14 6008 48184 31 _ _ (539139 / 25000) (2156559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2321860864 :
    ThetaLowerSegment 2321860864 2321991936 (2902267221093 / 1250) (116097265279539 / 50000) := by
  exact
    packedTile65536 2321860864 2321991936 14 6099 48185 31 _ _ (1078281 / 50000) (431313 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2321991936 :
    ThetaLowerSegment 2321991936 2322123008 (116097265279539 / 50000)
      (116103839577087 / 50000) := by
  exact
    packedTile65536 2321991936 2322123008 14 6097 48187 31 _ _ (269571 / 12500) (2156571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2322123008 :
    ThetaLowerSegment 2322123008 2322254080 (116103839577087 / 50000)
      (232220819153463 / 100000) := by
  exact
    packedTile65536 2322123008 2322254080 14 6093 48188 31 _ _ (2156573 / 100000) (67393 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2322254080 :
    ThetaLowerSegment 2322254080 2322385152 (232220819153463 / 100000)
      (46446776741809 / 20000) := by
  exact
    packedTile65536 2322254080 2322385152 14 6058 48189 31 _ _ (2156579 / 100000) (1078291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2322385152 :
    ThetaLowerSegment 2322385152 2322516224 (46446776741809 / 20000) (1857975413881 / 800) := by
  exact
    packedTile65536 2322385152 2322516224 14 6048 48191 31 _ _ (431317 / 20000) (539147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2322516224 :
    ThetaLowerSegment 2322516224 2322647296 (1857975413881 / 800) (46451974117661 / 20000) := by
  exact
    packedTile65536 2322516224 2322647296 14 6002 48192 31 _ _ (215659 / 10000) (2156593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2322647296 :
    ThetaLowerSegment 2322647296 2322778368 (46451974117661 / 20000)
      (232273105617957 / 100000) := by
  exact
    packedTile65536 2322647296 2322778368 14 6137 48193 31 _ _ (539149 / 25000) (2156599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2322778368 :
    ThetaLowerSegment 2322778368 2322909440 (232273105617957 / 100000)
      (232286161680411 / 100000) := by
  exact
    packedTile65536 2322778368 2322909440 14 6054 48195 31 _ _ (2156601 / 100000) (539151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2322909440 :
    ThetaLowerSegment 2322909440 2323040512 (232286161680411 / 100000)
      (232299109948839 / 100000) := by
  exact
    packedTile65536 2322909440 2323040512 14 6004 48196 31 _ _ (2156607 / 100000) (215661 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323040512 :
    ThetaLowerSegment 2323040512 2323171584 (232299109948839 / 100000)
      (232312286854269 / 100000) := by
  exact
    packedTile65536 2323040512 2323171584 14 6110 48197 31 _ _ (2156613 / 100000) (269577 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323171584 :
    ThetaLowerSegment 2323171584 2323302656 (232312286854269 / 100000)
      (46465087150843 / 20000) := by
  exact
    packedTile65536 2323171584 2323302656 14 6097 48199 31 _ _ (1078309 / 50000) (2156621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323302656 :
    ThetaLowerSegment 2323302656 2323433728 (46465087150843 / 20000)
      (232338711931559 / 100000) := by
  exact
    packedTile65536 2323302656 2323433728 14 6156 48200 31 _ _ (134789 / 6250) (2156627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323433728 :
    ThetaLowerSegment 2323433728 2323564800 (232338711931559 / 100000)
      (232351880314339 / 100000) := by
  exact
    packedTile65536 2323433728 2323564800 14 6106 48202 31 _ _ (215663 / 10000) (2156633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323564800 :
    ThetaLowerSegment 2323564800 2323695872 (232351880314339 / 100000)
      (116182419767027 / 50000) := by
  exact
    packedTile65536 2323564800 2323695872 14 6009 48203 31 _ _ (431327 / 20000) (1078319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323695872 :
    ThetaLowerSegment 2323695872 2323826944 (116182419767027 / 50000)
      (232378130912537 / 100000) := by
  exact
    packedTile65536 2323695872 2323826944 14 6163 48204 31 _ _ (2156641 / 100000) (539161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323826944 :
    ThetaLowerSegment 2323826944 2323958016 (232378130912537 / 100000)
      (23239115490377 / 10000) := by
  exact
    packedTile65536 2323826944 2323958016 14 6039 48206 31 _ _ (2156647 / 100000) (43133 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323958016 :
    ThetaLowerSegment 2323958016 2324089088 (23239115490377 / 10000) (116202126125683 / 50000) := by
  exact
    packedTile65536 2323958016 2324089088 14 6073 48207 31 _ _ (539163 / 25000) (431331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2324089088 :
    ThetaLowerSegment 2324089088 2324220160 (116202126125683 / 50000)
      (116208699619267 / 50000) := by
  exact
    packedTile65536 2324089088 2324220160 14 6096 48208 31 _ _ (1078329 / 50000) (2156661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2324220160 :
    ThetaLowerSegment 2324220160 2324351232 (116208699619267 / 50000)
      (116215186864579 / 50000) := by
  exact
    packedTile65536 2324220160 2324351232 14 6016 48210 31 _ _ (269583 / 12500) (2156667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2324351232 :
    ThetaLowerSegment 2324351232 2324482304 (116215186864579 / 50000) (14527724631883 / 6250) := by
  exact
    packedTile65536 2324351232 2324482304 14 6130 48211 31 _ _ (2156669 / 100000) (67396 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2324482304 :
    ThetaLowerSegment 2324482304 2324613376 (14527724631883 / 6250) (116228308056889 / 50000) := by
  exact
    packedTile65536 2324482304 2324613376 14 6038 48212 31 _ _ (86267 / 4000) (1078339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2324613376 :
    ThetaLowerSegment 2324613376 2324744448 (116228308056889 / 50000)
      (116234895635949 / 50000) := by
  exact
    packedTile65536 2324613376 2324744448 14 6109 48214 31 _ _ (53917 / 2500) (2156683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2324744448 :
    ThetaLowerSegment 2324744448 2324875520 (116234895635949 / 50000)
      (116241473528249 / 50000) := by
  exact
    packedTile65536 2324744448 2324875520 14 6100 48215 31 _ _ (1078343 / 50000) (2156689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2324875520 :
    ThetaLowerSegment 2324875520 2325006592 (116241473528249 / 50000)
      (116248037420351 / 50000) := by
  exact
    packedTile65536 2324875520 2325006592 14 6087 48216 31 _ _ (539173 / 25000) (431339 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2325006592 :
    ThetaLowerSegment 2325006592 2325137664 (116248037420351 / 50000)
      (116254602406019 / 50000) := by
  exact
    packedTile65536 2325006592 2325137664 14 6088 48218 31 _ _ (2156697 / 100000) (21567 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2325137664 :
    ThetaLowerSegment 2325137664 2325268736 (116254602406019 / 50000)
      (232522194634207 / 100000) := by
  exact
    packedTile65536 2325137664 2325268736 14 6023 48219 31 _ _ (2156703 / 100000) (1078353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2325268736 :
    ThetaLowerSegment 2325268736 2325399808 (232522194634207 / 100000) (11626758577613 / 5000) := by
  exact
    packedTile65536 2325268736 2325399808 14 6017 48221 31 _ _ (2156709 / 100000) (269589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2325399808 :
    ThetaLowerSegment 2325399808 2325530880 (11626758577613 / 5000) (14534273973889 / 6250) := by
  exact
    packedTile65536 2325399808 2325530880 14 6126 48222 31 _ _ (1078357 / 50000) (2156717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2325530880 :
    ThetaLowerSegment 2325530880 2325661952 (14534273973889 / 6250) (7267549796632 / 3125) := by
  exact
    packedTile65536 2325530880 2325661952 14 6125 48223 31 _ _ (26959 / 1250) (2156723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2325661952 :
    ThetaLowerSegment 2325661952 2325793024 (7267549796632 / 3125) (7267958496209 / 3125) := by
  exact
    packedTile65536 2325661952 2325793024 14 6064 48225 31 _ _ (1078363 / 50000) (2156729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2325793024 :
    ThetaLowerSegment 2325793024 2325924096 (7267958496209 / 3125) (46517568606981 / 20000) := by
  exact
    packedTile65536 2325793024 2325924096 14 6107 48226 31 _ _ (2156731 / 100000) (1078367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2325924096 :
    ThetaLowerSegment 2325924096 2326055168 (46517568606981 / 20000) (58150227676097 / 25000) := by
  exact
    packedTile65536 2325924096 2326055168 14 6059 48227 31 _ _ (2156737 / 100000) (107837 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2326055168 :
    ThetaLowerSegment 2326055168 2326186240 (58150227676097 / 25000) (7269191071216 / 3125) := by
  exact
    packedTile65536 2326055168 2326186240 14 6122 48229 31 _ _ (1078371 / 50000) (431349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2326186240 :
    ThetaLowerSegment 2326186240 2326317312 (7269191071216 / 3125) (29078392090417 / 12500) := by
  exact
    packedTile65536 2326186240 2326317312 14 6038 48230 31 _ _ (539187 / 25000) (2156751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2326317312 :
    ThetaLowerSegment 2326317312 2326448384 (29078392090417 / 12500) (58160046271259 / 25000) := by
  exact
    packedTile65536 2326317312 2326448384 14 6050 48231 31 _ _ (1078377 / 50000) (2156757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2326448384 :
    ThetaLowerSegment 2326448384 2326579456 (58160046271259 / 25000) (7270416376902 / 3125) := by
  exact
    packedTile65536 2326448384 2326579456 14 6092 48233 31 _ _ (2156759 / 100000) (1078381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2326579456 :
    ThetaLowerSegment 2326579456 2326710528 (7270416376902 / 3125) (232666508365309 / 100000) := by
  exact
    packedTile65536 2326579456 2326710528 14 6113 48234 31 _ _ (431353 / 20000) (67399 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2326710528 :
    ThetaLowerSegment 2326710528 2326841600 (232666508365309 / 100000) (14542482950923 / 6250) := by
  exact
    packedTile65536 2326710528 2326841600 14 6129 48235 31 _ _ (2156771 / 100000) (1078387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2326841600 :
    ThetaLowerSegment 2326841600 2326972672 (14542482950923 / 6250) (14543297133863 / 6250) := by
  exact
    packedTile65536 2326841600 2326972672 14 6040 48237 31 _ _ (269597 / 12500) (2156779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2326972672 :
    ThetaLowerSegment 2326972672 2327103744 (14543297133863 / 6250) (116352883003807 / 50000) := by
  exact
    packedTile65536 2326972672 2327103744 14 6033 48238 31 _ _ (1078391 / 50000) (431357 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2327103744 :
    ThetaLowerSegment 2327103744 2327234816 (116352883003807 / 50000)
      (116359399738749 / 50000) := by
  exact
    packedTile65536 2327103744 2327234816 14 6043 48240 31 _ _ (539197 / 25000) (2156791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2327234816 :
    ThetaLowerSegment 2327234816 2327365888 (116359399738749 / 50000) (29091497185341 / 12500) := by
  exact
    packedTile65536 2327234816 2327365888 14 6110 48241 31 _ _ (2156793 / 100000) (539199 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2327365888 :
    ThetaLowerSegment 2327365888 2327496960 (29091497185341 / 12500) (58186253293971 / 25000) := by
  exact
    packedTile65536 2327365888 2327496960 14 6044 48242 31 _ _ (2156799 / 100000) (1078401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2327496960 :
    ThetaLowerSegment 2327496960 2327628032 (58186253293971 / 25000) (58189516538423 / 25000) := by
  exact
    packedTile65536 2327496960 2327628032 14 6052 48244 31 _ _ (539201 / 25000) (2156807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2327628032 :
    ThetaLowerSegment 2327628032 2327759104 (58189516538423 / 25000) (116385655561951 / 50000) := by
  exact
    packedTile65536 2327628032 2327759104 14 6141 48245 31 _ _ (215681 / 10000) (2156813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2327759104 :
    ThetaLowerSegment 2327759104 2327890176 (116385655561951 / 50000)
      (116392234929159 / 50000) := by
  exact
    packedTile65536 2327759104 2327890176 14 6101 48246 31 _ _ (134801 / 6250) (2156819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2327890176 :
    ThetaLowerSegment 2327890176 2328021248 (116392234929159 / 50000)
      (232797494900337 / 100000) := by
  exact
    packedTile65536 2327890176 2328021248 14 6039 48248 31 _ _ (2156821 / 100000) (269603 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2328021248 :
    ThetaLowerSegment 2328021248 2328152320 (232797494900337 / 100000)
      (58202652641331 / 25000) := by
  exact
    packedTile65536 2328021248 2328152320 14 6081 48249 31 _ _ (2156827 / 100000) (215683 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2328152320 :
    ThetaLowerSegment 2328152320 2328283392 (58202652641331 / 25000) (58205870636167 / 25000) := by
  exact
    packedTile65536 2328152320 2328283392 14 5968 48250 31 _ _ (2156833 / 100000) (539209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2328283392 :
    ThetaLowerSegment 2328283392 2328414464 (58205870636167 / 25000) (116418227962619 / 50000) := by
  exact
    packedTile65536 2328283392 2328414464 14 6015 48252 31 _ _ (1078419 / 50000) (2156841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2328414464 :
    ThetaLowerSegment 2328414464 2328545536 (116418227962619 / 50000)
      (116424811728929 / 50000) := by
  exact
    packedTile65536 2328414464 2328545536 14 6105 48253 31 _ _ (539211 / 25000) (2156847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2328545536 :
    ThetaLowerSegment 2328545536 2328676608 (116424811728929 / 50000)
      (116431342667701 / 50000) := by
  exact
    packedTile65536 2328545536 2328676608 14 6056 48255 31 _ _ (2156849 / 100000) (539213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2328676608 :
    ThetaLowerSegment 2328676608 2328807680 (116431342667701 / 50000) (58218983184703 / 25000) := by
  exact
    packedTile65536 2328676608 2328807680 14 6142 48256 31 _ _ (431371 / 20000) (1078429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2328807680 :
    ThetaLowerSegment 2328807680 2328938752 (58218983184703 / 25000) (116444430481823 / 50000) := by
  exact
    packedTile65536 2328807680 2328938752 14 5994 48257 31 _ _ (2156861 / 100000) (67402 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2328938752 :
    ThetaLowerSegment 2328938752 2329069824 (116444430481823 / 50000) (23290194019907 / 10000) := by
  exact
    packedTile65536 2328938752 2329069824 14 6064 48259 31 _ _ (1078433 / 50000) (2156869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2329069824 :
    ThetaLowerSegment 2329069824 2329200896 (23290194019907 / 10000) (116457530225723 / 50000) := by
  exact
    packedTile65536 2329069824 2329200896 14 6083 48260 31 _ _ (269609 / 12500) (3451 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2329200896 :
    ThetaLowerSegment 2329200896 2329331968 (116457530225723 / 50000) (58232048420397 / 25000) := by
  exact
    packedTile65536 2329200896 2329331968 14 6089 48261 31 _ _ (1078439 / 50000) (2156881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2329331968 :
    ThetaLowerSegment 2329331968 2329463040 (58232048420397 / 25000) (58235352765153 / 25000) := by
  exact
    packedTile65536 2329331968 2329463040 14 6128 48263 31 _ _ (2156883 / 100000) (1078443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2329463040 :
    ThetaLowerSegment 2329463040 2329594112 (58235352765153 / 25000) (46590890753679 / 20000) := by
  exact
    packedTile65536 2329463040 2329594112 14 6047 48264 31 _ _ (2156889 / 100000) (539223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2329594112 :
    ThetaLowerSegment 2329594112 2329725184 (46590890753679 / 20000)
      (232967410230653 / 100000) := by
  exact
    packedTile65536 2329594112 2329725184 14 6007 48265 31 _ _ (1078447 / 50000) (2156897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2329725184 :
    ThetaLowerSegment 2329725184 2329856256 (232967410230653 / 100000)
      (232980528496453 / 100000) := by
  exact
    packedTile65536 2329725184 2329856256 14 6082 48267 31 _ _ (21569 / 1000) (2156903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2329856256 :
    ThetaLowerSegment 2329856256 2329987328 (232980528496453 / 100000)
      (232993595033001 / 100000) := by
  exact
    packedTile65536 2329856256 2329987328 14 6058 48268 31 _ _ (1078453 / 50000) (2156909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2329987328 :
    ThetaLowerSegment 2329987328 2330118400 (232993595033001 / 100000)
      (116503323250731 / 50000) := by
  exact
    packedTile65536 2329987328 2330118400 14 6051 48269 31 _ _ (2156911 / 100000) (1078457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2330118400 :
    ThetaLowerSegment 2330118400 2330249472 (116503323250731 / 50000) (58254874353237 / 25000) := by
  exact
    packedTile65536 2330118400 2330249472 14 5958 48271 31 _ _ (2156917 / 100000) (53923 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2330249472 :
    ThetaLowerSegment 2330249472 2330380544 (58254874353237 / 25000)
      (233032376400181 / 100000) := by
  exact
    packedTile65536 2330249472 2330380544 14 5971 48272 31 _ _ (2156923 / 100000) (1078463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2330380544 :
    ThetaLowerSegment 2330380544 2330511616 (233032376400181 / 100000)
      (46609123124849 / 20000) := by
  exact
    packedTile65536 2330380544 2330511616 14 6138 48274 31 _ _ (67404 / 3125) (2156931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2330511616 :
    ThetaLowerSegment 2330511616 2330642688 (46609123124849 / 20000)
      (233058576640651 / 100000) := by
  exact
    packedTile65536 2330511616 2330642688 14 6009 48275 31 _ _ (1078467 / 50000) (2156937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2330642688 :
    ThetaLowerSegment 2330642688 2330773760 (233058576640651 / 100000)
      (233071820246111 / 100000) := by
  exact
    packedTile65536 2330642688 2330773760 14 6140 48276 31 _ _ (2156939 / 100000) (1078471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2330773760 :
    ThetaLowerSegment 2330773760 2330904832 (233071820246111 / 100000)
      (58271236314109 / 25000) := by
  exact
    packedTile65536 2330773760 2330904832 14 6085 48278 31 _ _ (431389 / 20000) (539237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2330904832 :
    ThetaLowerSegment 2330904832 2331035904 (58271236314109 / 25000) (116549105252543 / 50000) := by
  exact
    packedTile65536 2330904832 2331035904 14 6150 48279 31 _ _ (2156951 / 100000) (1078477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331035904 :
    ThetaLowerSegment 2331035904 2331166976 (116549105252543 / 50000)
      (116555624652053 / 50000) := by
  exact
    packedTile65536 2331035904 2331166976 14 6045 48280 31 _ _ (539239 / 25000) (2156959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331166976 :
    ThetaLowerSegment 2331166976 2331298048 (116555624652053 / 50000) (58281130272823 / 25000) := by
  exact
    packedTile65536 2331166976 2331298048 14 6153 48282 31 _ _ (1078481 / 50000) (431393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331298048 :
    ThetaLowerSegment 2331298048 2331429120 (58281130272823 / 25000) (58284395383133 / 25000) := by
  exact
    packedTile65536 2331298048 2331429120 14 6055 48283 31 _ _ (269621 / 12500) (2156971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331429120 :
    ThetaLowerSegment 2331429120 2331560192 (58284395383133 / 25000) (23315075200967 / 10000) := by
  exact
    packedTile65536 2331429120 2331560192 14 6106 48284 31 _ _ (2156973 / 100000) (134811 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331560192 :
    ThetaLowerSegment 2331560192 2331691264 (23315075200967 / 10000) (46632749561629 / 20000) := by
  exact
    packedTile65536 2331560192 2331691264 14 6025 48286 31 _ _ (2156979 / 100000) (1078491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331691264 :
    ThetaLowerSegment 2331691264 2331822336 (46632749561629 / 20000) (46635381082109 / 20000) := by
  exact
    packedTile65536 2331691264 2331822336 14 6100 48287 31 _ _ (269623 / 12500) (2156987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331822336 :
    ThetaLowerSegment 2331822336 2331953408 (46635381082109 / 20000) (46637997079581 / 20000) := by
  exact
    packedTile65536 2331822336 2331953408 14 6064 48288 31 _ _ (215699 / 10000) (2156993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331953408 :
    ThetaLowerSegment 2331953408 2332084480 (46637997079581 / 20000) (46640617829721 / 20000) := by
  exact
    packedTile65536 2331953408 2332084480 14 6075 48290 31 _ _ (539249 / 25000) (2156999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2332084480 :
    ThetaLowerSegment 2332084480 2332215552 (46640617829721 / 20000) (116608098621841 / 50000) := by
  exact
    packedTile65536 2332084480 2332215552 14 6077 48291 31 _ _ (2157001 / 100000) (539251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2332215552 :
    ThetaLowerSegment 2332215552 2332346624 (116608098621841 / 50000) (23322927733413 / 10000) := by
  exact
    packedTile65536 2332215552 2332346624 14 6064 48293 31 _ _ (2157007 / 100000) (215701 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2332346624 :
    ThetaLowerSegment 2332346624 2332477696 (23322927733413 / 10000) (9329690070693 / 4000) := by
  exact
    packedTile65536 2332346624 2332477696 14 6015 48294 31 _ _ (2157013 / 100000) (269627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2332477696 :
    ThetaLowerSegment 2332477696 2332608768 (9329690070693 / 4000) (233255198189361 / 100000) := by
  exact
    packedTile65536 2332477696 2332608768 14 6002 48295 31 _ _ (1078509 / 50000) (2157021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2332608768 :
    ThetaLowerSegment 2332608768 2332739840 (233255198189361 / 100000)
      (233268427217553 / 100000) := by
  exact
    packedTile65536 2332608768 2332739840 14 6133 48297 31 _ _ (67407 / 3125) (2157027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2332739840 :
    ThetaLowerSegment 2332739840 2332870912 (233268427217553 / 100000)
      (58320410833559 / 25000) := by
  exact
    packedTile65536 2332739840 2332870912 14 6127 48298 31 _ _ (2157029 / 100000) (269629 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2332870912 :
    ThetaLowerSegment 2332870912 2333001984 (58320410833559 / 25000)
      (233294639470111 / 100000) := by
  exact
    packedTile65536 2332870912 2333001984 14 6025 48299 31 _ _ (431407 / 20000) (1078519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2333001984 :
    ThetaLowerSegment 2333001984 2333133056 (233294639470111 / 100000)
      (46661574151921 / 20000) := by
  exact
    packedTile65536 2333001984 2333133056 14 6134 48301 31 _ _ (2157041 / 100000) (539261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2333133056 :
    ThetaLowerSegment 2333133056 2333264128 (46661574151921 / 20000)
      (233321067567033 / 100000) := by
  exact
    packedTile65536 2333133056 2333264128 14 6118 48302 31 _ _ (1078523 / 50000) (2157049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2333264128 :
    ThetaLowerSegment 2333264128 2333395200 (233321067567033 / 100000)
      (233334126359841 / 100000) := by
  exact
    packedTile65536 2333264128 2333395200 14 6054 48303 31 _ _ (539263 / 25000) (431411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2333395200 :
    ThetaLowerSegment 2333395200 2333526272 (233334126359841 / 100000)
      (233347325397743 / 100000) := by
  exact
    packedTile65536 2333395200 2333526272 14 6119 48305 31 _ _ (1078529 / 50000) (2157061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2333526272 :
    ThetaLowerSegment 2333526272 2333657344 (233347325397743 / 100000)
      (233360479167917 / 100000) := by
  exact
    packedTile65536 2333526272 2333657344 14 6098 48306 31 _ _ (2157063 / 100000) (1078533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2333657344 :
    ThetaLowerSegment 2333657344 2333788416 (233360479167917 / 100000)
      (233373581205023 / 100000) := by
  exact
    packedTile65536 2333657344 2333788416 14 6074 48307 31 _ _ (2157069 / 100000) (134817 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2333788416 :
    ThetaLowerSegment 2333788416 2333919488 (233373581205023 / 100000)
      (233386588361243 / 100000) := by
  exact
    packedTile65536 2333788416 2333919488 14 6030 48309 31 _ _ (1078537 / 50000) (2157077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2333919488 :
    ThetaLowerSegment 2333919488 2334050560 (233386588361243 / 100000)
      (233399796162083 / 100000) := by
  exact
    packedTile65536 2333919488 2334050560 14 6123 48310 31 _ _ (53927 / 2500) (2157083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2334050560 :
    ThetaLowerSegment 2334050560 2334181632 (233399796162083 / 100000)
      (233412924187479 / 100000) := by
  exact
    packedTile65536 2334050560 2334181632 14 6086 48312 31 _ _ (1078543 / 50000) (2157089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2334181632 :
    ThetaLowerSegment 2334181632 2334312704 (233412924187479 / 100000)
      (23342595517421 / 10000) := by
  exact
    packedTile65536 2334181632 2334312704 14 6041 48313 31 _ _ (2157091 / 100000) (1078547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2334312704 :
    ThetaLowerSegment 2334312704 2334443776 (23342595517421 / 10000) (29179876779931 / 12500) := by
  exact
    packedTile65536 2334312704 2334443776 14 6054 48314 31 _ _ (2157097 / 100000) (21571 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2334443776 :
    ThetaLowerSegment 2334443776 2334574848 (29179876779931 / 12500) (14590769413511 / 6250) := by
  exact
    packedTile65536 2334443776 2334574848 14 6164 48316 31 _ _ (1078551 / 50000) (431421 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2334574848 :
    ThetaLowerSegment 2334574848 2334705920 (14590769413511 / 6250) (29183173375609 / 12500) := by
  exact
    packedTile65536 2334574848 2334705920 14 6062 48317 31 _ _ (539277 / 25000) (2157111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2334705920 :
    ThetaLowerSegment 2334705920 2334836992 (29183173375609 / 12500) (5836964282141 / 2500) := by
  exact
    packedTile65536 2334705920 2334836992 14 6112 48318 31 _ _ (1078557 / 50000) (2157117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2334836992 :
    ThetaLowerSegment 2334836992 2334968064 (5836964282141 / 2500) (233491649898137 / 100000) := by
  exact
    packedTile65536 2334836992 2334968064 14 6063 48320 31 _ _ (2157119 / 100000) (1078561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2334968064 :
    ThetaLowerSegment 2334968064 2335099136 (233491649898137 / 100000)
      (58376169194003 / 25000) := by
  exact
    packedTile65536 2334968064 2335099136 14 6039 48321 31 _ _ (17257 / 800) (269641 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2335099136 :
    ThetaLowerSegment 2335099136 2335230208 (58376169194003 / 25000)
      (233517789975361 / 100000) := by
  exact
    packedTile65536 2335099136 2335230208 14 6079 48322 31 _ _ (2157131 / 100000) (1078567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2335230208 :
    ThetaLowerSegment 2335230208 2335361280 (233517789975361 / 100000)
      (46706212998061 / 20000) := by
  exact
    packedTile65536 2335230208 2335361280 14 6154 48324 31 _ _ (134821 / 6250) (2157139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2335361280 :
    ThetaLowerSegment 2335361280 2335492352 (46706212998061 / 20000)
      (233544465156409 / 100000) := by
  exact
    packedTile65536 2335361280 2335492352 14 6212 48325 31 _ _ (1078571 / 50000) (431429 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2335492352 :
    ThetaLowerSegment 2335492352 2335623424 (233544465156409 / 100000)
      (58389361177477 / 25000) := by
  exact
    packedTile65536 2335492352 2335623424 14 6017 48326 31 _ _ (2157147 / 100000) (43143 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2335623424 :
    ThetaLowerSegment 2335623424 2335754496 (58389361177477 / 25000)
      (233570359584919 / 100000) := by
  exact
    packedTile65536 2335623424 2335754496 14 5987 48328 31 _ _ (2157153 / 100000) (539289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2335754496 :
    ThetaLowerSegment 2335754496 2335885568 (233570359584919 / 100000) (4671666439067 / 2000) := by
  exact
    packedTile65536 2335754496 2335885568 14 6009 48329 31 _ _ (2157159 / 100000) (1078581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2335885568 :
    ThetaLowerSegment 2335885568 2336016640 (4671666439067 / 2000) (4671931770239 / 2000) := by
  exact
    packedTile65536 2335885568 2336016640 14 6150 48331 31 _ _ (539291 / 25000) (2157167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2336016640 :
    ThetaLowerSegment 2336016640 2336147712 (4671931770239 / 2000) (2920122838303 / 1250) := by
  exact
    packedTile65536 2336016640 2336147712 14 6137 48332 31 _ _ (215717 / 10000) (2157173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2336147712 :
    ThetaLowerSegment 2336147712 2336278784 (2920122838303 / 1250) (46724552728543 / 20000) := by
  exact
    packedTile65536 2336147712 2336278784 14 5997 48333 31 _ _ (86287 / 4000) (1078589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2336278784 :
    ThetaLowerSegment 2336278784 2336409856 (46724552728543 / 20000)
      (233635909503729 / 100000) := by
  exact
    packedTile65536 2336278784 2336409856 14 6094 48335 31 _ _ (2157181 / 100000) (67412 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2336409856 :
    ThetaLowerSegment 2336409856 2336540928 (233635909503729 / 100000)
      (233649051086933 / 100000) := by
  exact
    packedTile65536 2336409856 2336540928 14 6092 48336 31 _ _ (2157187 / 100000) (215719 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2336540928 :
    ThetaLowerSegment 2336540928 2336672000 (233649051086933 / 100000)
      (233661994238933 / 100000) := by
  exact
    packedTile65536 2336540928 2336672000 14 6000 48337 31 _ _ (269649 / 12500) (431439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2336672000 :
    ThetaLowerSegment 2336672000 2336803072 (233661994238933 / 100000) (74776017253 / 32) := by
  exact
    packedTile65536 2336672000 2336803072 14 6054 48339 31 _ _ (1078599 / 50000) (2157201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2336803072 :
    ThetaLowerSegment 2336803072 2336934144 (74776017253 / 32) (233688251683579 / 100000) := by
  exact
    packedTile65536 2336803072 2336934144 14 6118 48340 31 _ _ (2157203 / 100000) (1078603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2336934144 :
    ThetaLowerSegment 2336934144 2337065216 (233688251683579 / 100000)
      (23370140850127 / 10000) := by
  exact
    packedTile65536 2336934144 2337065216 14 6099 48341 31 _ _ (2157209 / 100000) (539303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2337065216 :
    ThetaLowerSegment 2337065216 2337196288 (23370140850127 / 10000) (46742900990707 / 20000) := by
  exact
    packedTile65536 2337065216 2337196288 14 6071 48343 31 _ _ (431443 / 20000) (1078609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2337196288 :
    ThetaLowerSegment 2337196288 2337327360 (46742900990707 / 20000) (46745508206799 / 20000) := by
  exact
    packedTile65536 2337196288 2337327360 14 6043 48344 31 _ _ (107861 / 5000) (2157223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2337327360 :
    ThetaLowerSegment 2337327360 2337458432 (46745508206799 / 20000)
      (233740572836261 / 100000) := by
  exact
    packedTile65536 2337327360 2337458432 14 6041 48345 31 _ _ (1078613 / 50000) (2157229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2337458432 :
    ThetaLowerSegment 2337458432 2337589504 (233740572836261 / 100000)
      (46750749410417 / 20000) := by
  exact
    packedTile65536 2337458432 2337589504 14 6107 48347 31 _ _ (134827 / 6250) (431447 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2337589504 :
    ThetaLowerSegment 2337589504 2337720576 (46750749410417 / 20000)
      (233766806964883 / 100000) := by
  exact
    packedTile65536 2337589504 2337720576 14 6054 48348 31 _ _ (2157237 / 100000) (53931 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2337720576 :
    ThetaLowerSegment 2337720576 2337851648 (233766806964883 / 100000)
      (233780207758399 / 100000) := by
  exact
    packedTile65536 2337720576 2337851648 14 6212 48349 31 _ _ (2157243 / 100000) (1078623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2337851648 :
    ThetaLowerSegment 2337851648 2337982720 (233780207758399 / 100000)
      (233793125359423 / 100000) := by
  exact
    packedTile65536 2337851648 2337982720 14 5988 48351 31 _ _ (67414 / 3125) (2157251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2337982720 :
    ThetaLowerSegment 2337982720 2338113792 (233793125359423 / 100000)
      (46761225857307 / 20000) := by
  exact
    packedTile65536 2337982720 2338113792 14 6028 48352 31 _ _ (1078627 / 50000) (2157257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2338113792 :
    ThetaLowerSegment 2338113792 2338244864 (46761225857307 / 20000) (9352764121927 / 4000) := by
  exact
    packedTile65536 2338113792 2338244864 14 6014 48354 31 _ _ (107863 / 5000) (2157263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2338244864 :
    ThetaLowerSegment 2338244864 2338375936 (9352764121927 / 4000) (5845808554587 / 2500) := by
  exact
    packedTile65536 2338244864 2338375936 14 6137 48355 31 _ _ (431453 / 20000) (539317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2338375936 :
    ThetaLowerSegment 2338375936 2338507008 (5845808554587 / 2500) (116922752925561 / 50000) := by
  exact
    packedTile65536 2338375936 2338507008 14 6102 48356 31 _ _ (2157271 / 100000) (1078637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2338507008 :
    ThetaLowerSegment 2338507008 2338638080 (116922752925561 / 50000)
      (116929329381447 / 50000) := by
  exact
    packedTile65536 2338507008 2338638080 14 6097 48358 31 _ _ (539319 / 25000) (2157279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2338638080 :
    ThetaLowerSegment 2338638080 2338769152 (116929329381447 / 50000) (4677438866109 / 2000) := by
  exact
    packedTile65536 2338638080 2338769152 14 6158 48359 31 _ _ (1078641 / 50000) (431457 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2338769152 :
    ThetaLowerSegment 2338769152 2338900224 (4677438866109 / 2000) (116942480190621 / 50000) := by
  exact
    packedTile65536 2338769152 2338900224 14 6034 48360 31 _ _ (269661 / 12500) (2157291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2338900224 :
    ThetaLowerSegment 2338900224 2339031296 (116942480190621 / 50000)
      (233898109082077 / 100000) := by
  exact
    packedTile65536 2338900224 2339031296 14 6095 48362 31 _ _ (2157293 / 100000) (134831 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339031296 :
    ThetaLowerSegment 2339031296 2339162368 (233898109082077 / 100000)
      (233911221145399 / 100000) := by
  exact
    packedTile65536 2339031296 2339162368 14 6078 48363 31 _ _ (2157299 / 100000) (1078651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339162368 :
    ThetaLowerSegment 2339162368 2339293440 (233911221145399 / 100000)
      (46784890809627 / 20000) := by
  exact
    packedTile65536 2339162368 2339293440 14 6134 48364 31 _ _ (269663 / 12500) (2157307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339293440 :
    ThetaLowerSegment 2339293440 2339424512 (46784890809627 / 20000) (9357501007577 / 4000) := by
  exact
    packedTile65536 2339293440 2339424512 14 6059 48366 31 _ _ (215731 / 10000) (2157313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339424512 :
    ThetaLowerSegment 2339424512 2339555584 (9357501007577 / 4000) (233950579108541 / 100000) := by
  exact
    packedTile65536 2339424512 2339555584 14 6051 48367 31 _ _ (539329 / 25000) (2157319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339555584 :
    ThetaLowerSegment 2339555584 2339686656 (233950579108541 / 100000) (7311368387032 / 3125) := by
  exact
    packedTile65536 2339555584 2339686656 14 6123 48368 31 _ _ (2157321 / 100000) (539331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339686656 :
    ThetaLowerSegment 2339686656 2339817728 (7311368387032 / 3125) (233976769021583 / 100000) := by
  exact
    packedTile65536 2339686656 2339817728 14 6017 48370 31 _ _ (2157327 / 100000) (215733 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339817728 :
    ThetaLowerSegment 2339817728 2339948800 (233976769021583 / 100000)
      (233989754002891 / 100000) := by
  exact
    packedTile65536 2339817728 2339948800 14 6019 48371 31 _ _ (539333 / 25000) (431467 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339948800 :
    ThetaLowerSegment 2339948800 2340079872 (233989754002891 / 100000)
      (234002894348649 / 100000) := by
  exact
    packedTile65536 2339948800 2340079872 14 6091 48373 31 _ _ (1078669 / 50000) (2157341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2340079872 :
    ThetaLowerSegment 2340079872 2340210944 (234002894348649 / 100000)
      (234015827625929 / 100000) := by
  exact
    packedTile65536 2340079872 2340210944 14 5995 48374 31 _ _ (67417 / 3125) (2157347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2340210944 :
    ThetaLowerSegment 2340210944 2340342016 (234015827625929 / 100000)
      (117014455973807 / 50000) := by
  exact
    packedTile65536 2340210944 2340342016 14 6065 48375 31 _ _ (2157349 / 100000) (269669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2340342016 :
    ThetaLowerSegment 2340342016 2340473088 (117014455973807 / 50000)
      (117020945297647 / 50000) := by
  exact
    packedTile65536 2340342016 2340473088 14 6016 48377 31 _ _ (431471 / 20000) (1078679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2340473088 :
    ThetaLowerSegment 2340473088 2340604160 (117020945297647 / 50000)
      (117027427085767 / 50000) := by
  exact
    packedTile65536 2340473088 2340604160 14 6009 48378 31 _ _ (26967 / 1250) (2157363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2340604160 :
    ThetaLowerSegment 2340604160 2340735232 (117027427085767 / 50000) (58516995435911 / 25000) := by
  exact
    packedTile65536 2340604160 2340735232 14 6085 48379 31 _ _ (1078683 / 50000) (2157369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2340735232 :
    ThetaLowerSegment 2340735232 2340866304 (58516995435911 / 25000) (2926015970341 / 1250) := by
  exact
    packedTile65536 2340735232 2340866304 14 6163 48381 31 _ _ (539343 / 25000) (17259 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2340866304 :
    ThetaLowerSegment 2340866304 2340997376 (2926015970341 / 1250) (117047246859391 / 50000) := by
  exact
    packedTile65536 2340866304 2340997376 14 6126 48382 31 _ _ (2157377 / 100000) (107869 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2340997376 :
    ThetaLowerSegment 2340997376 2341128448 (117047246859391 / 50000) (4682152902511 / 2000) := by
  exact
    packedTile65536 2340997376 2341128448 14 6096 48383 31 _ _ (2157383 / 100000) (1078693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2341128448 :
    ThetaLowerSegment 2341128448 2341259520 (4682152902511 / 2000) (117060387494459 / 50000) := by
  exact
    packedTile65536 2341128448 2341259520 14 6086 48385 31 _ _ (539347 / 25000) (2157391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2341259520 :
    ThetaLowerSegment 2341259520 2341390592 (117060387494459 / 50000) (58533489705913 / 25000) := by
  exact
    packedTile65536 2341259520 2341390592 14 6111 48386 31 _ _ (1078697 / 50000) (2157397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2341390592 :
    ThetaLowerSegment 2341390592 2341521664 (58533489705913 / 25000) (58536771111313 / 25000) := by
  exact
    packedTile65536 2341390592 2341521664 14 6084 48387 31 _ _ (10787 / 500) (2157403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2341521664 :
    ThetaLowerSegment 2341521664 2341652736 (58536771111313 / 25000)
      (234160315810117 / 100000) := by
  exact
    packedTile65536 2341521664 2341652736 14 6133 48389 31 _ _ (431481 / 20000) (67419 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2341652736 :
    ThetaLowerSegment 2341652736 2341783808 (234160315810117 / 100000)
      (58543360914013 / 25000) := by
  exact
    packedTile65536 2341652736 2341783808 14 6085 48390 31 _ _ (2157411 / 100000) (1078707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2341783808 :
    ThetaLowerSegment 2341783808 2341914880 (58543360914013 / 25000) (58546629399253 / 25000) := by
  exact
    packedTile65536 2341783808 2341914880 14 6060 48391 31 _ _ (269677 / 12500) (2157419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2341914880 :
    ThetaLowerSegment 2341914880 2342045952 (58546629399253 / 25000) (29274921439661 / 12500) := by
  exact
    packedTile65536 2341914880 2342045952 14 5958 48393 31 _ _ (1078711 / 50000) (86297 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2342045952 :
    ThetaLowerSegment 2342045952 2342177024 (29274921439661 / 12500) (14638272182437 / 6250) := by
  exact
    packedTile65536 2342045952 2342177024 14 6018 48394 31 _ _ (539357 / 25000) (2157431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2342177024 :
    ThetaLowerSegment 2342177024 2342308096 (14638272182437 / 6250) (58556348611011 / 25000) := by
  exact
    packedTile65536 2342177024 2342308096 14 6044 48396 31 _ _ (2157433 / 100000) (539359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2342308096 :
    ThetaLowerSegment 2342308096 2342439168 (58556348611011 / 25000) (117119305457679 / 50000) := by
  exact
    packedTile65536 2342308096 2342439168 14 6126 48397 31 _ _ (2157439 / 100000) (1078721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2342439168 :
    ThetaLowerSegment 2342439168 2342570240 (117119305457679 / 50000)
      (117125909393763 / 50000) := by
  exact
    packedTile65536 2342439168 2342570240 14 6122 48398 31 _ _ (539361 / 25000) (2157447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2342570240 :
    ThetaLowerSegment 2342570240 2342701312 (117125909393763 / 50000)
      (117132515505663 / 50000) := by
  exact
    packedTile65536 2342570240 2342701312 14 6124 48400 31 _ _ (43149 / 2000) (2157453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2342701312 :
    ThetaLowerSegment 2342701312 2342832384 (117132515505663 / 50000) (23427812461179 / 10000) := by
  exact
    packedTile65536 2342701312 2342832384 14 6069 48401 31 _ _ (134841 / 6250) (2157459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2342832384 :
    ThetaLowerSegment 2342832384 2342963456 (23427812461179 / 10000) (29286423045887 / 12500) := by
  exact
    packedTile65536 2342832384 2342963456 14 6146 48402 31 _ _ (2157461 / 100000) (269683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2342963456 :
    ThetaLowerSegment 2342963456 2343094528 (29286423045887 / 12500) (117152149482279 / 50000) := by
  exact
    packedTile65536 2342963456 2343094528 14 5986 48404 31 _ _ (2157467 / 100000) (215747 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2343094528 :
    ThetaLowerSegment 2343094528 2343225600 (117152149482279 / 50000)
      (117158710354631 / 50000) := by
  exact
    packedTile65536 2343094528 2343225600 14 6082 48405 31 _ _ (67421 / 3125) (86299 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2343225600 :
    ThetaLowerSegment 2343225600 2343356672 (117158710354631 / 50000) (58582639398201 / 25000) := by
  exact
    packedTile65536 2343225600 2343356672 14 6089 48406 31 _ _ (1078739 / 50000) (2157481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2343356672 :
    ThetaLowerSegment 2343356672 2343487744 (58582639398201 / 25000) (58585930640043 / 25000) := by
  exact
    packedTile65536 2343356672 2343487744 14 6102 48408 31 _ _ (539371 / 25000) (2157487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2343487744 :
    ThetaLowerSegment 2343487744 2343618816 (58585930640043 / 25000) (117178417889157 / 50000) := by
  exact
    packedTile65536 2343487744 2343618816 14 6078 48409 31 _ _ (2157489 / 100000) (539373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2343618816 :
    ThetaLowerSegment 2343618816 2343749888 (117178417889157 / 50000)
      (234369869205609 / 100000) := by
  exact
    packedTile65536 2343618816 2343749888 14 6041 48410 31 _ _ (431499 / 20000) (1078749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2343749888 :
    ThetaLowerSegment 2343749888 2343880960 (234369869205609 / 100000)
      (234382855198109 / 100000) := by
  exact
    packedTile65536 2343749888 2343880960 14 6019 48412 31 _ _ (863 / 40) (2157503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2343880960 :
    ThetaLowerSegment 2343880960 2344012032 (234382855198109 / 100000)
      (234395782974061 / 100000) := by
  exact
    packedTile65536 2343880960 2344012032 14 5992 48413 31 _ _ (1078753 / 50000) (2157509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344012032 :
    ThetaLowerSegment 2344012032 2344143104 (234395782974061 / 100000)
      (46881764594109 / 20000) := by
  exact
    packedTile65536 2344012032 2344143104 14 6044 48414 31 _ _ (2157511 / 100000) (1078757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344143104 :
    ThetaLowerSegment 2344143104 2344274176 (46881764594109 / 20000)
      (234421927728803 / 100000) := by
  exact
    packedTile65536 2344143104 2344274176 14 6074 48416 31 _ _ (2157517 / 100000) (26969 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344274176 :
    ThetaLowerSegment 2344274176 2344405248 (234421927728803 / 100000)
      (117217558333451 / 50000) := by
  exact
    packedTile65536 2344274176 2344405248 14 6113 48417 31 _ _ (2157523 / 100000) (1078763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344405248 :
    ThetaLowerSegment 2344405248 2344536320 (117217558333451 / 50000)
      (117224122612391 / 50000) := by
  exact
    packedTile65536 2344405248 2344536320 14 6085 48419 31 _ _ (269691 / 12500) (2157531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344536320 :
    ThetaLowerSegment 2344536320 2344667392 (117224122612391 / 50000)
      (117230582269187 / 50000) := by
  exact
    packedTile65536 2344536320 2344667392 14 5988 48420 31 _ _ (1078767 / 50000) (2157537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344667392 :
    ThetaLowerSegment 2344667392 2344798464 (117230582269187 / 50000)
      (117237227489307 / 50000) := by
  exact
    packedTile65536 2344667392 2344798464 14 6160 48421 31 _ _ (2157539 / 100000) (1078771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344798464 :
    ThetaLowerSegment 2344798464 2344929536 (117237227489307 / 50000)
      (117243656973407 / 50000) := by
  exact
    packedTile65536 2344798464 2344929536 14 5960 48423 31 _ _ (431509 / 20000) (539387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344929536 :
    ThetaLowerSegment 2344929536 2345060608 (117243656973407 / 50000)
      (234500300246283 / 100000) := by
  exact
    packedTile65536 2344929536 2345060608 14 6019 48424 31 _ _ (2157551 / 100000) (1078777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345060608 :
    ThetaLowerSegment 2345060608 2345191680 (234500300246283 / 100000)
      (234513485070999 / 100000) := by
  exact
    packedTile65536 2345060608 2345191680 14 6111 48425 31 _ _ (539389 / 25000) (2157559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345191680 :
    ThetaLowerSegment 2345191680 2345322752 (234513485070999 / 100000)
      (234526779968043 / 100000) := by
  exact
    packedTile65536 2345191680 2345322752 14 6162 48427 31 _ _ (1078781 / 50000) (431513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345322752 :
    ThetaLowerSegment 2345322752 2345339136 (234526779968043 / 100000)
      (58632104390349 / 25000) := by
  exact
    packedTile65536 2345322752 2345339136 11 759 48428 31 _ _ (2157567 / 100000) (215757 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2345339136 :
    ThetaLowerSegment 2345339136 2345341184 (58632104390349 / 25000) (11726432528937 / 5000) := by
  exact
    packedTile65536 2345339136 2345341184 8 108 48428 31 _ _ (67424 / 3125) (2157571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2313341184_2345341184 :
    ThetaLowerSegment 2313341184 2345341184 (115664835976187 / 50000) (11726432528937 / 5000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2313341184 cell2313472256)
                  (ThetaLowerSegment.join cell2313603328 cell2313734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2313865472 cell2313996544)
                  (ThetaLowerSegment.join cell2314127616 cell2314258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2314389760 cell2314520832)
                  (ThetaLowerSegment.join cell2314651904 cell2314782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2314914048 cell2315045120)
                  (ThetaLowerSegment.join cell2315176192 cell2315307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2315438336 cell2315569408)
                  (ThetaLowerSegment.join cell2315700480 cell2315831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2315962624 cell2316093696)
                  (ThetaLowerSegment.join cell2316224768 cell2316355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2316486912 cell2316617984)
                  (ThetaLowerSegment.join cell2316749056 cell2316880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2317011200 cell2317142272)
                  (ThetaLowerSegment.join cell2317273344 cell2317404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2317535488 cell2317666560)
                  (ThetaLowerSegment.join cell2317797632 cell2317928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2318059776 cell2318190848)
                  (ThetaLowerSegment.join cell2318321920 cell2318452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2318584064 cell2318715136)
                  (ThetaLowerSegment.join cell2318846208 cell2318977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2319108352 cell2319239424)
                  (ThetaLowerSegment.join cell2319370496 cell2319501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2319632640 cell2319763712)
                  (ThetaLowerSegment.join cell2319894784 cell2320025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2320156928 cell2320288000)
                  (ThetaLowerSegment.join cell2320419072 cell2320550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2320681216 cell2320812288)
                  (ThetaLowerSegment.join cell2320943360 cell2321074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2321205504 cell2321336576)
                  (ThetaLowerSegment.join cell2321467648 cell2321598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2321729792 cell2321860864)
                  (ThetaLowerSegment.join cell2321991936 cell2322123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2322254080 cell2322385152)
                  (ThetaLowerSegment.join cell2322516224 cell2322647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2322778368 cell2322909440)
                  (ThetaLowerSegment.join cell2323040512 cell2323171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2323302656 cell2323433728)
                  (ThetaLowerSegment.join cell2323564800 cell2323695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2323826944 cell2323958016)
                  (ThetaLowerSegment.join cell2324089088 cell2324220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2324351232 cell2324482304)
                  (ThetaLowerSegment.join cell2324613376 cell2324744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2324875520 cell2325006592)
                  (ThetaLowerSegment.join cell2325137664 cell2325268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2325399808 cell2325530880)
                  (ThetaLowerSegment.join cell2325661952 cell2325793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2325924096 cell2326055168)
                  (ThetaLowerSegment.join cell2326186240 cell2326317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2326448384 cell2326579456)
                  (ThetaLowerSegment.join cell2326710528 cell2326841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2326972672 cell2327103744)
                  (ThetaLowerSegment.join cell2327234816 cell2327365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2327496960 cell2327628032)
                  (ThetaLowerSegment.join cell2327759104 cell2327890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2328021248 cell2328152320)
                  (ThetaLowerSegment.join cell2328283392 cell2328414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2328545536 cell2328676608)
                  (ThetaLowerSegment.join cell2328807680 cell2328938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2329069824 cell2329200896)
                  (ThetaLowerSegment.join cell2329331968 cell2329463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2329594112 cell2329725184)
                  (ThetaLowerSegment.join cell2329856256 cell2329987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2330118400 cell2330249472)
                  (ThetaLowerSegment.join cell2330380544 cell2330511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2330642688 cell2330773760)
                  (ThetaLowerSegment.join cell2330904832 cell2331035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2331166976 cell2331298048)
                  (ThetaLowerSegment.join cell2331429120 cell2331560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2331691264 cell2331822336)
                  (ThetaLowerSegment.join cell2331953408 cell2332084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2332215552 cell2332346624)
                  (ThetaLowerSegment.join cell2332477696 cell2332608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2332739840 cell2332870912)
                  (ThetaLowerSegment.join cell2333001984 cell2333133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2333264128 cell2333395200)
                  (ThetaLowerSegment.join cell2333526272 cell2333657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2333788416 cell2333919488)
                  (ThetaLowerSegment.join cell2334050560 cell2334181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2334312704 cell2334443776)
                  (ThetaLowerSegment.join cell2334574848 cell2334705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2334836992 cell2334968064)
                  (ThetaLowerSegment.join cell2335099136 cell2335230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2335361280 cell2335492352)
                  (ThetaLowerSegment.join cell2335623424 cell2335754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2335885568 cell2336016640)
                  (ThetaLowerSegment.join cell2336147712 cell2336278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2336409856 cell2336540928)
                  (ThetaLowerSegment.join cell2336672000 cell2336803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2336934144 cell2337065216)
                  (ThetaLowerSegment.join cell2337196288 cell2337327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2337458432 cell2337589504)
                  (ThetaLowerSegment.join cell2337720576 cell2337851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2337982720 cell2338113792)
                  (ThetaLowerSegment.join cell2338244864 cell2338375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2338507008 cell2338638080)
                  (ThetaLowerSegment.join cell2338769152 cell2338900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2339031296 cell2339162368)
                  (ThetaLowerSegment.join cell2339293440 cell2339424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2339555584 cell2339686656)
                  (ThetaLowerSegment.join cell2339817728 cell2339948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2340079872 cell2340210944)
                  (ThetaLowerSegment.join cell2340342016 cell2340473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2340604160 cell2340735232)
                  (ThetaLowerSegment.join cell2340866304 cell2340997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2341128448 cell2341259520)
                  (ThetaLowerSegment.join cell2341390592 cell2341521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2341652736 cell2341783808)
                  (ThetaLowerSegment.join cell2341914880 cell2342045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2342177024 cell2342308096)
                  (ThetaLowerSegment.join cell2342439168 cell2342570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2342701312 cell2342832384)
                  (ThetaLowerSegment.join cell2342963456 cell2343094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2343225600 cell2343356672)
                  (ThetaLowerSegment.join cell2343487744 cell2343618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2343749888 cell2343880960)
                  (ThetaLowerSegment.join cell2344012032 cell2344143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2344274176 cell2344405248)
                  (ThetaLowerSegment.join cell2344536320 cell2344667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2344798464 cell2344929536)
                (ThetaLowerSegment.join cell2345060608 cell2345191680))
              (ThetaLowerSegment.join cell2345322752 cell2345339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
