/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2633341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2601341184 :
    ThetaLowerSegment 2601341184 2601472256 (325163039859 / 125) (32517916111359 / 12500) := by
  exact
    packedTile65536 2601341184 2601472256 14 5949 51003 31 _ _ (270991 / 12500) (2167931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601472256 :
    ThetaLowerSegment 2601472256 2601603328 (32517916111359 / 12500)
      (260156477404517 / 100000) := by
  exact
    packedTile65536 2601472256 2601603328 14 6065 51004 31 _ _ (2167933 / 100000) (67748 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601603328 :
    ThetaLowerSegment 2601603328 2601734400 (260156477404517 / 100000)
      (260169821062907 / 100000) := by
  exact
    packedTile65536 2601603328 2601734400 14 6155 51005 31 _ _ (1083969 / 50000) (2167941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601734400 :
    ThetaLowerSegment 2601734400 2601865472 (260169821062907 / 100000)
      (130091419780311 / 50000) := by
  exact
    packedTile65536 2601734400 2601865472 14 6005 51007 31 _ _ (2167943 / 100000) (1083973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601865472 :
    ThetaLowerSegment 2601865472 2601996544 (130091419780311 / 50000)
      (130097966983271 / 50000) := by
  exact
    packedTile65536 2601865472 2601996544 14 6040 51008 31 _ _ (541987 / 25000) (2167951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601996544 :
    ThetaLowerSegment 2601996544 2602127616 (130097966983271 / 50000) (52041823457747 / 20000) := by
  exact
    packedTile65536 2601996544 2602127616 14 6081 51009 31 _ _ (2167953 / 100000) (541989 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2602127616 :
    ThetaLowerSegment 2602127616 2602258688 (52041823457747 / 20000)
      (260222142380399 / 100000) := by
  exact
    packedTile65536 2602127616 2602258688 14 6008 51011 31 _ _ (1083979 / 50000) (2167961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2602258688 :
    ThetaLowerSegment 2602258688 2602389760 (260222142380399 / 100000)
      (65058843364647 / 25000) := by
  exact
    packedTile65536 2602258688 2602389760 14 6103 51012 31 _ _ (2167963 / 100000) (1083983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2602389760 :
    ThetaLowerSegment 2602389760 2602520832 (65058843364647 / 25000) (65062129462143 / 25000) := by
  exact
    packedTile65536 2602389760 2602520832 14 6063 51013 31 _ _ (67749 / 3125) (2167971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2602520832 :
    ThetaLowerSegment 2602520832 2602651904 (65062129462143 / 25000)
      (260261536526437 / 100000) := by
  exact
    packedTile65536 2602520832 2602651904 14 6005 51014 31 _ _ (2167973 / 100000) (270997 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2602651904 :
    ThetaLowerSegment 2602651904 2602782976 (260261536526437 / 100000)
      (52054924488329 / 20000) := by
  exact
    packedTile65536 2602651904 2602782976 14 6036 51016 31 _ _ (1083989 / 50000) (2167981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2602782976 :
    ThetaLowerSegment 2602782976 2602914048 (52054924488329 / 20000) (130143792406001 / 50000) := by
  exact
    packedTile65536 2602782976 2602914048 14 5979 51017 31 _ _ (2167983 / 100000) (1083993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2602914048 :
    ThetaLowerSegment 2602914048 2603045120 (130143792406001 / 50000)
      (130150257346217 / 50000) := by
  exact
    packedTile65536 2602914048 2603045120 14 5964 51018 31 _ _ (541997 / 25000) (2167991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2603045120 :
    ThetaLowerSegment 2603045120 2603176192 (130150257346217 / 50000)
      (260313394738847 / 100000) := by
  exact
    packedTile65536 2603045120 2603176192 14 5941 51020 31 _ _ (2167993 / 100000) (541999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2603176192 :
    ThetaLowerSegment 2603176192 2603307264 (260313394738847 / 100000)
      (260326498118759 / 100000) := by
  exact
    packedTile65536 2603176192 2603307264 14 6044 51021 31 _ _ (1083999 / 50000) (2168001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2603307264 :
    ThetaLowerSegment 2603307264 2603438336 (260326498118759 / 100000)
      (65084897672219 / 25000) := by
  exact
    packedTile65536 2603307264 2603438336 14 6039 51022 31 _ _ (2168003 / 100000) (1084003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2603438336 :
    ThetaLowerSegment 2603438336 2603569408 (65084897672219 / 25000) (65088181662337 / 25000) := by
  exact
    packedTile65536 2603438336 2603569408 14 6059 51023 31 _ _ (271001 / 12500) (2168011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2603569408 :
    ThetaLowerSegment 2603569408 2603700480 (65088181662337 / 25000) (65091507394279 / 25000) := by
  exact
    packedTile65536 2603569408 2603700480 14 6136 51025 31 _ _ (2168013 / 100000) (135501 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2603700480 :
    ThetaLowerSegment 2603700480 2603831552 (65091507394279 / 25000) (65094772429387 / 25000) := by
  exact
    packedTile65536 2603700480 2603831552 14 6024 51026 31 _ _ (1084009 / 50000) (2168021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2603831552 :
    ThetaLowerSegment 2603831552 2603962624 (65094772429387 / 25000)
      (260392238777043 / 100000) := by
  exact
    packedTile65536 2603831552 2603962624 14 6065 51027 31 _ _ (2168023 / 100000) (1084013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2603962624 :
    ThetaLowerSegment 2603962624 2604093696 (260392238777043 / 100000)
      (65101357808377 / 25000) := by
  exact
    packedTile65536 2603962624 2604093696 14 6085 51029 31 _ _ (2168029 / 100000) (67751 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2604093696 :
    ThetaLowerSegment 2604093696 2604224768 (65101357808377 / 25000) (130209275003621 / 50000) := by
  exact
    packedTile65536 2604093696 2604224768 14 6051 51030 31 _ _ (1084017 / 50000) (2168037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2604224768 :
    ThetaLowerSegment 2604224768 2604355840 (130209275003621 / 50000) (32553958330399 / 12500) := by
  exact
    packedTile65536 2604224768 2604355840 14 6050 51031 31 _ _ (2168039 / 100000) (1084021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2604355840 :
    ThetaLowerSegment 2604355840 2604486912 (32553958330399 / 12500) (32555615800037 / 12500) := by
  exact
    packedTile65536 2604355840 2604486912 14 6116 51032 31 _ _ (542011 / 25000) (2168047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2604486912 :
    ThetaLowerSegment 2604486912 2604617984 (32555615800037 / 12500)
      (260458079953579 / 100000) := by
  exact
    packedTile65536 2604486912 2604617984 14 6067 51034 31 _ _ (2168049 / 100000) (542013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2604617984 :
    ThetaLowerSegment 2604617984 2604749056 (260458079953579 / 100000)
      (52094251910769 / 20000) := by
  exact
    packedTile65536 2604617984 2604749056 14 6079 51035 31 _ _ (1084027 / 50000) (2168057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2604749056 :
    ThetaLowerSegment 2604749056 2604880128 (52094251910769 / 20000)
      (260484350294087 / 100000) := by
  exact
    packedTile65536 2604749056 2604880128 14 6038 51036 31 _ _ (2168059 / 100000) (1084031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2604880128 :
    ThetaLowerSegment 2604880128 2605011200 (260484350294087 / 100000)
      (260497386862919 / 100000) := by
  exact
    packedTile65536 2604880128 2605011200 14 6013 51038 31 _ _ (67752 / 3125) (2168067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2605011200 :
    ThetaLowerSegment 2605011200 2605142272 (260497386862919 / 100000)
      (65127629714213 / 25000) := by
  exact
    packedTile65536 2605011200 2605142272 14 6057 51039 31 _ _ (2168069 / 100000) (271009 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2605142272 :
    ThetaLowerSegment 2605142272 2605273344 (65127629714213 / 25000) (26052360751959 / 10000) := by
  exact
    packedTile65536 2605142272 2605273344 14 6037 51040 31 _ _ (1084037 / 50000) (2168077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2605273344 :
    ThetaLowerSegment 2605273344 2605404416 (26052360751959 / 10000) (65134185435543 / 25000) := by
  exact
    packedTile65536 2605273344 2605404416 14 6058 51041 31 _ _ (2168079 / 100000) (1084041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2605404416 :
    ThetaLowerSegment 2605404416 2605535488 (65134185435543 / 25000) (16284353021639 / 6250) := by
  exact
    packedTile65536 2605404416 2605535488 14 5953 51043 31 _ _ (542021 / 25000) (2168087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2605535488 :
    ThetaLowerSegment 2605535488 2605666560 (16284353021639 / 6250) (32570342950473 / 12500) := by
  exact
    packedTile65536 2605535488 2605666560 14 6040 51044 31 _ _ (2168089 / 100000) (542023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2605666560 :
    ThetaLowerSegment 2605666560 2605797632 (32570342950473 / 12500) (65143932621711 / 25000) := by
  exact
    packedTile65536 2605666560 2605797632 14 5990 51045 31 _ _ (1084047 / 50000) (2168097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2605797632 :
    ThetaLowerSegment 2605797632 2605928704 (65143932621711 / 25000) (26058889952017 / 10000) := by
  exact
    packedTile65536 2605797632 2605928704 14 6074 51047 31 _ _ (2168099 / 100000) (1084051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2605928704 :
    ThetaLowerSegment 2605928704 2606059776 (26058889952017 / 10000) (130301074401857 / 50000) := by
  exact
    packedTile65536 2605928704 2606059776 14 6111 51048 31 _ _ (271013 / 12500) (2168107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606059776 :
    ThetaLowerSegment 2606059776 2606190848 (130301074401857 / 50000) (52123061411447 / 20000) := by
  exact
    packedTile65536 2606059776 2606190848 14 6069 51049 31 _ _ (2168109 / 100000) (135507 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606190848 :
    ThetaLowerSegment 2606190848 2606321920 (52123061411447 / 20000)
      (260628298396323 / 100000) := by
  exact
    packedTile65536 2606190848 2606321920 14 5992 51050 31 _ _ (1084057 / 50000) (2168117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606321920 :
    ThetaLowerSegment 2606321920 2606452992 (260628298396323 / 100000) (13032072185091 / 5000) := by
  exact
    packedTile65536 2606321920 2606452992 14 6063 51052 31 _ _ (2168119 / 100000) (1084061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606452992 :
    ThetaLowerSegment 2606452992 2606584064 (13032072185091 / 5000) (65163631540509 / 25000) := by
  exact
    packedTile65536 2606452992 2606584064 14 6034 51053 31 _ _ (542031 / 25000) (2168127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606584064 :
    ThetaLowerSegment 2606584064 2606715136 (65163631540509 / 25000) (130333769636147 / 50000) := by
  exact
    packedTile65536 2606584064 2606715136 14 6002 51054 31 _ _ (2168129 / 100000) (542033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606715136 :
    ThetaLowerSegment 2606715136 2606846208 (130333769636147 / 50000) (8146269227764 / 3125) := by
  exact
    packedTile65536 2606715136 2606846208 14 6031 51056 31 _ _ (1084067 / 50000) (2168137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606846208 :
    ThetaLowerSegment 2606846208 2606977280 (8146269227764 / 3125) (260693925493769 / 100000) := by
  exact
    packedTile65536 2606846208 2606977280 14 6139 51057 31 _ _ (2168139 / 100000) (1084071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606977280 :
    ThetaLowerSegment 2606977280 2607108352 (260693925493769 / 100000) (2085655457517 / 800) := by
  exact
    packedTile65536 2606977280 2607108352 14 5999 51058 31 _ _ (135509 / 6250) (2168147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2607108352 :
    ThetaLowerSegment 2607108352 2607239424 (2085655457517 / 800) (52143979544129 / 20000) := by
  exact
    packedTile65536 2607108352 2607239424 14 5980 51059 31 _ _ (2168149 / 100000) (271019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2607239424 :
    ThetaLowerSegment 2607239424 2607370496 (52143979544129 / 20000)
      (260732986866343 / 100000) := by
  exact
    packedTile65536 2607239424 2607370496 14 6037 51061 31 _ _ (1084077 / 50000) (2168157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2607370496 :
    ThetaLowerSegment 2607370496 2607501568 (260732986866343 / 100000)
      (130372964303707 / 50000) := by
  exact
    packedTile65536 2607370496 2607501568 14 5969 51062 31 _ _ (2168159 / 100000) (1084081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2607501568 :
    ThetaLowerSegment 2607501568 2607632640 (130372964303707 / 50000)
      (130379504570413 / 50000) := by
  exact
    packedTile65536 2607501568 2607632640 14 6033 51063 31 _ _ (542041 / 25000) (2168167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2607632640 :
    ThetaLowerSegment 2607632640 2607763712 (130379504570413 / 50000)
      (260771963950601 / 100000) := by
  exact
    packedTile65536 2607632640 2607763712 14 5975 51064 31 _ _ (2168169 / 100000) (542043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2607763712 :
    ThetaLowerSegment 2607763712 2607894784 (260771963950601 / 100000)
      (260785189812001 / 100000) := by
  exact
    packedTile65536 2607763712 2607894784 14 6100 51066 31 _ _ (1084087 / 50000) (2168177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2607894784 :
    ThetaLowerSegment 2607894784 2608025856 (260785189812001 / 100000)
      (260798285613161 / 100000) := by
  exact
    packedTile65536 2607894784 2608025856 14 6040 51067 31 _ _ (2168179 / 100000) (1084091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2608025856 :
    ThetaLowerSegment 2608025856 2608156928 (260798285613161 / 100000)
      (260811413967281 / 100000) := by
  exact
    packedTile65536 2608025856 2608156928 14 6055 51068 31 _ _ (271023 / 12500) (2168187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2608156928 :
    ThetaLowerSegment 2608156928 2608288000 (260811413967281 / 100000)
      (260824518501597 / 100000) := by
  exact
    packedTile65536 2608156928 2608288000 14 6044 51070 31 _ _ (2168189 / 100000) (67756 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2608288000 :
    ThetaLowerSegment 2608288000 2608419072 (260824518501597 / 100000)
      (260837666430013 / 100000) := by
  exact
    packedTile65536 2608288000 2608419072 14 6064 51071 31 _ _ (1084097 / 50000) (2168197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2608419072 :
    ThetaLowerSegment 2608419072 2608550144 (260837666430013 / 100000)
      (260850526024213 / 100000) := by
  exact
    packedTile65536 2608419072 2608550144 14 5931 51072 31 _ _ (10841 / 500) (2168203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2608550144 :
    ThetaLowerSegment 2608550144 2608681216 (260850526024213 / 100000)
      (130431872785049 / 50000) := by
  exact
    packedTile65536 2608550144 2608681216 14 6097 51073 31 _ _ (433641 / 20000) (135513 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2608681216 :
    ThetaLowerSegment 2608681216 2608812288 (130431872785049 / 50000)
      (130438479320919 / 50000) := by
  exact
    packedTile65536 2608681216 2608812288 14 6094 51075 31 _ _ (216821 / 10000) (2168213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2608812288 :
    ThetaLowerSegment 2608812288 2608943360 (130438479320919 / 50000) (32611251954071 / 12500) := by
  exact
    packedTile65536 2608812288 2608943360 14 6022 51076 31 _ _ (433643 / 20000) (1084109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2608943360 :
    ThetaLowerSegment 2608943360 2609074432 (32611251954071 / 12500) (32612904137711 / 12500) := by
  exact
    packedTile65536 2608943360 2609074432 14 6096 51077 31 _ _ (108411 / 5000) (2168223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2609074432 :
    ThetaLowerSegment 2609074432 2609205504 (32612904137711 / 12500)
      (260916231610563 / 100000) := by
  exact
    packedTile65536 2609074432 2609205504 14 5995 51079 31 _ _ (86729 / 4000) (542057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2609205504 :
    ThetaLowerSegment 2609205504 2609336576 (260916231610563 / 100000)
      (260929223644723 / 100000) := by
  exact
    packedTile65536 2609205504 2609336576 14 5992 51080 31 _ _ (216823 / 10000) (2168233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2609336576 :
    ThetaLowerSegment 2609336576 2609467648 (260929223644723 / 100000)
      (260942389167643 / 100000) := by
  exact
    packedTile65536 2609336576 2609467648 14 6072 51081 31 _ _ (433647 / 20000) (1084119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2609467648 :
    ThetaLowerSegment 2609467648 2609598720 (260942389167643 / 100000)
      (260955400775883 / 100000) := by
  exact
    packedTile65536 2609467648 2609598720 14 6001 51082 31 _ _ (27103 / 1250) (2168243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2609598720 :
    ThetaLowerSegment 2609598720 2609729792 (260955400775883 / 100000)
      (65242096598797 / 25000) := by
  exact
    packedTile65536 2609598720 2609729792 14 5989 51084 31 _ _ (433649 / 20000) (271031 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2609729792 :
    ThetaLowerSegment 2609729792 2609860864 (65242096598797 / 25000) (130490722882469 / 50000) := by
  exact
    packedTile65536 2609729792 2609860864 14 6023 51085 31 _ _ (8673 / 400) (2168253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2609860864 :
    ThetaLowerSegment 2609860864 2609991936 (130490722882469 / 50000)
      (130497318714179 / 50000) := by
  exact
    packedTile65536 2609860864 2609991936 14 6084 51086 31 _ _ (433651 / 20000) (1084129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2609991936 :
    ThetaLowerSegment 2609991936 2610123008 (130497318714179 / 50000)
      (130503893962629 / 50000) := by
  exact
    packedTile65536 2609991936 2610123008 14 6065 51088 31 _ _ (108413 / 5000) (2168263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2610123008 :
    ThetaLowerSegment 2610123008 2610254080 (130503893962629 / 50000) (8156905749564 / 3125) := by
  exact
    packedTile65536 2610123008 2610254080 14 6086 51089 31 _ _ (433653 / 20000) (542067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2610254080 :
    ThetaLowerSegment 2610254080 2610385152 (8156905749564 / 3125) (8157317720864 / 3125) := by
  exact
    packedTile65536 2610254080 2610385152 14 6080 51090 31 _ _ (216827 / 10000) (2168273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2610385152 :
    ThetaLowerSegment 2610385152 2610516224 (8157317720864 / 3125) (32630903594531 / 12500) := by
  exact
    packedTile65536 2610385152 2610516224 14 6024 51091 31 _ _ (86731 / 4000) (1084139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2610516224 :
    ThetaLowerSegment 2610516224 2610647296 (32630903594531 / 12500) (8158135906829 / 3125) := by
  exact
    packedTile65536 2610516224 2610647296 14 6051 51093 31 _ _ (54207 / 2500) (2168283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2610647296 :
    ThetaLowerSegment 2610647296 2610778368 (8158135906829 / 3125) (261073577725313 / 100000) := by
  exact
    packedTile65536 2610647296 2610778368 14 6101 51094 31 _ _ (433657 / 20000) (67759 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2610778368 :
    ThetaLowerSegment 2610778368 2610909440 (261073577725313 / 100000)
      (261086600475053 / 100000) := by
  exact
    packedTile65536 2610778368 2610909440 14 6006 51095 31 _ _ (216829 / 10000) (2168293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2610909440 :
    ThetaLowerSegment 2610909440 2611040512 (261086600475053 / 100000)
      (65274898766747 / 25000) := by
  exact
    packedTile65536 2610909440 2611040512 14 5993 51097 31 _ _ (433659 / 20000) (1084149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2611040512 :
    ThetaLowerSegment 2611040512 2611171584 (65274898766747 / 25000) (32639110572211 / 12500) := by
  exact
    packedTile65536 2611040512 2611171584 14 6129 51098 31 _ _ (21683 / 1000) (2168303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2611171584 :
    ThetaLowerSegment 2611171584 2611302656 (32639110572211 / 12500)
      (261126022337683 / 100000) := by
  exact
    packedTile65536 2611171584 2611302656 14 6059 51099 31 _ _ (433661 / 20000) (542077 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2611302656 :
    ThetaLowerSegment 2611302656 2611433728 (261126022337683 / 100000)
      (261139123266703 / 100000) := by
  exact
    packedTile65536 2611302656 2611433728 14 6042 51100 31 _ _ (216831 / 10000) (2168313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2611433728 :
    ThetaLowerSegment 2611433728 2611564800 (261139123266703 / 100000)
      (261152176523003 / 100000) := by
  exact
    packedTile65536 2611433728 2611564800 14 6020 51102 31 _ _ (433663 / 20000) (1084159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2611564800 :
    ThetaLowerSegment 2611564800 2611695872 (261152176523003 / 100000)
      (261165368581883 / 100000) := by
  exact
    packedTile65536 2611564800 2611695872 14 6084 51103 31 _ _ (13552 / 625) (2168323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2611695872 :
    ThetaLowerSegment 2611695872 2611826944 (261165368581883 / 100000)
      (261178404551783 / 100000) := by
  exact
    packedTile65536 2611695872 2611826944 14 6012 51104 31 _ _ (86733 / 4000) (271041 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2611826944 :
    ThetaLowerSegment 2611826944 2611958016 (261178404551783 / 100000)
      (261191614018143 / 100000) := by
  exact
    packedTile65536 2611826944 2611958016 14 6092 51106 31 _ _ (216833 / 10000) (2168333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2611958016 :
    ThetaLowerSegment 2611958016 2612089088 (261191614018143 / 100000)
      (65301127276597 / 25000) := by
  exact
    packedTile65536 2611958016 2612089088 14 5947 51107 31 _ _ (433667 / 20000) (1084169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2612089088 :
    ThetaLowerSegment 2612089088 2612220160 (65301127276597 / 25000) (65304399301657 / 25000) := by
  exact
    packedTile65536 2612089088 2612220160 14 6036 51108 31 _ _ (108417 / 5000) (2168343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2612220160 :
    ThetaLowerSegment 2612220160 2612351232 (65304399301657 / 25000)
      (261230691842083 / 100000) := by
  exact
    packedTile65536 2612220160 2612351232 14 6039 51109 31 _ _ (433669 / 20000) (542087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2612351232 :
    ThetaLowerSegment 2612351232 2612482304 (261230691842083 / 100000)
      (261243840716483 / 100000) := by
  exact
    packedTile65536 2612351232 2612482304 14 6064 51111 31 _ _ (43367 / 2000) (2168353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2612482304 :
    ThetaLowerSegment 2612482304 2612613376 (261243840716483 / 100000)
      (130628409160579 / 50000) := by
  exact
    packedTile65536 2612482304 2612613376 14 5985 51112 31 _ _ (433671 / 20000) (1084179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2612613376 :
    ThetaLowerSegment 2612613376 2612744448 (130628409160579 / 50000)
      (130634989048999 / 50000) := by
  exact
    packedTile65536 2612613376 2612744448 14 6069 51113 31 _ _ (54209 / 2500) (2168363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2612744448 :
    ThetaLowerSegment 2612744448 2612875520 (130634989048999 / 50000)
      (261283064180773 / 100000) := by
  exact
    packedTile65536 2612744448 2612875520 14 6035 51115 31 _ _ (433673 / 20000) (135523 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2612875520 :
    ThetaLowerSegment 2612875520 2613006592 (261283064180773 / 100000)
      (261296265217333 / 100000) := by
  exact
    packedTile65536 2612875520 2613006592 14 6088 51116 31 _ _ (216837 / 10000) (2168373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2613006592 :
    ThetaLowerSegment 2613006592 2613137664 (261296265217333 / 100000)
      (130654627975979 / 50000) := by
  exact
    packedTile65536 2613006592 2613137664 14 5991 51117 31 _ _ (17347 / 800) (1084189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2613137664 :
    ThetaLowerSegment 2613137664 2613268736 (130654627975979 / 50000)
      (130661224187939 / 50000) := by
  exact
    packedTile65536 2613137664 2613268736 14 6084 51118 31 _ _ (108419 / 5000) (2168383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2613268736 :
    ThetaLowerSegment 2613268736 2613399808 (130661224187939 / 50000)
      (261335660345683 / 100000) := by
  exact
    packedTile65536 2613268736 2613399808 14 6093 51120 31 _ _ (433677 / 20000) (542097 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2613399808 :
    ThetaLowerSegment 2613399808 2613530880 (261335660345683 / 100000)
      (261348759589673 / 100000) := by
  exact
    packedTile65536 2613399808 2613530880 14 6041 51121 31 _ _ (216839 / 10000) (2168393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2613530880 :
    ThetaLowerSegment 2613530880 2613661952 (261348759589673 / 100000)
      (261361986799173 / 100000) := by
  exact
    packedTile65536 2613530880 2613661952 14 6100 51122 31 _ _ (433679 / 20000) (1084199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2613661952 :
    ThetaLowerSegment 2613661952 2613793024 (261361986799173 / 100000)
      (261374908294773 / 100000) := by
  exact
    packedTile65536 2613661952 2613793024 14 5959 51123 31 _ _ (5421 / 250) (2168403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2613793024 :
    ThetaLowerSegment 2613793024 2613924096 (261374908294773 / 100000)
      (261388196280613 / 100000) := by
  exact
    packedTile65536 2613793024 2613924096 14 6128 51125 31 _ _ (433681 / 20000) (271051 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2613924096 :
    ThetaLowerSegment 2613924096 2614055168 (261388196280613 / 100000)
      (261401447434123 / 100000) := by
  exact
    packedTile65536 2613924096 2614055168 14 6111 51126 31 _ _ (216841 / 10000) (2168413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614055168 :
    ThetaLowerSegment 2614055168 2614186240 (261401447434123 / 100000)
      (261414466597783 / 100000) := by
  exact
    packedTile65536 2614055168 2614186240 14 6004 51127 31 _ _ (433683 / 20000) (1084209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614186240 :
    ThetaLowerSegment 2614186240 2614317312 (261414466597783 / 100000)
      (261427377370463 / 100000) := by
  exact
    packedTile65536 2614186240 2614317312 14 5954 51129 31 _ _ (108421 / 5000) (2168423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614317312 :
    ThetaLowerSegment 2614317312 2614448384 (261427377370463 / 100000)
      (32680074782211 / 12500) := by
  exact
    packedTile65536 2614317312 2614448384 14 6097 51130 31 _ _ (86737 / 4000) (542107 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614448384 :
    ThetaLowerSegment 2614448384 2614579456 (32680074782211 / 12500) (130726785987189 / 50000) := by
  exact
    packedTile65536 2614448384 2614579456 14 5983 51131 31 _ _ (216843 / 10000) (2168433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614579456 :
    ThetaLowerSegment 2614579456 2614710528 (130726785987189 / 50000)
      (130733273944709 / 50000) := by
  exact
    packedTile65536 2614579456 2614710528 14 5984 51132 31 _ _ (433687 / 20000) (1084219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614710528 :
    ThetaLowerSegment 2614710528 2614841600 (130733273944709 / 50000)
      (130739838896809 / 50000) := by
  exact
    packedTile65536 2614710528 2614841600 14 6055 51134 31 _ _ (54211 / 2500) (2168443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614841600 :
    ThetaLowerSegment 2614841600 2614972672 (130739838896809 / 50000)
      (261492786043643 / 100000) := by
  exact
    packedTile65536 2614841600 2614972672 14 6045 51135 31 _ _ (433689 / 20000) (67764 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614972672 :
    ThetaLowerSegment 2614972672 2615103744 (261492786043643 / 100000)
      (261506004914843 / 100000) := by
  exact
    packedTile65536 2614972672 2615103744 14 6096 51136 31 _ _ (43369 / 2000) (2168453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2615103744 :
    ThetaLowerSegment 2615103744 2615234816 (261506004914843 / 100000)
      (261518790125523 / 100000) := by
  exact
    packedTile65536 2615103744 2615234816 14 5896 51138 31 _ _ (433691 / 20000) (1084229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2615234816 :
    ThetaLowerSegment 2615234816 2615365888 (261518790125523 / 100000)
      (261532143502203 / 100000) := by
  exact
    packedTile65536 2615234816 2615365888 14 6158 51139 31 _ _ (108423 / 5000) (2168463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2615365888 :
    ThetaLowerSegment 2615365888 2615496960 (261532143502203 / 100000)
      (261545241030803 / 100000) := by
  exact
    packedTile65536 2615365888 2615496960 14 6040 51140 31 _ _ (433693 / 20000) (542117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2615496960 :
    ThetaLowerSegment 2615496960 2615628032 (261545241030803 / 100000)
      (261558431833813 / 100000) := by
  exact
    packedTile65536 2615496960 2615628032 14 6083 51141 31 _ _ (216847 / 10000) (2168473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2615628032 :
    ThetaLowerSegment 2615628032 2615759104 (261558431833813 / 100000)
      (261571514249521 / 100000) := by
  exact
    packedTile65536 2615628032 2615759104 14 6033 51143 31 _ _ (542119 / 25000) (2168479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2615759104 :
    ThetaLowerSegment 2615759104 2615890176 (261571514249521 / 100000)
      (261584564168179 / 100000) := by
  exact
    packedTile65536 2615759104 2615890176 14 6018 51144 31 _ _ (2168481 / 100000) (542121 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2615890176 :
    ThetaLowerSegment 2615890176 2616021248 (261584564168179 / 100000)
      (261597553399319 / 100000) := by
  exact
    packedTile65536 2615890176 2616021248 14 5990 51145 31 _ _ (1084243 / 50000) (2168489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2616021248 :
    ThetaLowerSegment 2616021248 2616152320 (261597553399319 / 100000)
      (26161078336291 / 10000) := by
  exact
    packedTile65536 2616021248 2616152320 14 6101 51147 31 _ _ (2168491 / 100000) (1084247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2616152320 :
    ThetaLowerSegment 2616152320 2616283392 (26161078336291 / 10000) (130811957887343 / 50000) := by
  exact
    packedTile65536 2616152320 2616283392 14 6056 51148 31 _ _ (135531 / 6250) (2168499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2616283392 :
    ThetaLowerSegment 2616283392 2616414464 (130811957887343 / 50000) (32704629400717 / 12500) := by
  exact
    packedTile65536 2616283392 2616414464 14 6050 51149 31 _ _ (2168501 / 100000) (271063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2616414464 :
    ThetaLowerSegment 2616414464 2616545536 (32704629400717 / 12500) (130824991677531 / 50000) := by
  exact
    packedTile65536 2616414464 2616545536 14 5971 51150 31 _ _ (1084253 / 50000) (2168509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2616545536 :
    ThetaLowerSegment 2616545536 2616676608 (130824991677531 / 50000)
      (261663291507069 / 100000) := by
  exact
    packedTile65536 2616545536 2616676608 14 6137 51152 31 _ _ (2168511 / 100000) (1084257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2616676608 :
    ThetaLowerSegment 2616676608 2616807680 (261663291507069 / 100000)
      (261676205019849 / 100000) := by
  exact
    packedTile65536 2616676608 2616807680 14 5955 51153 31 _ _ (542129 / 25000) (2168519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2616807680 :
    ThetaLowerSegment 2616807680 2616938752 (261676205019849 / 100000)
      (261689480705411 / 100000) := by
  exact
    packedTile65536 2616807680 2616938752 14 6122 51154 31 _ _ (2168521 / 100000) (542131 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2616938752 :
    ThetaLowerSegment 2616938752 2617069824 (261689480705411 / 100000)
      (261702682691699 / 100000) := by
  exact
    packedTile65536 2616938752 2617069824 14 6088 51156 31 _ _ (1084263 / 50000) (2168529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2617069824 :
    ThetaLowerSegment 2617069824 2617200896 (261702682691699 / 100000)
      (261715780618939 / 100000) := by
  exact
    packedTile65536 2617069824 2617200896 14 6040 51157 31 _ _ (2168531 / 100000) (1084267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2617200896 :
    ThetaLowerSegment 2617200896 2617331968 (261715780618939 / 100000)
      (261728813520299 / 100000) := by
  exact
    packedTile65536 2617200896 2617331968 14 6010 51158 31 _ _ (271067 / 12500) (2168539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2617331968 :
    ThetaLowerSegment 2617331968 2617463040 (261728813520299 / 100000)
      (130870980692191 / 50000) := by
  exact
    packedTile65536 2617331968 2617463040 14 6063 51159 31 _ _ (2168541 / 100000) (67767 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2617463040 :
    ThetaLowerSegment 2617463040 2617594112 (130870980692191 / 50000) (6543872852741 / 2500) := by
  exact
    packedTile65536 2617463040 2617594112 14 5973 51161 31 _ _ (1084273 / 50000) (2168549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2617594112 :
    ThetaLowerSegment 2617594112 2617725184 (6543872852741 / 2500) (130883964876371 / 50000) := by
  exact
    packedTile65536 2617594112 2617725184 14 6002 51162 31 _ _ (2168551 / 100000) (1084277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2617725184 :
    ThetaLowerSegment 2617725184 2617856256 (130883964876371 / 50000) (26178104517943 / 10000) := by
  exact
    packedTile65536 2617725184 2617856256 14 6048 51163 31 _ _ (542139 / 25000) (2168559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2617856256 :
    ThetaLowerSegment 2617856256 2617987328 (26178104517943 / 10000)
      (261794149793553 / 100000) := by
  exact
    packedTile65536 2617856256 2617987328 14 6043 51164 31 _ _ (2168561 / 100000) (542141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2617987328 :
    ThetaLowerSegment 2617987328 2618118400 (261794149793553 / 100000)
      (261807365034757 / 100000) := by
  exact
    packedTile65536 2617987328 2618118400 14 6094 51166 31 _ _ (1084283 / 50000) (2168569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2618118400 :
    ThetaLowerSegment 2618118400 2618249472 (261807365034757 / 100000)
      (261820593317857 / 100000) := by
  exact
    packedTile65536 2618118400 2618249472 14 6100 51167 31 _ _ (2168571 / 100000) (1084287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2618249472 :
    ThetaLowerSegment 2618249472 2618380544 (261820593317857 / 100000)
      (261833715371233 / 100000) := by
  exact
    packedTile65536 2618249472 2618380544 14 6051 51168 31 _ _ (67768 / 3125) (2168579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2618380544 :
    ThetaLowerSegment 2618380544 2618511616 (261833715371233 / 100000)
      (261846952389657 / 100000) := by
  exact
    packedTile65536 2618380544 2618511616 14 6104 51170 31 _ _ (2168581 / 100000) (271073 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2618511616 :
    ThetaLowerSegment 2618511616 2618642688 (261846952389657 / 100000)
      (52371989745111 / 20000) := by
  exact
    packedTile65536 2618511616 2618642688 14 5993 51171 31 _ _ (1084293 / 50000) (2168589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2618642688 :
    ThetaLowerSegment 2618642688 2618773760 (52371989745111 / 20000)
      (261873016654921 / 100000) := by
  exact
    packedTile65536 2618642688 2618773760 14 6026 51172 31 _ _ (2168591 / 100000) (1084297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2618773760 :
    ThetaLowerSegment 2618773760 2618904832 (261873016654921 / 100000)
      (52377196538081 / 20000) := by
  exact
    packedTile65536 2618773760 2618904832 14 5979 51173 31 _ _ (542149 / 25000) (2168599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2618904832 :
    ThetaLowerSegment 2618904832 2619035904 (52377196538081 / 20000)
      (261899133086869 / 100000) := by
  exact
    packedTile65536 2618904832 2619035904 14 6064 51175 31 _ _ (2168601 / 100000) (542151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2619035904 :
    ThetaLowerSegment 2619035904 2619166976 (261899133086869 / 100000)
      (261912322548561 / 100000) := by
  exact
    packedTile65536 2619035904 2619166976 14 6082 51176 31 _ _ (1084303 / 50000) (2168609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2619166976 :
    ThetaLowerSegment 2619166976 2619298048 (261912322548561 / 100000)
      (130962670360197 / 50000) := by
  exact
    packedTile65536 2619166976 2619298048 14 6003 51177 31 _ _ (2168611 / 100000) (1084307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2619298048 :
    ThetaLowerSegment 2619298048 2619429120 (130962670360197 / 50000)
      (130969196810049 / 50000) := by
  exact
    packedTile65536 2619298048 2619429120 14 6019 51179 31 _ _ (271077 / 12500) (2168619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2619429120 :
    ThetaLowerSegment 2619429120 2619560192 (130969196810049 / 50000) (65487887118771 / 25000) := by
  exact
    packedTile65536 2619429120 2619560192 14 6066 51180 31 _ _ (2168621 / 100000) (135539 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2619560192 :
    ThetaLowerSegment 2619560192 2619691264 (65487887118771 / 25000) (32745591172989 / 12500) := by
  exact
    packedTile65536 2619560192 2619691264 14 6078 51181 31 _ _ (1084313 / 50000) (2168629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2619691264 :
    ThetaLowerSegment 2619691264 2619822336 (32745591172989 / 12500) (8186814712557 / 3125) := by
  exact
    packedTile65536 2619691264 2619822336 14 6152 51182 31 _ _ (2168631 / 100000) (1084317 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2619822336 :
    ThetaLowerSegment 2619822336 2619953408 (8186814712557 / 3125) (65497756016163 / 25000) := by
  exact
    packedTile65536 2619822336 2619953408 14 5973 51184 31 _ _ (542159 / 25000) (2168639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2619953408 :
    ThetaLowerSegment 2619953408 2620084480 (65497756016163 / 25000) (52400817157879 / 20000) := by
  exact
    packedTile65536 2619953408 2620084480 14 6023 51185 31 _ _ (2168641 / 100000) (542161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2620084480 :
    ThetaLowerSegment 2620084480 2620215552 (52400817157879 / 20000)
      (262017308024057 / 100000) := by
  exact
    packedTile65536 2620084480 2620215552 14 6097 51186 31 _ _ (1084323 / 50000) (2168649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2620215552 :
    ThetaLowerSegment 2620215552 2620346624 (262017308024057 / 100000)
      (131015210928327 / 50000) := by
  exact
    packedTile65536 2620215552 2620346624 14 6047 51188 31 _ _ (2168651 / 100000) (1084327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2620346624 :
    ThetaLowerSegment 2620346624 2620477696 (131015210928327 / 50000)
      (131021839425391 / 50000) := by
  exact
    packedTile65536 2620346624 2620477696 14 6113 51189 31 _ _ (135541 / 6250) (2168659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2620477696 :
    ThetaLowerSegment 2620477696 2620608768 (131021839425391 / 50000)
      (262056714672053 / 100000) := by
  exact
    packedTile65536 2620477696 2620608768 14 6011 51190 31 _ _ (2168661 / 100000) (271083 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2620608768 :
    ThetaLowerSegment 2620608768 2620739840 (262056714672053 / 100000)
      (262069867631343 / 100000) := by
  exact
    packedTile65536 2620608768 2620739840 14 6065 51191 31 _ _ (1084333 / 50000) (2168669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2620739840 :
    ThetaLowerSegment 2620739840 2620870912 (262069867631343 / 100000)
      (131041466937059 / 50000) := by
  exact
    packedTile65536 2620739840 2620870912 14 6025 51193 31 _ _ (2168671 / 100000) (1084337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2620870912 :
    ThetaLowerSegment 2620870912 2621001984 (131041466937059 / 50000)
      (131048064049451 / 50000) := by
  exact
    packedTile65536 2620870912 2621001984 14 6084 51194 31 _ _ (542169 / 25000) (2168679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2621001984 :
    ThetaLowerSegment 2621001984 2621133056 (131048064049451 / 50000) (8190917814534 / 3125) := by
  exact
    packedTile65536 2621001984 2621133056 14 6106 51195 31 _ _ (2168681 / 100000) (542171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2621133056 :
    ThetaLowerSegment 2621133056 2621264128 (8190917814534 / 3125) (131061233379921 / 50000) := by
  exact
    packedTile65536 2621133056 2621264128 14 6039 51197 31 _ _ (1084343 / 50000) (2168689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2621264128 :
    ThetaLowerSegment 2621264128 2621395200 (131061233379921 / 50000)
      (262135498424061 / 100000) := by
  exact
    packedTile65536 2621264128 2621395200 14 6009 51198 31 _ _ (2168691 / 100000) (1084347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2621395200 :
    ThetaLowerSegment 2621395200 2621526272 (262135498424061 / 100000)
      (262148610360077 / 100000) := by
  exact
    packedTile65536 2621395200 2621526272 14 6046 51199 31 _ _ (271087 / 12500) (2168699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2621526272 :
    ThetaLowerSegment 2621526272 2621657344 (262148610360077 / 100000)
      (262161722326323 / 100000) := by
  exact
    packedTile65536 2621526272 2621657344 14 6046 51200 31 _ _ (2168701 / 100000) (67772 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2621657344 :
    ThetaLowerSegment 2621657344 2621788416 (262161722326323 / 100000)
      (262174810467033 / 100000) := by
  exact
    packedTile65536 2621657344 2621788416 14 6035 51202 31 _ _ (1084353 / 50000) (2168709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2621788416 :
    ThetaLowerSegment 2621788416 2621919488 (262174810467033 / 100000)
      (65547036467743 / 25000) := by
  exact
    packedTile65536 2621788416 2621919488 14 6149 51203 31 _ _ (2168711 / 100000) (1084357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2621919488 :
    ThetaLowerSegment 2621919488 2622050560 (65547036467743 / 25000) (8193788564751 / 3125) := by
  exact
    packedTile65536 2621919488 2622050560 14 6035 51204 31 _ _ (542179 / 25000) (2168719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622050560 :
    ThetaLowerSegment 2622050560 2622181632 (8193788564751 / 3125) (131107151392389 / 50000) := by
  exact
    packedTile65536 2622050560 2622181632 14 6026 51205 31 _ _ (2168721 / 100000) (542181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622181632 :
    ThetaLowerSegment 2622181632 2622312704 (131107151392389 / 50000) (1638919865694 / 625) := by
  exact
    packedTile65536 2622181632 2622312704 14 5937 51207 31 _ _ (1084363 / 50000) (2168729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622312704 :
    ThetaLowerSegment 2622312704 2622443776 (1638919865694 / 625) (16390029280913 / 6250) := by
  exact
    packedTile65536 2622312704 2622443776 14 6128 51208 31 _ _ (2168731 / 100000) (1084367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622443776 :
    ThetaLowerSegment 2622443776 2622574848 (16390029280913 / 6250) (16390845403379 / 6250) := by
  exact
    packedTile65536 2622443776 2622574848 14 6021 51209 31 _ _ (67773 / 3125) (2168739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622574848 :
    ThetaLowerSegment 2622574848 2622705920 (16390845403379 / 6250) (262266623480963 / 100000) := by
  exact
    packedTile65536 2622574848 2622705920 14 6039 51211 31 _ _ (2168741 / 100000) (271093 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622705920 :
    ThetaLowerSegment 2622705920 2622836992 (262266623480963 / 100000)
      (262279722706803 / 100000) := by
  exact
    packedTile65536 2622705920 2622836992 14 6040 51212 31 _ _ (1084373 / 50000) (2168749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622836992 :
    ThetaLowerSegment 2622836992 2622968064 (262279722706803 / 100000)
      (65573170248507 / 25000) := by
  exact
    packedTile65536 2622836992 2622968064 14 5975 51213 31 _ _ (2168751 / 100000) (1084377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622968064 :
    ThetaLowerSegment 2622968064 2623099136 (65573170248507 / 25000) (65576485192053 / 25000) := by
  exact
    packedTile65536 2622968064 2623099136 14 6114 51214 31 _ _ (542189 / 25000) (2168759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2623099136 :
    ThetaLowerSegment 2623099136 2623230208 (65576485192053 / 25000) (131159426785603 / 50000) := by
  exact
    packedTile65536 2623099136 2623230208 14 5954 51216 31 _ _ (2168761 / 100000) (542191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2623230208 :
    ThetaLowerSegment 2623230208 2623361280 (131159426785603 / 50000)
      (131166015496711 / 50000) := by
  exact
    packedTile65536 2623230208 2623361280 14 6076 51217 31 _ _ (1084383 / 50000) (2168769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2623361280 :
    ThetaLowerSegment 2623361280 2623492352 (131166015496711 / 50000) (10493801137521 / 4000) := by
  exact
    packedTile65536 2623361280 2623492352 14 5993 51218 31 _ _ (2168771 / 100000) (1084387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2623492352 :
    ThetaLowerSegment 2623492352 2623623424 (10493801137521 / 4000) (52471593037373 / 20000) := by
  exact
    packedTile65536 2623492352 2623623424 14 5965 51220 31 _ _ (271097 / 12500) (2168779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2623623424 :
    ThetaLowerSegment 2623623424 2623754496 (52471593037373 / 20000)
      (262371199088527 / 100000) := by
  exact
    packedTile65536 2623623424 2623754496 14 6102 51221 31 _ _ (2168781 / 100000) (135549 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2623754496 :
    ThetaLowerSegment 2623754496 2623885568 (262371199088527 / 100000)
      (262384183610309 / 100000) := by
  exact
    packedTile65536 2623754496 2623885568 14 5987 51222 31 _ _ (1084393 / 50000) (2168789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2623885568 :
    ThetaLowerSegment 2623885568 2624016640 (262384183610309 / 100000) (10495894447377 / 4000) := by
  exact
    packedTile65536 2623885568 2624016640 14 6076 51223 31 _ _ (2168791 / 100000) (1084397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2624016640 :
    ThetaLowerSegment 2624016640 2624147712 (10495894447377 / 4000) (262410527944941 / 100000) := by
  exact
    packedTile65536 2624016640 2624147712 14 6071 51225 31 _ _ (542199 / 25000) (2168799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2624147712 :
    ThetaLowerSegment 2624147712 2624278784 (262410527944941 / 100000) (13121181266709 / 5000) := by
  exact
    packedTile65536 2624147712 2624278784 14 6039 51226 31 _ _ (2168801 / 100000) (542201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2624278784 :
    ThetaLowerSegment 2624278784 2624409856 (13121181266709 / 5000) (16402292325543 / 6250) := by
  exact
    packedTile65536 2624278784 2624409856 14 6018 51227 31 _ _ (1084403 / 50000) (2168809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2624409856 :
    ThetaLowerSegment 2624409856 2624540928 (16402292325543 / 6250) (131224894919997 / 50000) := by
  exact
    packedTile65536 2624409856 2624540928 14 6046 51228 31 _ _ (2168811 / 100000) (1084407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2624540928 :
    ThetaLowerSegment 2624540928 2624672000 (131224894919997 / 50000)
      (131231514146429 / 50000) := by
  exact
    packedTile65536 2624540928 2624672000 14 6104 51230 31 _ _ (135551 / 6250) (2168819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2624672000 :
    ThetaLowerSegment 2624672000 2624803072 (131231514146429 / 50000)
      (131238046635281 / 50000) := by
  exact
    packedTile65536 2624672000 2624803072 14 6024 51231 31 _ _ (2168821 / 100000) (271103 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2624803072 :
    ThetaLowerSegment 2624803072 2624934144 (131238046635281 / 50000) (16405578221119 / 6250) := by
  exact
    packedTile65536 2624803072 2624934144 14 6067 51232 31 _ _ (1084413 / 50000) (2168829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2624934144 :
    ThetaLowerSegment 2624934144 2625065216 (16405578221119 / 6250) (8203195766372 / 3125) := by
  exact
    packedTile65536 2624934144 2625065216 14 6000 51234 31 _ _ (2168831 / 100000) (1084417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2625065216 :
    ThetaLowerSegment 2625065216 2625196288 (8203195766372 / 3125) (2625154098389 / 1000) := by
  exact
    packedTile65536 2625065216 2625196288 14 6061 51235 31 _ _ (542209 / 25000) (2168839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2625196288 :
    ThetaLowerSegment 2625196288 2625327360 (2625154098389 / 1000) (262528373001557 / 100000) := by
  exact
    packedTile65536 2625196288 2625327360 14 5977 51236 31 _ _ (2168841 / 100000) (542211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2625327360 :
    ThetaLowerSegment 2625327360 2625458432 (262528373001557 / 100000)
      (262541448974091 / 100000) := by
  exact
    packedTile65536 2625327360 2625458432 14 6029 51237 31 _ _ (1084423 / 50000) (2168849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2625458432 :
    ThetaLowerSegment 2625458432 2625589504 (262541448974091 / 100000)
      (52510946203523 / 20000) := by
  exact
    packedTile65536 2625458432 2625589504 14 6124 51239 31 _ _ (2168851 / 100000) (1084427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2625589504 :
    ThetaLowerSegment 2625589504 2625720576 (52510946203523 / 20000)
      (262567778855311 / 100000) := by
  exact
    packedTile65536 2625589504 2625720576 14 6016 51240 31 _ _ (271107 / 12500) (2168859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2625720576 :
    ThetaLowerSegment 2625720576 2625851648 (262567778855311 / 100000)
      (65645250600207 / 25000) := by
  exact
    packedTile65536 2625720576 2625851648 14 6097 51241 31 _ _ (2168861 / 100000) (67777 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2625851648 :
    ThetaLowerSegment 2625851648 2625982720 (65645250600207 / 25000) (65648493054877 / 25000) := by
  exact
    packedTile65536 2625851648 2625982720 14 5980 51243 31 _ _ (1084433 / 50000) (2168869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2625982720 :
    ThetaLowerSegment 2625982720 2626113792 (65648493054877 / 25000) (131303529593561 / 50000) := by
  exact
    packedTile65536 2625982720 2626113792 14 6034 51244 31 _ _ (2168871 / 100000) (1084437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2626113792 :
    ThetaLowerSegment 2626113792 2626244864 (131303529593561 / 50000)
      (131310013448363 / 50000) := by
  exact
    packedTile65536 2626113792 2626244864 14 5979 51245 31 _ _ (542219 / 25000) (2168879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2626244864 :
    ThetaLowerSegment 2626244864 2626375936 (131310013448363 / 50000)
      (131316485389267 / 50000) := by
  exact
    packedTile65536 2626244864 2626375936 14 5968 51246 31 _ _ (2168881 / 100000) (542221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2626375936 :
    ThetaLowerSegment 2626375936 2626507008 (131316485389267 / 50000) (16415386883669 / 6250) := by
  exact
    packedTile65536 2626375936 2626507008 14 6095 51248 31 _ _ (1084443 / 50000) (2168889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2626507008 :
    ThetaLowerSegment 2626507008 2626638080 (16415386883669 / 6250) (262659262044761 / 100000) := by
  exact
    packedTile65536 2626507008 2626638080 14 6027 51249 31 _ _ (2168891 / 100000) (1084447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2626638080 :
    ThetaLowerSegment 2626638080 2626769152 (262659262044761 / 100000)
      (262672529181593 / 100000) := by
  exact
    packedTile65536 2626638080 2626769152 14 6117 51250 31 _ _ (67778 / 3125) (2168899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2626769152 :
    ThetaLowerSegment 2626769152 2626900224 (262672529181593 / 100000)
      (26268557945891 / 10000) := by
  exact
    packedTile65536 2626769152 2626900224 14 6017 51252 31 _ _ (2168901 / 100000) (271113 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2626900224 :
    ThetaLowerSegment 2626900224 2627031296 (26268557945891 / 10000) (131349400554943 / 50000) := by
  exact
    packedTile65536 2626900224 2627031296 14 6096 51253 31 _ _ (1084453 / 50000) (2168909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2627031296 :
    ThetaLowerSegment 2627031296 2627162368 (131349400554943 / 50000)
      (131355928977053 / 50000) := by
  exact
    packedTile65536 2627031296 2627162368 14 6020 51254 31 _ _ (2168911 / 100000) (1084457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2627162368 :
    ThetaLowerSegment 2627162368 2627293440 (131355928977053 / 50000)
      (131362574535677 / 50000) := by
  exact
    packedTile65536 2627162368 2627293440 14 6128 51255 31 _ _ (542229 / 25000) (2168919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2627293440 :
    ThetaLowerSegment 2627293440 2627424512 (131362574535677 / 50000)
      (131369063947309 / 50000) := by
  exact
    packedTile65536 2627293440 2627424512 14 5984 51257 31 _ _ (2168921 / 100000) (542231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2627424512 :
    ThetaLowerSegment 2627424512 2627555584 (131369063947309 / 50000)
      (131375731222759 / 50000) := by
  exact
    packedTile65536 2627424512 2627555584 14 6148 51258 31 _ _ (86757 / 4000) (67779 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2627555584 :
    ThetaLowerSegment 2627555584 2627686656 (131375731222759 / 50000) (32845556520911 / 12500) := by
  exact
    packedTile65536 2627555584 2627686656 14 5989 51259 31 _ _ (216893 / 10000) (2168933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2627686656 :
    ThetaLowerSegment 2627686656 2627817728 (32845556520911 / 12500)
      (262777506987053 / 100000) := by
  exact
    packedTile65536 2627686656 2627817728 14 6019 51260 31 _ _ (433787 / 20000) (1084469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2627817728 :
    ThetaLowerSegment 2627817728 2627948800 (262777506987053 / 100000)
      (262790505444473 / 100000) := by
  exact
    packedTile65536 2627817728 2627948800 14 5993 51262 31 _ _ (108447 / 5000) (2168943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2627948800 :
    ThetaLowerSegment 2627948800 2628079872 (262790505444473 / 100000)
      (131401895116299 / 50000) := by
  exact
    packedTile65536 2627948800 2628079872 14 6125 51263 31 _ _ (433789 / 20000) (542237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2628079872 :
    ThetaLowerSegment 2628079872 2628210944 (131401895116299 / 50000) (65704227552787 / 25000) := by
  exact
    packedTile65536 2628079872 2628210944 14 6049 51264 31 _ _ (43379 / 2000) (2168953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2628210944 :
    ThetaLowerSegment 2628210944 2628342016 (65704227552787 / 25000) (131414942449979 / 50000) := by
  exact
    packedTile65536 2628210944 2628342016 14 5982 51266 31 _ _ (433791 / 20000) (1084479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2628342016 :
    ThetaLowerSegment 2628342016 2628473088 (131414942449979 / 50000)
      (131421499216059 / 50000) := by
  exact
    packedTile65536 2628342016 2628473088 14 6046 51267 31 _ _ (13556 / 625) (2168963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2628473088 :
    ThetaLowerSegment 2628473088 2628604160 (131421499216059 / 50000)
      (131427945380039 / 50000) := by
  exact
    packedTile65536 2628473088 2628604160 14 5944 51268 31 _ _ (433793 / 20000) (271121 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2628604160 :
    ThetaLowerSegment 2628604160 2628735232 (131427945380039 / 50000) (65717275489087 / 25000) := by
  exact
    packedTile65536 2628604160 2628735232 14 6091 51269 31 _ _ (216897 / 10000) (2168973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2628735232 :
    ThetaLowerSegment 2628735232 2628866304 (65717275489087 / 25000) (131441151169099 / 50000) := by
  exact
    packedTile65536 2628735232 2628866304 14 6086 51271 31 _ _ (86759 / 4000) (1084489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2628866304 :
    ThetaLowerSegment 2628866304 2628997376 (131441151169099 / 50000)
      (131447757882179 / 50000) := by
  exact
    packedTile65536 2628866304 2628997376 14 6092 51272 31 _ _ (108449 / 5000) (2168983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2628997376 :
    ThetaLowerSegment 2628997376 2629128448 (131447757882179 / 50000)
      (131454199767629 / 50000) := by
  exact
    packedTile65536 2628997376 2629128448 14 5940 51273 31 _ _ (433797 / 20000) (542247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2629128448 :
    ThetaLowerSegment 2629128448 2629259520 (131454199767629 / 50000) (65730337643637 / 25000) := by
  exact
    packedTile65536 2629128448 2629259520 14 5971 51275 31 _ _ (216899 / 10000) (2168993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2629259520 :
    ThetaLowerSegment 2629259520 2629390592 (65730337643637 / 25000)
      (262934436121383 / 100000) := by
  exact
    packedTile65536 2629259520 2629390592 14 6033 51276 31 _ _ (433799 / 20000) (1084499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2629390592 :
    ThetaLowerSegment 2629390592 2629521664 (262934436121383 / 100000)
      (262947430600383 / 100000) := by
  exact
    packedTile65536 2629390592 2629521664 14 5991 51277 31 _ _ (2169 / 100) (2169003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2629521664 :
    ThetaLowerSegment 2629521664 2629652736 (262947430600383 / 100000)
      (65740150741937 / 25000) := by
  exact
    packedTile65536 2629521664 2629652736 14 6073 51278 31 _ _ (433801 / 20000) (135563 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2629652736 :
    ThetaLowerSegment 2629652736 2629783808 (65740150741937 / 25000) (32871722191811 / 12500) := by
  exact
    packedTile65536 2629652736 2629783808 14 6074 51280 31 _ _ (216901 / 10000) (2169013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2629783808 :
    ThetaLowerSegment 2629783808 2629914880 (32871722191811 / 12500)
      (262986806807593 / 100000) := by
  exact
    packedTile65536 2629783808 2629914880 14 6007 51281 31 _ _ (433803 / 20000) (1084509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2629914880 :
    ThetaLowerSegment 2629914880 2630045952 (262986806807593 / 100000)
      (262999901181333 / 100000) := by
  exact
    packedTile65536 2629914880 2630045952 14 6037 51282 31 _ _ (108451 / 5000) (2169023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2630045952 :
    ThetaLowerSegment 2630045952 2630177024 (262999901181333 / 100000)
      (131506502130679 / 50000) := by
  exact
    packedTile65536 2630045952 2630177024 14 6041 51283 31 _ _ (86761 / 4000) (542257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2630177024 :
    ThetaLowerSegment 2630177024 2630308096 (131506502130679 / 50000)
      (131513054770309 / 50000) := by
  exact
    packedTile65536 2630177024 2630308096 14 6042 51285 31 _ _ (216903 / 10000) (2169033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2630308096 :
    ThetaLowerSegment 2630308096 2630439168 (131513054770309 / 50000)
      (263039104229303 / 100000) := by
  exact
    packedTile65536 2630308096 2630439168 14 5991 51286 31 _ _ (433807 / 20000) (1084519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2630439168 :
    ThetaLowerSegment 2630439168 2630570240 (263039104229303 / 100000)
      (263052363570823 / 100000) := by
  exact
    packedTile65536 2630439168 2630570240 14 6113 51287 31 _ _ (27113 / 1250) (2169043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2630570240 :
    ThetaLowerSegment 2630570240 2630701312 (263052363570823 / 100000)
      (263065542688243 / 100000) := by
  exact
    packedTile65536 2630570240 2630701312 14 6076 51289 31 _ _ (433809 / 20000) (271131 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2630701312 :
    ThetaLowerSegment 2630701312 2630832384 (263065542688243 / 100000)
      (263078700145543 / 100000) := by
  exact
    packedTile65536 2630701312 2630832384 14 6066 51290 31 _ _ (43381 / 2000) (2169053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2630832384 :
    ThetaLowerSegment 2630832384 2630963456 (263078700145543 / 100000)
      (263092035495683 / 100000) := by
  exact
    packedTile65536 2630832384 2630963456 14 6148 51291 31 _ _ (433811 / 20000) (1084529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2630963456 :
    ThetaLowerSegment 2630963456 2631094528 (263092035495683 / 100000)
      (263105173492103 / 100000) := by
  exact
    packedTile65536 2630963456 2631094528 14 6057 51292 31 _ _ (108453 / 5000) (2169063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2631094528 :
    ThetaLowerSegment 2631094528 2631225600 (263105173492103 / 100000)
      (131559153590339 / 50000) := by
  exact
    packedTile65536 2631094528 2631225600 14 6055 51294 31 _ _ (433813 / 20000) (542267 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2631225600 :
    ThetaLowerSegment 2631225600 2631356672 (131559153590339 / 50000) (32891430112441 / 12500) := by
  exact
    packedTile65536 2631225600 2631356672 14 6055 51295 31 _ _ (216907 / 10000) (2169073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2631356672 :
    ThetaLowerSegment 2631356672 2631487744 (32891430112441 / 12500)
      (263144565972353 / 100000) := by
  exact
    packedTile65536 2631356672 2631487744 14 6051 51296 31 _ _ (86763 / 4000) (1084539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2631487744 :
    ThetaLowerSegment 2631487744 2631618816 (263144565972353 / 100000)
      (263157749640593 / 100000) := by
  exact
    packedTile65536 2631487744 2631618816 14 6078 51298 31 _ _ (54227 / 2500) (2169083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2631618816 :
    ThetaLowerSegment 2631618816 2631749888 (263157749640593 / 100000)
      (32896368023081 / 12500) := by
  exact
    packedTile65536 2631618816 2631749888 14 6083 51299 31 _ _ (433817 / 20000) (67784 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2631749888 :
    ThetaLowerSegment 2631749888 2631880960 (32896368023081 / 12500) (65796005949337 / 25000) := by
  exact
    packedTile65536 2631749888 2631880960 14 6030 51300 31 _ _ (216909 / 10000) (2169093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2631880960 :
    ThetaLowerSegment 2631880960 2632012032 (65796005949337 / 25000) (32899628711371 / 12500) := by
  exact
    packedTile65536 2631880960 2632012032 14 5996 51301 31 _ _ (433819 / 20000) (1084549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2632012032 :
    ThetaLowerSegment 2632012032 2632143104 (32899628711371 / 12500) (32901270720071 / 12500) := by
  exact
    packedTile65536 2632012032 2632143104 14 6056 51303 31 _ _ (21691 / 1000) (2169103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2632143104 :
    ThetaLowerSegment 2632143104 2632274176 (32901270720071 / 12500)
      (263223542631103 / 100000) := by
  exact
    packedTile65536 2632143104 2632274176 14 6167 51304 31 _ _ (433821 / 20000) (542277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2632274176 :
    ThetaLowerSegment 2632274176 2632405248 (263223542631103 / 100000)
      (263236544276443 / 100000) := by
  exact
    packedTile65536 2632274176 2632405248 14 5994 51305 31 _ _ (216911 / 10000) (2169113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2632405248 :
    ThetaLowerSegment 2632405248 2632536320 (263236544276443 / 100000) (16453105976293 / 6250) := by
  exact
    packedTile65536 2632405248 2632536320 14 6063 51306 31 _ _ (433823 / 20000) (1084559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2632536320 :
    ThetaLowerSegment 2632536320 2632667392 (16453105976293 / 6250) (16453919803003 / 6250) := by
  exact
    packedTile65536 2632536320 2632667392 14 6003 51308 31 _ _ (13557 / 625) (2169123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2632667392 :
    ThetaLowerSegment 2632667392 2632798464 (16453919803003 / 6250) (131637980762649 / 50000) := by
  exact
    packedTile65536 2632667392 2632798464 14 6106 51309 31 _ _ (17353 / 800) (271141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2632798464 :
    ThetaLowerSegment 2632798464 2632929536 (131637980762649 / 50000)
      (131644459953959 / 50000) := by
  exact
    packedTile65536 2632798464 2632929536 14 5974 51310 31 _ _ (216913 / 10000) (2169133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2632929536 :
    ThetaLowerSegment 2632929536 2633060608 (131644459953959 / 50000) (65825458734427 / 25000) := by
  exact
    packedTile65536 2632929536 2633060608 14 5954 51312 31 _ _ (433827 / 20000) (1084569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633060608 :
    ThetaLowerSegment 2633060608 2633191680 (65825458734427 / 25000) (32914361373921 / 12500) := by
  exact
    packedTile65536 2633060608 2633191680 14 6019 51313 31 _ _ (108457 / 5000) (2169143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633191680 :
    ThetaLowerSegment 2633191680 2633322752 (32914361373921 / 12500) (8228993262164 / 3125) := by
  exact
    packedTile65536 2633191680 2633322752 14 5944 51314 31 _ _ (433829 / 20000) (542287 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633322752 :
    ThetaLowerSegment 2633322752 2633339136 (8228993262164 / 3125) (32916188879081 / 12500) := by
  exact
    packedTile65536 2633322752 2633339136 11 796 51315 31 _ _ (43383 / 2000) (2169153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633339136 :
    ThetaLowerSegment 2633339136 2633341184 (32916188879081 / 12500) (65832433071487 / 25000) := by
  exact
    packedTile65536 2633339136 2633341184 8 102 51316 31 _ _ (43383 / 2000) (2169153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2601341184_2633341184 :
    ThetaLowerSegment 2601341184 2633341184 (325163039859 / 125) (65832433071487 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2601341184 cell2601472256)
                  (ThetaLowerSegment.join cell2601603328 cell2601734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2601865472 cell2601996544)
                  (ThetaLowerSegment.join cell2602127616 cell2602258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2602389760 cell2602520832)
                  (ThetaLowerSegment.join cell2602651904 cell2602782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2602914048 cell2603045120)
                  (ThetaLowerSegment.join cell2603176192 cell2603307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2603438336 cell2603569408)
                  (ThetaLowerSegment.join cell2603700480 cell2603831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2603962624 cell2604093696)
                  (ThetaLowerSegment.join cell2604224768 cell2604355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2604486912 cell2604617984)
                  (ThetaLowerSegment.join cell2604749056 cell2604880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2605011200 cell2605142272)
                  (ThetaLowerSegment.join cell2605273344 cell2605404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2605535488 cell2605666560)
                  (ThetaLowerSegment.join cell2605797632 cell2605928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2606059776 cell2606190848)
                  (ThetaLowerSegment.join cell2606321920 cell2606452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2606584064 cell2606715136)
                  (ThetaLowerSegment.join cell2606846208 cell2606977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2607108352 cell2607239424)
                  (ThetaLowerSegment.join cell2607370496 cell2607501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2607632640 cell2607763712)
                  (ThetaLowerSegment.join cell2607894784 cell2608025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2608156928 cell2608288000)
                  (ThetaLowerSegment.join cell2608419072 cell2608550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2608681216 cell2608812288)
                  (ThetaLowerSegment.join cell2608943360 cell2609074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2609205504 cell2609336576)
                  (ThetaLowerSegment.join cell2609467648 cell2609598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2609729792 cell2609860864)
                  (ThetaLowerSegment.join cell2609991936 cell2610123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2610254080 cell2610385152)
                  (ThetaLowerSegment.join cell2610516224 cell2610647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2610778368 cell2610909440)
                  (ThetaLowerSegment.join cell2611040512 cell2611171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2611302656 cell2611433728)
                  (ThetaLowerSegment.join cell2611564800 cell2611695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2611826944 cell2611958016)
                  (ThetaLowerSegment.join cell2612089088 cell2612220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2612351232 cell2612482304)
                  (ThetaLowerSegment.join cell2612613376 cell2612744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2612875520 cell2613006592)
                  (ThetaLowerSegment.join cell2613137664 cell2613268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2613399808 cell2613530880)
                  (ThetaLowerSegment.join cell2613661952 cell2613793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2613924096 cell2614055168)
                  (ThetaLowerSegment.join cell2614186240 cell2614317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2614448384 cell2614579456)
                  (ThetaLowerSegment.join cell2614710528 cell2614841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2614972672 cell2615103744)
                  (ThetaLowerSegment.join cell2615234816 cell2615365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2615496960 cell2615628032)
                  (ThetaLowerSegment.join cell2615759104 cell2615890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2616021248 cell2616152320)
                  (ThetaLowerSegment.join cell2616283392 cell2616414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2616545536 cell2616676608)
                  (ThetaLowerSegment.join cell2616807680 cell2616938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2617069824 cell2617200896)
                  (ThetaLowerSegment.join cell2617331968 cell2617463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2617594112 cell2617725184)
                  (ThetaLowerSegment.join cell2617856256 cell2617987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2618118400 cell2618249472)
                  (ThetaLowerSegment.join cell2618380544 cell2618511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2618642688 cell2618773760)
                  (ThetaLowerSegment.join cell2618904832 cell2619035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2619166976 cell2619298048)
                  (ThetaLowerSegment.join cell2619429120 cell2619560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2619691264 cell2619822336)
                  (ThetaLowerSegment.join cell2619953408 cell2620084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2620215552 cell2620346624)
                  (ThetaLowerSegment.join cell2620477696 cell2620608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2620739840 cell2620870912)
                  (ThetaLowerSegment.join cell2621001984 cell2621133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2621264128 cell2621395200)
                  (ThetaLowerSegment.join cell2621526272 cell2621657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2621788416 cell2621919488)
                  (ThetaLowerSegment.join cell2622050560 cell2622181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2622312704 cell2622443776)
                  (ThetaLowerSegment.join cell2622574848 cell2622705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2622836992 cell2622968064)
                  (ThetaLowerSegment.join cell2623099136 cell2623230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2623361280 cell2623492352)
                  (ThetaLowerSegment.join cell2623623424 cell2623754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2623885568 cell2624016640)
                  (ThetaLowerSegment.join cell2624147712 cell2624278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2624409856 cell2624540928)
                  (ThetaLowerSegment.join cell2624672000 cell2624803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2624934144 cell2625065216)
                  (ThetaLowerSegment.join cell2625196288 cell2625327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2625458432 cell2625589504)
                  (ThetaLowerSegment.join cell2625720576 cell2625851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2625982720 cell2626113792)
                  (ThetaLowerSegment.join cell2626244864 cell2626375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2626507008 cell2626638080)
                  (ThetaLowerSegment.join cell2626769152 cell2626900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2627031296 cell2627162368)
                  (ThetaLowerSegment.join cell2627293440 cell2627424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2627555584 cell2627686656)
                  (ThetaLowerSegment.join cell2627817728 cell2627948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2628079872 cell2628210944)
                  (ThetaLowerSegment.join cell2628342016 cell2628473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2628604160 cell2628735232)
                  (ThetaLowerSegment.join cell2628866304 cell2628997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2629128448 cell2629259520)
                  (ThetaLowerSegment.join cell2629390592 cell2629521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2629652736 cell2629783808)
                  (ThetaLowerSegment.join cell2629914880 cell2630045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2630177024 cell2630308096)
                  (ThetaLowerSegment.join cell2630439168 cell2630570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2630701312 cell2630832384)
                  (ThetaLowerSegment.join cell2630963456 cell2631094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2631225600 cell2631356672)
                  (ThetaLowerSegment.join cell2631487744 cell2631618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2631749888 cell2631880960)
                  (ThetaLowerSegment.join cell2632012032 cell2632143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2632274176 cell2632405248)
                  (ThetaLowerSegment.join cell2632536320 cell2632667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2632798464 cell2632929536)
                (ThetaLowerSegment.join cell2633060608 cell2633191680))
              (ThetaLowerSegment.join cell2633322752 cell2633339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
