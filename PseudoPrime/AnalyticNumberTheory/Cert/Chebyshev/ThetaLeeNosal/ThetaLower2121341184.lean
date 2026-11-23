/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2121341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2089341184 :
    ThetaLowerSegment 2089341184 2089472256 (104463976484627 / 50000)
      (104470569027347 / 50000) := by
  exact
    packedTile65536 2089341184 2089472256 14 6144 45709 31 _ _ (214601 / 10000) (2146013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089472256 :
    ThetaLowerSegment 2089472256 2089603328 (104470569027347 / 50000) (20895446696007 / 10000) := by
  exact
    packedTile65536 2089472256 2089603328 14 6211 45710 31 _ _ (67063 / 3125) (2146019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089603328 :
    ThetaLowerSegment 2089603328 2089734400 (20895446696007 / 10000)
      (208967529802071 / 100000) := by
  exact
    packedTile65536 2089603328 2089734400 14 6087 45712 31 _ _ (2146023 / 100000) (1073013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089734400 :
    ThetaLowerSegment 2089734400 2089865472 (208967529802071 / 100000)
      (20898064418529 / 10000) := by
  exact
    packedTile65536 2089734400 2089865472 14 6111 45713 31 _ _ (2146029 / 100000) (134127 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089865472 :
    ThetaLowerSegment 2089865472 2089996544 (20898064418529 / 10000) (5224844555289 / 2500) := by
  exact
    packedTile65536 2089865472 2089996544 14 6122 45715 31 _ _ (429207 / 20000) (1073019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089996544 :
    ThetaLowerSegment 2089996544 2090127616 (5224844555289 / 2500) (104503455845199 / 50000) := by
  exact
    packedTile65536 2089996544 2090127616 14 6118 45716 31 _ _ (2146041 / 100000) (536511 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2090127616 :
    ThetaLowerSegment 2090127616 2090258688 (104503455845199 / 50000)
      (104509929398991 / 50000) := by
  exact
    packedTile65536 2090127616 2090258688 14 6033 45717 31 _ _ (67064 / 3125) (2146051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2090258688 :
    ThetaLowerSegment 2090258688 2090389760 (104509929398991 / 50000) (52258252990737 / 25000) := by
  exact
    packedTile65536 2090258688 2090389760 14 6129 45719 31 _ _ (1073027 / 50000) (2146057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2090389760 :
    ThetaLowerSegment 2090389760 2090520832 (52258252990737 / 25000) (26130780839371 / 12500) := by
  exact
    packedTile65536 2090389760 2090520832 14 6167 45720 31 _ _ (107303 / 5000) (2146063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2090520832 :
    ThetaLowerSegment 2090520832 2090651904 (26130780839371 / 12500) (10452973538683 / 5000) := by
  exact
    packedTile65536 2090520832 2090651904 14 6162 45722 31 _ _ (1073033 / 50000) (2146069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2090651904 :
    ThetaLowerSegment 2090651904 2090782976 (10452973538683 / 5000) (209072469537821 / 100000) := by
  exact
    packedTile65536 2090651904 2090782976 14 6057 45723 31 _ _ (2146073 / 100000) (536519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2090782976 :
    ThetaLowerSegment 2090782976 2090914048 (209072469537821 / 100000)
      (41817097530607 / 20000) := by
  exact
    packedTile65536 2090782976 2090914048 14 6066 45725 31 _ _ (2146079 / 100000) (1073041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2090914048 :
    ThetaLowerSegment 2090914048 2091045120 (41817097530607 / 20000) (1306866077083 / 625) := by
  exact
    packedTile65536 2090914048 2091045120 14 6097 45726 31 _ _ (429217 / 20000) (268261 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2091045120 :
    ThetaLowerSegment 2091045120 2091176192 (1306866077083 / 625) (209111657050107 / 100000) := by
  exact
    packedTile65536 2091045120 2091176192 14 6097 45727 31 _ _ (2146091 / 100000) (1073047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2091176192 :
    ThetaLowerSegment 2091176192 2091307264 (209111657050107 / 100000) (8364993449517 / 4000) := by
  exact
    packedTile65536 2091176192 2091307264 14 6141 45729 31 _ _ (1073049 / 50000) (2146101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2091307264 :
    ThetaLowerSegment 2091307264 2091438336 (8364993449517 / 4000) (41827579056153 / 20000) := by
  exact
    packedTile65536 2091307264 2091438336 14 6085 45730 31 _ _ (268263 / 12500) (2146107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2091438336 :
    ThetaLowerSegment 2091438336 2091569408 (41827579056153 / 20000) (8366032251141 / 4000) := by
  exact
    packedTile65536 2091438336 2091569408 14 6016 45732 31 _ _ (214611 / 10000) (2146113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2091569408 :
    ThetaLowerSegment 2091569408 2091700480 (8366032251141 / 4000) (6536375220131 / 3125) := by
  exact
    packedTile65536 2091569408 2091700480 14 6151 45733 31 _ _ (2146117 / 100000) (53653 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2091700480 :
    ThetaLowerSegment 2091700480 2091831552 (6536375220131 / 3125) (104588624311551 / 50000) := by
  exact
    packedTile65536 2091700480 2091831552 14 6170 45735 31 _ _ (2146123 / 100000) (1073063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2091831552 :
    ThetaLowerSegment 2091831552 2091962624 (104588624311551 / 50000)
      (209190428001291 / 100000) := by
  exact
    packedTile65536 2091831552 2091962624 14 6141 45736 31 _ _ (2146129 / 100000) (536533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2091962624 :
    ThetaLowerSegment 2091962624 2092093696 (209190428001291 / 100000)
      (209203716869211 / 100000) := by
  exact
    packedTile65536 2091962624 2092093696 14 6192 45737 31 _ _ (429227 / 20000) (1073069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2092093696 :
    ThetaLowerSegment 2092093696 2092224768 (209203716869211 / 100000)
      (209216776143281 / 100000) := by
  exact
    packedTile65536 2092093696 2092224768 14 6085 45739 31 _ _ (1073071 / 50000) (429229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2092224768 :
    ThetaLowerSegment 2092224768 2092355840 (209216776143281 / 100000)
      (41845959793869 / 20000) := by
  exact
    packedTile65536 2092224768 2092355840 14 6068 45740 31 _ _ (536537 / 25000) (2146151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2092355840 :
    ThetaLowerSegment 2092355840 2092486912 (41845959793869 / 20000) (41848582394057 / 20000) := by
  exact
    packedTile65536 2092355840 2092486912 14 6110 45742 31 _ _ (1073077 / 50000) (2146157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2092486912 :
    ThetaLowerSegment 2092486912 2092617984 (41848582394057 / 20000) (8370234046757 / 4000) := by
  exact
    packedTile65536 2092486912 2092617984 14 6029 45743 31 _ _ (26827 / 1250) (2146163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2092617984 :
    ThetaLowerSegment 2092617984 2092749056 (8370234046757 / 4000) (26158615970557 / 12500) := by
  exact
    packedTile65536 2092617984 2092749056 14 6093 45745 31 _ _ (2146167 / 100000) (214617 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2092749056 :
    ThetaLowerSegment 2092749056 2092880128 (26158615970557 / 12500) (6540061228966 / 3125) := by
  exact
    packedTile65536 2092749056 2092880128 14 6072 45746 31 _ _ (2146173 / 100000) (67068 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2092880128 :
    ThetaLowerSegment 2092880128 2093011200 (6540061228966 / 3125) (209295143304509 / 100000) := by
  exact
    packedTile65536 2092880128 2093011200 14 6143 45748 31 _ _ (2146179 / 100000) (1073091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2093011200 :
    ThetaLowerSegment 2093011200 2093142272 (209295143304509 / 100000)
      (52327064660261 / 25000) := by
  exact
    packedTile65536 2093011200 2093142272 14 6111 45749 31 _ _ (429237 / 20000) (536547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2093142272 :
    ThetaLowerSegment 2093142272 2093273344 (52327064660261 / 25000) (10466071061829 / 5000) := by
  exact
    packedTile65536 2093142272 2093273344 14 6133 45750 31 _ _ (134137 / 6250) (429239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2093273344 :
    ThetaLowerSegment 2093273344 2093404416 (10466071061829 / 5000) (13083402504603 / 6250) := by
  exact
    packedTile65536 2093273344 2093404416 14 6066 45752 31 _ _ (1073099 / 50000) (2146201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2093404416 :
    ThetaLowerSegment 2093404416 2093535488 (13083402504603 / 6250) (52336909270511 / 25000) := by
  exact
    packedTile65536 2093404416 2093535488 14 6149 45753 31 _ _ (536551 / 25000) (2146207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2093535488 :
    ThetaLowerSegment 2093535488 2093666560 (52336909270511 / 25000) (52340197265763 / 25000) := by
  exact
    packedTile65536 2093535488 2093666560 14 6128 45755 31 _ _ (2146211 / 100000) (1073107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2093666560 :
    ThetaLowerSegment 2093666560 2093797632 (52340197265763 / 25000)
      (209373904595139 / 100000) := by
  exact
    packedTile65536 2093666560 2093797632 14 6111 45756 31 _ _ (2146217 / 100000) (107311 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2093797632 :
    ThetaLowerSegment 2093797632 2093928704 (209373904595139 / 100000)
      (209387048064791 / 100000) := by
  exact
    packedTile65536 2093797632 2093928704 14 6124 45758 31 _ _ (2146223 / 100000) (1073113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2093928704 :
    ThetaLowerSegment 2093928704 2094059776 (209387048064791 / 100000)
      (209399839589631 / 100000) := by
  exact
    packedTile65536 2093928704 2094059776 14 5960 45759 31 _ _ (2146229 / 100000) (268279 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094059776 :
    ThetaLowerSegment 2094059776 2094190848 (209399839589631 / 100000)
      (41882594481543 / 20000) := by
  exact
    packedTile65536 2094059776 2094190848 14 6119 45760 31 _ _ (536559 / 25000) (2146239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094190848 :
    ThetaLowerSegment 2094190848 2094321920 (41882594481543 / 20000) (41885221481751 / 20000) := by
  exact
    packedTile65536 2094190848 2094321920 14 6120 45762 31 _ _ (1073121 / 50000) (429249 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094321920 :
    ThetaLowerSegment 2094321920 2094452992 (41885221481751 / 20000) (41887874244279 / 20000) := by
  exact
    packedTile65536 2094321920 2094452992 14 6180 45763 31 _ _ (268281 / 12500) (2146251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094452992 :
    ThetaLowerSegment 2094452992 2094584064 (41887874244279 / 20000)
      (209452371081873 / 100000) := by
  exact
    packedTile65536 2094452992 2094584064 14 6057 45765 31 _ _ (1073127 / 50000) (2146257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094584064 :
    ThetaLowerSegment 2094584064 2094715136 (209452371081873 / 100000)
      (209465523369281 / 100000) := by
  exact
    packedTile65536 2094584064 2094715136 14 6128 45766 31 _ _ (2146261 / 100000) (268283 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094715136 :
    ThetaLowerSegment 2094715136 2094846208 (209465523369281 / 100000)
      (52369686630067 / 25000) := by
  exact
    packedTile65536 2094715136 2094846208 14 6161 45768 31 _ _ (2146267 / 100000) (214627 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094846208 :
    ThetaLowerSegment 2094846208 2094977280 (52369686630067 / 25000) (104745973049609 / 50000) := by
  exact
    packedTile65536 2094846208 2094977280 14 6150 45769 31 _ _ (2146273 / 100000) (536569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094977280 :
    ThetaLowerSegment 2094977280 2095108352 (104745973049609 / 50000) (8380208661691 / 4000) := by
  exact
    packedTile65536 2094977280 2095108352 14 6183 45770 31 _ _ (2146279 / 100000) (1073141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2095108352 :
    ThetaLowerSegment 2095108352 2095239424 (8380208661691 / 4000) (209518345373737 / 100000) := by
  exact
    packedTile65536 2095108352 2095239424 14 6117 45772 31 _ _ (1073143 / 50000) (2146289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2095239424 :
    ThetaLowerSegment 2095239424 2095370496 (209518345373737 / 100000)
      (209531495704821 / 100000) := by
  exact
    packedTile65536 2095239424 2095370496 14 6127 45773 31 _ _ (536573 / 25000) (429259 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2095370496 :
    ThetaLowerSegment 2095370496 2095501568 (209531495704821 / 100000)
      (209544727631991 / 100000) := by
  exact
    packedTile65536 2095370496 2095501568 14 6165 45775 31 _ _ (1073149 / 50000) (2146301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2095501568 :
    ThetaLowerSegment 2095501568 2095632640 (209544727631991 / 100000)
      (41911570885451 / 20000) := by
  exact
    packedTile65536 2095501568 2095632640 14 6116 45776 31 _ _ (67072 / 3125) (2146307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2095632640 :
    ThetaLowerSegment 2095632640 2095763712 (41911570885451 / 20000)
      (209570998435819 / 100000) := by
  exact
    packedTile65536 2095632640 2095763712 14 6124 45778 31 _ _ (2146311 / 100000) (1073157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2095763712 :
    ThetaLowerSegment 2095763712 2095894784 (209570998435819 / 100000)
      (26198010566321 / 12500) := by
  exact
    packedTile65536 2095763712 2095894784 14 6097 45779 31 _ _ (2146317 / 100000) (26829 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2095894784 :
    ThetaLowerSegment 2095894784 2096025856 (26198010566321 / 12500)
      (209597084808979 / 100000) := by
  exact
    packedTile65536 2095894784 2096025856 14 6057 45780 31 _ _ (2146323 / 100000) (1073163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2096025856 :
    ThetaLowerSegment 2096025856 2096156928 (209597084808979 / 100000)
      (52402547036881 / 25000) := by
  exact
    packedTile65536 2096025856 2096156928 14 6105 45782 31 _ _ (2146329 / 100000) (536583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2096156928 :
    ThetaLowerSegment 2096156928 2096288000 (52402547036881 / 25000) (52405829857793 / 25000) := by
  exact
    packedTile65536 2096156928 2096288000 14 6118 45783 31 _ _ (67073 / 3125) (2146339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2096288000 :
    ThetaLowerSegment 2096288000 2096419072 (52405829857793 / 25000) (13102262610991 / 6250) := by
  exact
    packedTile65536 2096288000 2096419072 14 6002 45785 31 _ _ (1073171 / 50000) (429269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2096419072 :
    ThetaLowerSegment 2096419072 2096550144 (13102262610991 / 6250) (52412312356337 / 25000) := by
  exact
    packedTile65536 2096419072 2096550144 14 6079 45786 31 _ _ (536587 / 25000) (2146351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2096550144 :
    ThetaLowerSegment 2096550144 2096681216 (52412312356337 / 25000) (104831240848879 / 50000) := by
  exact
    packedTile65536 2096550144 2096681216 14 6165 45788 31 _ _ (1073177 / 50000) (2146357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2096681216 :
    ThetaLowerSegment 2096681216 2096812288 (104831240848879 / 50000)
      (104837813006261 / 50000) := by
  exact
    packedTile65536 2096681216 2096812288 14 6124 45789 31 _ _ (2146361 / 100000) (536591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2096812288 :
    ThetaLowerSegment 2096812288 2096943360 (104837813006261 / 50000)
      (209688712412121 / 100000) := by
  exact
    packedTile65536 2096812288 2096943360 14 6097 45790 31 _ _ (2146367 / 100000) (214637 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2096943360 :
    ThetaLowerSegment 2096943360 2097074432 (209688712412121 / 100000)
      (104850946644357 / 50000) := by
  exact
    packedTile65536 2096943360 2097074432 14 6141 45792 31 _ _ (2146373 / 100000) (268297 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2097074432 :
    ThetaLowerSegment 2097074432 2097205504 (104850946644357 / 50000)
      (209714954004929 / 100000) := by
  exact
    packedTile65536 2097074432 2097205504 14 6085 45793 31 _ _ (2146379 / 100000) (1073191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2097205504 :
    ThetaLowerSegment 2097205504 2097336576 (209714954004929 / 100000)
      (209728139254127 / 100000) := by
  exact
    packedTile65536 2097205504 2097336576 14 6143 45795 31 _ _ (1073193 / 50000) (2146389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2097336576 :
    ThetaLowerSegment 2097336576 2097467648 (209728139254127 / 100000)
      (209741296637087 / 100000) := by
  exact
    packedTile65536 2097336576 2097467648 14 6130 45796 31 _ _ (268299 / 12500) (429279 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2097467648 :
    ThetaLowerSegment 2097467648 2097598720 (209741296637087 / 100000)
      (209754404689673 / 100000) := by
  exact
    packedTile65536 2097467648 2097598720 14 6107 45798 31 _ _ (1073199 / 50000) (2146401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2097598720 :
    ThetaLowerSegment 2097598720 2097729792 (209754404689673 / 100000)
      (41953524449101 / 20000) := by
  exact
    packedTile65536 2097598720 2097729792 14 6158 45799 31 _ _ (536601 / 25000) (2146407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2097729792 :
    ThetaLowerSegment 2097729792 2097860864 (41953524449101 / 20000)
      (209780470661751 / 100000) := by
  exact
    packedTile65536 2097729792 2097860864 14 5986 45800 31 _ _ (2146411 / 100000) (1073207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2097860864 :
    ThetaLowerSegment 2097860864 2097991936 (209780470661751 / 100000)
      (209793400677759 / 100000) := by
  exact
    packedTile65536 2097860864 2097991936 14 6024 45802 31 _ _ (2146417 / 100000) (107321 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2097991936 :
    ThetaLowerSegment 2097991936 2098123008 (209793400677759 / 100000)
      (104903269466471 / 50000) := by
  exact
    packedTile65536 2097991936 2098123008 14 6121 45803 31 _ _ (2146423 / 100000) (1073213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2098123008 :
    ThetaLowerSegment 2098123008 2098254080 (104903269466471 / 50000) (5245489837853 / 2500) := by
  exact
    packedTile65536 2098123008 2098254080 14 6082 45805 31 _ _ (2146429 / 100000) (67076 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2098254080 :
    ThetaLowerSegment 2098254080 2098385152 (5245489837853 / 2500) (1311453889879 / 625) := by
  exact
    packedTile65536 2098254080 2098385152 14 6070 45806 31 _ _ (536609 / 25000) (2146439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2098385152 :
    ThetaLowerSegment 2098385152 2098516224 (1311453889879 / 625) (104922794518381 / 50000) := by
  exact
    packedTile65536 2098385152 2098516224 14 6041 45808 31 _ _ (1073221 / 50000) (429289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2098516224 :
    ThetaLowerSegment 2098516224 2098647296 (104922794518381 / 50000) (20985879183841 / 10000) := by
  exact
    packedTile65536 2098516224 2098647296 14 6151 45809 31 _ _ (134153 / 6250) (2146451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2098647296 :
    ThetaLowerSegment 2098647296 2098778368 (20985879183841 / 10000) (104935918992911 / 50000) := by
  exact
    packedTile65536 2098647296 2098778368 14 6078 45810 31 _ _ (1073227 / 50000) (2146457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2098778368 :
    ThetaLowerSegment 2098778368 2098909440 (104935918992911 / 50000)
      (209884963594837 / 100000) := by
  exact
    packedTile65536 2098778368 2098909440 14 6115 45812 31 _ _ (2146461 / 100000) (67077 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2098909440 :
    ThetaLowerSegment 2098909440 2099040512 (209884963594837 / 100000)
      (209898095679943 / 100000) := by
  exact
    packedTile65536 2098909440 2099040512 14 6118 45813 31 _ _ (2146467 / 100000) (214647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2099040512 :
    ThetaLowerSegment 2099040512 2099171584 (209898095679943 / 100000)
      (209911171993459 / 100000) := by
  exact
    packedTile65536 2099040512 2099171584 14 6092 45815 31 _ _ (2146473 / 100000) (536619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2099171584 :
    ThetaLowerSegment 2099171584 2099302656 (209911171993459 / 100000) (5248108730701 / 2500) := by
  exact
    packedTile65536 2099171584 2099302656 14 6139 45816 31 _ _ (2146479 / 100000) (1073241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2099302656 :
    ThetaLowerSegment 2099302656 2099433728 (5248108730701 / 2500) (2624219108151 / 1250) := by
  exact
    packedTile65536 2099302656 2099433728 14 6140 45818 31 _ _ (1073243 / 50000) (2146489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2099433728 :
    ThetaLowerSegment 2099433728 2099564800 (2624219108151 / 1250) (52487666832403 / 25000) := by
  exact
    packedTile65536 2099433728 2099564800 14 6121 45819 31 _ _ (536623 / 25000) (429299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2099564800 :
    ThetaLowerSegment 2099564800 2099695872 (52487666832403 / 25000) (104981812869019 / 50000) := by
  exact
    packedTile65536 2099564800 2099695872 14 6037 45821 31 _ _ (1073249 / 50000) (2146501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2099695872 :
    ThetaLowerSegment 2099695872 2099826944 (104981812869019 / 50000)
      (104988366145731 / 50000) := by
  exact
    packedTile65536 2099695872 2099826944 14 6106 45822 31 _ _ (268313 / 12500) (2146507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2099826944 :
    ThetaLowerSegment 2099826944 2099958016 (104988366145731 / 50000)
      (209989686485347 / 100000) := by
  exact
    packedTile65536 2099826944 2099958016 14 6035 45823 31 _ _ (2146511 / 100000) (1073257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2099958016 :
    ThetaLowerSegment 2099958016 2100089088 (209989686485347 / 100000)
      (210002866099727 / 100000) := by
  exact
    packedTile65536 2099958016 2100089088 14 6140 45825 31 _ _ (2146517 / 100000) (53663 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2100089088 :
    ThetaLowerSegment 2100089088 2100220160 (210002866099727 / 100000) (1680128125597 / 800) := by
  exact
    packedTile65536 2100089088 2100220160 14 6126 45826 31 _ _ (2146523 / 100000) (1073263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2100220160 :
    ThetaLowerSegment 2100220160 2100351232 (1680128125597 / 800) (6563416313528 / 3125) := by
  exact
    packedTile65536 2100220160 2100351232 14 6199 45828 31 _ _ (2146529 / 100000) (536633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2100351232 :
    ThetaLowerSegment 2100351232 2100482304 (6563416313528 / 3125) (1312763811469 / 625) := by
  exact
    packedTile65536 2100351232 2100482304 14 6004 45829 31 _ _ (268317 / 12500) (2146539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2100482304 :
    ThetaLowerSegment 2100482304 2100613376 (1312763811469 / 625) (105027659383517 / 50000) := by
  exact
    packedTile65536 2100482304 2100613376 14 6107 45831 31 _ _ (1073271 / 50000) (429309 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2100613376 :
    ThetaLowerSegment 2100613376 2100744448 (105027659383517 / 50000)
      (105034258945343 / 50000) := by
  exact
    packedTile65536 2100613376 2100744448 14 6149 45832 31 _ _ (536637 / 25000) (2146551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2100744448 :
    ThetaLowerSegment 2100744448 2100875520 (105034258945343 / 50000) (52520413163653 / 25000) := by
  exact
    packedTile65536 2100744448 2100875520 14 6119 45833 31 _ _ (1073277 / 50000) (2146557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2100875520 :
    ThetaLowerSegment 2100875520 2101006592 (52520413163653 / 25000) (8403796993651 / 4000) := by
  exact
    packedTile65536 2100875520 2101006592 14 6183 45835 31 _ _ (2146561 / 100000) (536641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2101006592 :
    ThetaLowerSegment 2101006592 2101137664 (8403796993651 / 4000) (210108096176387 / 100000) := by
  exact
    packedTile65536 2101006592 2101137664 14 6136 45836 31 _ _ (2146567 / 100000) (214657 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2101137664 :
    ThetaLowerSegment 2101137664 2101268736 (210108096176387 / 100000)
      (105060538251659 / 50000) := by
  exact
    packedTile65536 2101137664 2101268736 14 6047 45838 31 _ _ (2146573 / 100000) (134161 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2101268736 :
    ThetaLowerSegment 2101268736 2101399808 (105060538251659 / 50000) (8405369658893 / 4000) := by
  exact
    packedTile65536 2101268736 2101399808 14 6133 45839 31 _ _ (2146579 / 100000) (1073291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2101399808 :
    ThetaLowerSegment 2101399808 2101530880 (8405369658893 / 4000) (42029453390021 / 20000) := by
  exact
    packedTile65536 2101399808 2101530880 14 6068 45841 31 _ _ (429317 / 20000) (536647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2101530880 :
    ThetaLowerSegment 2101530880 2101661952 (42029453390021 / 20000)
      (210160513569337 / 100000) := by
  exact
    packedTile65536 2101530880 2101661952 14 6171 45842 31 _ _ (67081 / 3125) (429319 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2101661952 :
    ThetaLowerSegment 2101661952 2101793024 (210160513569337 / 100000)
      (210173644309303 / 100000) := by
  exact
    packedTile65536 2101661952 2101793024 14 6117 45843 31 _ _ (1073299 / 50000) (2146601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2101793024 :
    ThetaLowerSegment 2101793024 2101924096 (210173644309303 / 100000)
      (210186760059743 / 100000) := by
  exact
    packedTile65536 2101793024 2101924096 14 6110 45845 31 _ _ (536651 / 25000) (2146607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2101924096 :
    ThetaLowerSegment 2101924096 2102055168 (210186760059743 / 100000)
      (210199985323953 / 100000) := by
  exact
    packedTile65536 2101924096 2102055168 14 6161 45846 31 _ _ (214661 / 10000) (2146613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102055168 :
    ThetaLowerSegment 2102055168 2102186240 (210199985323953 / 100000)
      (52553260798791 / 25000) := by
  exact
    packedTile65536 2102055168 2102186240 14 6083 45848 31 _ _ (2146617 / 100000) (107331 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102186240 :
    ThetaLowerSegment 2102186240 2102317312 (52553260798791 / 25000)
      (210226062463659 / 100000) := by
  exact
    packedTile65536 2102186240 2102317312 14 6065 45849 31 _ _ (2146623 / 100000) (1073313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102317312 :
    ThetaLowerSegment 2102317312 2102448384 (210226062463659 / 100000)
      (42047845977189 / 20000) := by
  exact
    packedTile65536 2102317312 2102448384 14 6134 45851 31 _ _ (2146629 / 100000) (268329 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102448384 :
    ThetaLowerSegment 2102448384 2102579456 (42047845977189 / 20000) (841009666659 / 400) := by
  exact
    packedTile65536 2102448384 2102579456 14 6143 45852 31 _ _ (429327 / 20000) (1073319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102579456 :
    ThetaLowerSegment 2102579456 2102710528 (841009666659 / 400) (52566422338059 / 25000) := by
  exact
    packedTile65536 2102579456 2102710528 14 6183 45853 31 _ _ (1073321 / 50000) (429329 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102710528 :
    ThetaLowerSegment 2102710528 2102841600 (52566422338059 / 25000) (52569678266413 / 25000) := by
  exact
    packedTile65536 2102710528 2102841600 14 6067 45855 31 _ _ (268331 / 12500) (2146651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102841600 :
    ThetaLowerSegment 2102841600 2102972672 (52569678266413 / 25000) (105145962860511 / 50000) := by
  exact
    packedTile65536 2102841600 2102972672 14 6155 45856 31 _ _ (1073327 / 50000) (2146657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102972672 :
    ThetaLowerSegment 2102972672 2103103744 (105145962860511 / 50000)
      (105152481193601 / 50000) := by
  exact
    packedTile65536 2102972672 2103103744 14 6073 45858 31 _ _ (107333 / 5000) (2146663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2103103744 :
    ThetaLowerSegment 2103103744 2103234816 (105152481193601 / 50000) (52579480990637 / 25000) := by
  exact
    packedTile65536 2103103744 2103234816 14 6038 45859 31 _ _ (2146667 / 100000) (214667 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2103234816 :
    ThetaLowerSegment 2103234816 2103365888 (52579480990637 / 25000)
      (210331063747981 / 100000) := by
  exact
    packedTile65536 2103234816 2103365888 14 6121 45861 31 _ _ (2146673 / 100000) (536669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2103365888 :
    ThetaLowerSegment 2103365888 2103496960 (210331063747981 / 100000)
      (210344072622721 / 100000) := by
  exact
    packedTile65536 2103365888 2103496960 14 6060 45862 31 _ _ (2146679 / 100000) (1073341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2103496960 :
    ThetaLowerSegment 2103496960 2103628032 (210344072622721 / 100000)
      (210357257561991 / 100000) := by
  exact
    packedTile65536 2103496960 2103628032 14 6142 45863 31 _ _ (429337 / 20000) (67084 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2103628032 :
    ThetaLowerSegment 2103628032 2103759104 (210357257561991 / 100000)
      (42074063606007 / 20000) := by
  exact
    packedTile65536 2103628032 2103759104 14 6084 45865 31 _ _ (2146691 / 100000) (1073347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2103759104 :
    ThetaLowerSegment 2103759104 2103890176 (42074063606007 / 20000)
      (210383479435473 / 100000) := by
  exact
    packedTile65536 2103759104 2103890176 14 6131 45866 31 _ _ (1073349 / 50000) (2146701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2103890176 :
    ThetaLowerSegment 2103890176 2104021248 (210383479435473 / 100000)
      (210396445527633 / 100000) := by
  exact
    packedTile65536 2103890176 2104021248 14 6040 45868 31 _ _ (134169 / 6250) (2146707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2104021248 :
    ThetaLowerSegment 2104021248 2104152320 (210396445527633 / 100000)
      (210409667114523 / 100000) := by
  exact
    packedTile65536 2104021248 2104152320 14 6159 45869 31 _ _ (214671 / 10000) (2146713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2104152320 :
    ThetaLowerSegment 2104152320 2104283392 (210409667114523 / 100000)
      (210422796429579 / 100000) := by
  exact
    packedTile65536 2104152320 2104283392 14 6116 45871 31 _ _ (536679 / 25000) (2146719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2104283392 :
    ThetaLowerSegment 2104283392 2104414464 (210422796429579 / 100000)
      (105217976847423 / 50000) := by
  exact
    packedTile65536 2104283392 2104414464 14 6129 45872 31 _ _ (2146723 / 100000) (1073363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2104414464 :
    ThetaLowerSegment 2104414464 2104545536 (105217976847423 / 50000)
      (105224567305453 / 50000) := by
  exact
    packedTile65536 2104414464 2104545536 14 6140 45873 31 _ _ (2146729 / 100000) (536683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2104545536 :
    ThetaLowerSegment 2104545536 2104676608 (105224567305453 / 50000)
      (210462206080321 / 100000) := by
  exact
    packedTile65536 2104545536 2104676608 14 6089 45875 31 _ _ (429347 / 20000) (1073369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2104676608 :
    ThetaLowerSegment 2104676608 2104807680 (210462206080321 / 100000)
      (210475597450679 / 100000) := by
  exact
    packedTile65536 2104676608 2104807680 14 6238 45876 31 _ _ (2146741 / 100000) (268343 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2104807680 :
    ThetaLowerSegment 2104807680 2104938752 (210475597450679 / 100000)
      (52622183348893 / 25000) := by
  exact
    packedTile65536 2104807680 2104938752 14 6119 45878 31 _ _ (2146747 / 100000) (8587 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2104938752 :
    ThetaLowerSegment 2104938752 2105069824 (52622183348893 / 25000) (26312732331191 / 12500) := by
  exact
    packedTile65536 2104938752 2105069824 14 6114 45879 31 _ _ (1073377 / 50000) (2146757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2105069824 :
    ThetaLowerSegment 2105069824 2105200896 (26312732331191 / 12500) (6578595059459 / 3125) := by
  exact
    packedTile65536 2105069824 2105200896 14 6141 45881 31 _ _ (53669 / 2500) (2146763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2105200896 :
    ThetaLowerSegment 2105200896 2105331968 (6578595059459 / 3125) (52632009606013 / 25000) := by
  exact
    packedTile65536 2105200896 2105331968 14 6054 45882 31 _ _ (1073383 / 50000) (2146769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2105331968 :
    ThetaLowerSegment 2105331968 2105463040 (52632009606013 / 25000) (52635332809069 / 25000) := by
  exact
    packedTile65536 2105331968 2105463040 14 6192 45883 31 _ _ (536693 / 25000) (85871 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2105463040 :
    ThetaLowerSegment 2105463040 2105594112 (52635332809069 / 25000)
      (210554433028513 / 100000) := by
  exact
    packedTile65536 2105463040 2105594112 14 6103 45885 31 _ _ (2146779 / 100000) (1073391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2105594112 :
    ThetaLowerSegment 2105594112 2105725184 (210554433028513 / 100000)
      (210567588526993 / 100000) := by
  exact
    packedTile65536 2105594112 2105725184 14 6128 45886 31 _ _ (429357 / 20000) (536697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2105725184 :
    ThetaLowerSegment 2105725184 2105856256 (210567588526993 / 100000)
      (210580576612543 / 100000) := by
  exact
    packedTile65536 2105725184 2105856256 14 6050 45888 31 _ _ (2146791 / 100000) (1073397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2105856256 :
    ThetaLowerSegment 2105856256 2105987328 (210580576612543 / 100000)
      (210593672074243 / 100000) := by
  exact
    packedTile65536 2105856256 2105987328 14 6100 45889 31 _ _ (2146797 / 100000) (5367 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2105987328 :
    ThetaLowerSegment 2105987328 2106118400 (210593672074243 / 100000)
      (210606765431839 / 100000) := by
  exact
    packedTile65536 2105987328 2106118400 14 6099 45891 31 _ _ (536701 / 25000) (2146807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2106118400 :
    ThetaLowerSegment 2106118400 2106249472 (210606765431839 / 100000)
      (210619873853699 / 100000) := by
  exact
    packedTile65536 2106118400 2106249472 14 6106 45892 31 _ _ (214681 / 10000) (2146813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2106249472 :
    ThetaLowerSegment 2106249472 2106380544 (210619873853699 / 100000)
      (42126600756071 / 20000) := by
  exact
    packedTile65536 2106249472 2106380544 14 6116 45893 31 _ _ (67088 / 3125) (2146819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2106380544 :
    ThetaLowerSegment 2106380544 2106511616 (42126600756071 / 20000) (42129198410691 / 20000) := by
  exact
    packedTile65536 2106380544 2106511616 14 6050 45895 31 _ _ (1073411 / 50000) (85873 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2106511616 :
    ThetaLowerSegment 2106511616 2106642688 (42129198410691 / 20000)
      (210658967481887 / 100000) := by
  exact
    packedTile65536 2106511616 2106642688 14 6044 45896 31 _ _ (536707 / 25000) (2146831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2106642688 :
    ThetaLowerSegment 2106642688 2106773760 (210658967481887 / 100000)
      (210671981595657 / 100000) := by
  exact
    packedTile65536 2106642688 2106773760 14 6062 45898 31 _ _ (429367 / 20000) (1073419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2106773760 :
    ThetaLowerSegment 2106773760 2106904832 (210671981595657 / 100000)
      (42137018900097 / 20000) := by
  exact
    packedTile65536 2106773760 2106904832 14 6108 45899 31 _ _ (2146841 / 100000) (536711 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2106904832 :
    ThetaLowerSegment 2106904832 2107035904 (42137018900097 / 20000) (105349106941251 / 50000) := by
  exact
    packedTile65536 2106904832 2107035904 14 6111 45901 31 _ _ (2146847 / 100000) (42937 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2107035904 :
    ThetaLowerSegment 2107035904 2107166976 (105349106941251 / 50000)
      (210711264601889 / 100000) := by
  exact
    packedTile65536 2107035904 2107166976 14 6079 45902 31 _ _ (2146853 / 100000) (268357 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2107166976 :
    ThetaLowerSegment 2107166976 2107298048 (210711264601889 / 100000)
      (210724424853689 / 100000) := by
  exact
    packedTile65536 2107166976 2107298048 14 6130 45903 31 _ _ (107343 / 5000) (2146863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2107298048 :
    ThetaLowerSegment 2107298048 2107429120 (210724424853689 / 100000)
      (210737518589423 / 100000) := by
  exact
    packedTile65536 2107298048 2107429120 14 6099 45905 31 _ _ (1073433 / 50000) (2146869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2107429120 :
    ThetaLowerSegment 2107429120 2107560192 (210737518589423 / 100000)
      (210750708970991 / 100000) := by
  exact
    packedTile65536 2107429120 2107560192 14 6144 45906 31 _ _ (268359 / 12500) (687 / 32)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2107560192 :
    ThetaLowerSegment 2107560192 2107691264 (210750708970991 / 100000)
      (210763815661181 / 100000) := by
  exact
    packedTile65536 2107560192 2107691264 14 6105 45908 31 _ _ (1073439 / 50000) (2146881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2107691264 :
    ThetaLowerSegment 2107691264 2107822336 (210763815661181 / 100000)
      (210776855834597 / 100000) := by
  exact
    packedTile65536 2107691264 2107822336 14 6074 45909 31 _ _ (536721 / 25000) (2146887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2107822336 :
    ThetaLowerSegment 2107822336 2107953408 (210776855834597 / 100000)
      (21079004418601 / 10000) := by
  exact
    packedTile65536 2107822336 2107953408 14 6143 45911 31 _ _ (2146891 / 100000) (1073447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2107953408 :
    ThetaLowerSegment 2107953408 2108084480 (21079004418601 / 10000)
      (210803090879079 / 100000) := by
  exact
    packedTile65536 2107953408 2108084480 14 6077 45912 31 _ _ (2146897 / 100000) (21469 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2108084480 :
    ThetaLowerSegment 2108084480 2108215552 (210803090879079 / 100000)
      (52704059091537 / 25000) := by
  exact
    packedTile65536 2108084480 2108215552 14 6123 45913 31 _ _ (2146903 / 100000) (1073453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2108215552 :
    ThetaLowerSegment 2108215552 2108346624 (52704059091537 / 25000) (105414681283887 / 50000) := by
  exact
    packedTile65536 2108215552 2108346624 14 6114 45915 31 _ _ (2146909 / 100000) (67091 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2108346624 :
    ThetaLowerSegment 2108346624 2108477696 (105414681283887 / 50000)
      (210842512422149 / 100000) := by
  exact
    packedTile65536 2108346624 2108477696 14 6125 45916 31 _ _ (429383 / 20000) (1073459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2108477696 :
    ThetaLowerSegment 2108477696 2108608768 (210842512422149 / 100000)
      (210855741755513 / 100000) := by
  exact
    packedTile65536 2108477696 2108608768 14 6162 45918 31 _ _ (1073461 / 50000) (85877 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2108608768 :
    ThetaLowerSegment 2108608768 2108739840 (210855741755513 / 100000)
      (42173799377797 / 20000) := by
  exact
    packedTile65536 2108608768 2108739840 14 6174 45919 31 _ _ (134183 / 6250) (2146931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2108739840 :
    ThetaLowerSegment 2108739840 2108870912 (42173799377797 / 20000)
      (210881970811147 / 100000) := by
  exact
    packedTile65536 2108739840 2108870912 14 6043 45921 31 _ _ (1073467 / 50000) (2146937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2108870912 :
    ThetaLowerSegment 2108870912 2109001984 (210881970811147 / 100000)
      (210894970532847 / 100000) := by
  exact
    packedTile65536 2108870912 2109001984 14 6055 45922 31 _ _ (107347 / 5000) (2146943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2109001984 :
    ThetaLowerSegment 2109001984 2109133056 (210894970532847 / 100000)
      (105454038822141 / 50000) := by
  exact
    packedTile65536 2109001984 2109133056 14 6105 45923 31 _ _ (2146947 / 100000) (42939 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2109133056 :
    ThetaLowerSegment 2109133056 2109264128 (105454038822141 / 50000)
      (105460531208013 / 50000) := by
  exact
    packedTile65536 2109133056 2109264128 14 6048 45925 31 _ _ (2146953 / 100000) (536739 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2109264128 :
    ThetaLowerSegment 2109264128 2109395200 (105460531208013 / 50000)
      (105467100902553 / 50000) := by
  exact
    packedTile65536 2109264128 2109395200 14 6120 45926 31 _ _ (2146959 / 100000) (1073481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2109395200 :
    ThetaLowerSegment 2109395200 2109526272 (105467100902553 / 50000)
      (210947390611101 / 100000) := by
  exact
    packedTile65536 2109395200 2109526272 14 6143 45928 31 _ _ (429393 / 20000) (268371 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2109526272 :
    ThetaLowerSegment 2109526272 2109657344 (210947390611101 / 100000)
      (21096048498723 / 10000) := by
  exact
    packedTile65536 2109526272 2109657344 14 6099 45929 31 _ _ (2146971 / 100000) (1073487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2109657344 :
    ThetaLowerSegment 2109657344 2109788416 (21096048498723 / 10000) (52743386263601 / 25000) := by
  exact
    packedTile65536 2109657344 2109788416 14 6083 45931 31 _ _ (1073489 / 50000) (2146981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2109788416 :
    ThetaLowerSegment 2109788416 2109919488 (52743386263601 / 25000) (52746711405071 / 25000) := by
  exact
    packedTile65536 2109788416 2109919488 14 6195 45932 31 _ _ (268373 / 12500) (2146987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2109919488 :
    ThetaLowerSegment 2109919488 2110050560 (52746711405071 / 25000) (52750026357631 / 25000) := by
  exact
    packedTile65536 2109919488 2110050560 14 6176 45933 31 _ _ (214699 / 10000) (2146993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110050560 :
    ThetaLowerSegment 2110050560 2110181632 (52750026357631 / 25000) (13188326876067 / 6250) := by
  exact
    packedTile65536 2110050560 2110181632 14 6113 45935 31 _ _ (536749 / 25000) (2146999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110181632 :
    ThetaLowerSegment 2110181632 2110312704 (13188326876067 / 6250) (105513177320149 / 50000) := by
  exact
    packedTile65536 2110181632 2110312704 14 6113 45936 31 _ _ (1073501 / 50000) (429401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110312704 :
    ThetaLowerSegment 2110312704 2110443776 (105513177320149 / 50000)
      (211039380543901 / 100000) := by
  exact
    packedTile65536 2110312704 2110443776 14 6067 45938 31 _ _ (2147009 / 100000) (536753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110443776 :
    ThetaLowerSegment 2110443776 2110574848 (211039380543901 / 100000)
      (105526314886733 / 50000) := by
  exact
    packedTile65536 2110443776 2110574848 14 6171 45939 31 _ _ (429403 / 20000) (1073509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110574848 :
    ThetaLowerSegment 2110574848 2110705920 (105526314886733 / 50000)
      (211065784571133 / 100000) := by
  exact
    packedTile65536 2110574848 2110705920 14 6127 45940 31 _ _ (2147021 / 100000) (134189 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110705920 :
    ThetaLowerSegment 2110705920 2110836992 (211065784571133 / 100000)
      (105539461114673 / 50000) := by
  exact
    packedTile65536 2110705920 2110836992 14 6119 45942 31 _ _ (2147027 / 100000) (214703 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110836992 :
    ThetaLowerSegment 2110836992 2110968064 (105539461114673 / 50000)
      (105545923687013 / 50000) := by
  exact
    packedTile65536 2110836992 2110968064 14 6020 45943 31 _ _ (1073517 / 50000) (2147037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110968064 :
    ThetaLowerSegment 2110968064 2111099136 (105545923687013 / 50000)
      (105552537643733 / 50000) := by
  exact
    packedTile65536 2110968064 2111099136 14 6161 45945 31 _ _ (13419 / 625) (2147043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2111099136 :
    ThetaLowerSegment 2111099136 2111230208 (105552537643733 / 50000)
      (105559081839941 / 50000) := by
  exact
    packedTile65536 2111099136 2111230208 14 6096 45946 31 _ _ (1073523 / 50000) (2147049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2111230208 :
    ThetaLowerSegment 2111230208 2111361280 (105559081839941 / 50000)
      (105565663627847 / 50000) := by
  exact
    packedTile65536 2111230208 2111361280 14 6131 45948 31 _ _ (536763 / 25000) (429411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2111361280 :
    ThetaLowerSegment 2111361280 2111492352 (105565663627847 / 50000)
      (105572207860631 / 50000) := by
  exact
    packedTile65536 2111361280 2111492352 14 6096 45949 31 _ _ (1073529 / 50000) (2147061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2111492352 :
    ThetaLowerSegment 2111492352 2111623424 (105572207860631 / 50000)
      (211157545023737 / 100000) := by
  exact
    packedTile65536 2111492352 2111623424 14 6115 45950 31 _ _ (429413 / 20000) (536767 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2111623424 :
    ThetaLowerSegment 2111623424 2111754496 (211157545023737 / 100000)
      (211170710863109 / 100000) := by
  exact
    packedTile65536 2111623424 2111754496 14 6132 45952 31 _ _ (2147071 / 100000) (1073537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2111754496 :
    ThetaLowerSegment 2111754496 2111885568 (211170710863109 / 100000)
      (211183923974967 / 100000) := by
  exact
    packedTile65536 2111754496 2111885568 14 6154 45953 31 _ _ (2147077 / 100000) (53677 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2111885568 :
    ThetaLowerSegment 2111885568 2112016640 (211183923974967 / 100000) (6599907381589 / 3125) := by
  exact
    packedTile65536 2111885568 2112016640 14 6107 45955 31 _ _ (2147083 / 100000) (1073543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2112016640 :
    ThetaLowerSegment 2112016640 2112147712 (6599907381589 / 3125) (211210251543643 / 100000) := by
  exact
    packedTile65536 2112016640 2112147712 14 6155 45956 31 _ _ (2147089 / 100000) (536773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2112147712 :
    ThetaLowerSegment 2112147712 2112278784 (211210251543643 / 100000)
      (211223269386691 / 100000) := by
  exact
    packedTile65536 2112147712 2112278784 14 6063 45958 31 _ _ (268387 / 12500) (2147099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2112278784 :
    ThetaLowerSegment 2112278784 2112409856 (211223269386691 / 100000)
      (42247261318007 / 20000) := by
  exact
    packedTile65536 2112278784 2112409856 14 6072 45959 31 _ _ (1073551 / 50000) (429421 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2112409856 :
    ThetaLowerSegment 2112409856 2112540928 (42247261318007 / 20000)
      (211249309476083 / 100000) := by
  exact
    packedTile65536 2112409856 2112540928 14 6056 45960 31 _ _ (536777 / 25000) (2147111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2112540928 :
    ThetaLowerSegment 2112540928 2112672000 (211249309476083 / 100000)
      (211262565757919 / 100000) := by
  exact
    packedTile65536 2112540928 2112672000 14 6174 45962 31 _ _ (1073557 / 50000) (2147117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2112672000 :
    ThetaLowerSegment 2112672000 2112803072 (211262565757919 / 100000)
      (211275553686799 / 100000) := by
  exact
    packedTile65536 2112672000 2112803072 14 6049 45963 31 _ _ (26839 / 1250) (2147123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2112803072 :
    ThetaLowerSegment 2112803072 2112934144 (211275553686799 / 100000)
      (211288728458071 / 100000) := by
  exact
    packedTile65536 2112803072 2112934144 14 6136 45965 31 _ _ (2147127 / 100000) (214713 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2112934144 :
    ThetaLowerSegment 2112934144 2113065216 (211288728458071 / 100000) (8452072008151 / 4000) := by
  exact
    packedTile65536 2112934144 2113065216 14 6088 45966 31 _ _ (2147133 / 100000) (67098 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2113065216 :
    ThetaLowerSegment 2113065216 2113196288 (8452072008151 / 4000) (52828781873887 / 25000) := by
  exact
    packedTile65536 2113065216 2113196288 14 6207 45968 31 _ _ (2147139 / 100000) (1073571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2113196288 :
    ThetaLowerSegment 2113196288 2113327360 (52828781873887 / 25000) (26416017399281 / 12500) := by
  exact
    packedTile65536 2113196288 2113327360 14 6060 45969 31 _ _ (429429 / 20000) (536787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2113327360 :
    ThetaLowerSegment 2113327360 2113458432 (26416017399281 / 12500) (26417653528343 / 12500) := by
  exact
    packedTile65536 2113327360 2113458432 14 6096 45970 31 _ _ (2147151 / 100000) (1073577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2113458432 :
    ThetaLowerSegment 2113458432 2113589504 (26417653528343 / 12500) (21135442680697 / 10000) := by
  exact
    packedTile65536 2113458432 2113589504 14 6147 45972 31 _ _ (1073579 / 50000) (2147161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2113589504 :
    ThetaLowerSegment 2113589504 2113720576 (21135442680697 / 10000) (21136754597901 / 10000) := by
  exact
    packedTile65536 2113589504 2113720576 14 6110 45973 31 _ _ (536791 / 25000) (2147167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2113720576 :
    ThetaLowerSegment 2113720576 2113851648 (21136754597901 / 10000) (4227611242471 / 2000) := by
  exact
    packedTile65536 2113720576 2113851648 14 6062 45975 31 _ _ (214717 / 10000) (2147173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2113851648 :
    ThetaLowerSegment 2113851648 2113982720 (4227611242471 / 2000) (105696869671331 / 50000) := by
  exact
    packedTile65536 2113851648 2113982720 14 6137 45976 31 _ _ (268397 / 12500) (2147179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2113982720 :
    ThetaLowerSegment 2113982720 2114113792 (105696869671331 / 50000)
      (105703437901069 / 50000) := by
  exact
    packedTile65536 2113982720 2114113792 14 6118 45978 31 _ _ (1073591 / 50000) (429437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2114113792 :
    ThetaLowerSegment 2114113792 2114244864 (105703437901069 / 50000) (52855018106433 / 25000) := by
  exact
    packedTile65536 2114113792 2114244864 14 6146 45979 31 _ _ (2147189 / 100000) (268399 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2114244864 :
    ThetaLowerSegment 2114244864 2114375936 (52855018106433 / 25000) (52858372025023 / 25000) := by
  exact
    packedTile65536 2114244864 2114375936 14 6248 45980 31 _ _ (429439 / 20000) (1073599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2114375936 :
    ThetaLowerSegment 2114375936 2114507008 (52858372025023 / 25000)
      (211446751360669 / 100000) := by
  exact
    packedTile65536 2114375936 2114507008 14 6177 45982 31 _ _ (2147201 / 100000) (536801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2114507008 :
    ThetaLowerSegment 2114507008 2114638080 (211446751360669 / 100000)
      (211459965272547 / 100000) := by
  exact
    packedTile65536 2114507008 2114638080 14 6154 45983 31 _ _ (2147207 / 100000) (214721 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2114638080 :
    ThetaLowerSegment 2114638080 2114769152 (211459965272547 / 100000)
      (26434121367711 / 12500) := by
  exact
    packedTile65536 2114638080 2114769152 14 6057 45985 31 _ _ (2147213 / 100000) (134201 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2114769152 :
    ThetaLowerSegment 2114769152 2114900224 (26434121367711 / 12500) (52871482353597 / 25000) := by
  exact
    packedTile65536 2114769152 2114900224 14 6035 45986 31 _ _ (107361 / 5000) (2147223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2114900224 :
    ThetaLowerSegment 2114900224 2115031296 (52871482353597 / 25000) (52874754726021 / 25000) := by
  exact
    packedTile65536 2114900224 2115031296 14 6096 45988 31 _ _ (1073613 / 50000) (2147229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2115031296 :
    ThetaLowerSegment 2115031296 2115162368 (52874754726021 / 25000) (52878022276317 / 25000) := by
  exact
    packedTile65536 2115031296 2115162368 14 6087 45989 31 _ _ (67101 / 3125) (429447 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2115162368 :
    ThetaLowerSegment 2115162368 2115293440 (52878022276317 / 25000) (52881275341887 / 25000) := by
  exact
    packedTile65536 2115162368 2115293440 14 6060 45990 31 _ _ (1073619 / 50000) (2147241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2115293440 :
    ThetaLowerSegment 2115293440 2115424512 (52881275341887 / 25000) (52884545594499 / 25000) := by
  exact
    packedTile65536 2115293440 2115424512 14 6092 45992 31 _ _ (536811 / 25000) (2147247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2115424512 :
    ThetaLowerSegment 2115424512 2115555584 (52884545594499 / 25000) (105775599506779 / 50000) := by
  exact
    packedTile65536 2115424512 2115555584 14 6062 45993 31 _ _ (2147251 / 100000) (1073627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2115555584 :
    ThetaLowerSegment 2115555584 2115686656 (105775599506779 / 50000)
      (105782178702227 / 50000) := by
  exact
    packedTile65536 2115555584 2115686656 14 6128 45995 31 _ _ (2147257 / 100000) (107363 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2115686656 :
    ThetaLowerSegment 2115686656 2115817728 (105782178702227 / 50000) (52894328497349 / 25000) := by
  exact
    packedTile65536 2115686656 2115817728 14 6034 45996 31 _ _ (2147263 / 100000) (1073633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2115817728 :
    ThetaLowerSegment 2115817728 2115948800 (52894328497349 / 25000)
      (211590466012021 / 100000) := by
  exact
    packedTile65536 2115817728 2115948800 14 6125 45998 31 _ _ (2147269 / 100000) (268409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2115948800 :
    ThetaLowerSegment 2115948800 2116079872 (211590466012021 / 100000)
      (211603487087621 / 100000) := by
  exact
    packedTile65536 2115948800 2116079872 14 6064 45999 31 _ _ (85891 / 4000) (1073639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2116079872 :
    ThetaLowerSegment 2116079872 2116210944 (211603487087621 / 100000)
      (211616626306179 / 100000) := by
  exact
    packedTile65536 2116079872 2116210944 14 6119 46000 31 _ _ (1073641 / 50000) (429457 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2116210944 :
    ThetaLowerSegment 2116210944 2116342016 (211616626306179 / 100000)
      (211629875073139 / 100000) := by
  exact
    packedTile65536 2116210944 2116342016 14 6170 46002 31 _ _ (268411 / 12500) (2147291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2116342016 :
    ThetaLowerSegment 2116342016 2116473088 (211629875073139 / 100000)
      (211643162528411 / 100000) := by
  exact
    packedTile65536 2116342016 2116473088 14 6188 46003 31 _ _ (1073647 / 50000) (2147297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2116473088 :
    ThetaLowerSegment 2116473088 2116604160 (211643162528411 / 100000)
      (211656310446311 / 100000) := by
  exact
    packedTile65536 2116473088 2116604160 14 6123 46005 31 _ _ (21473 / 1000) (2147303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2116604160 :
    ThetaLowerSegment 2116604160 2116735232 (211656310446311 / 100000)
      (211669282321857 / 100000) := by
  exact
    packedTile65536 2116604160 2116735232 14 6041 46006 31 _ _ (1073653 / 50000) (2147309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2116735232 :
    ThetaLowerSegment 2116735232 2116866304 (211669282321857 / 100000) (13230154579101 / 6250) := by
  exact
    packedTile65536 2116735232 2116866304 14 6143 46007 31 _ _ (2147313 / 100000) (536829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2116866304 :
    ThetaLowerSegment 2116866304 2116997376 (13230154579101 / 6250) (4233910836981 / 2000) := by
  exact
    packedTile65536 2116866304 2116997376 14 6086 46009 31 _ _ (2147319 / 100000) (1073661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2116997376 :
    ThetaLowerSegment 2116997376 2117128448 (4233910836981 / 2000) (1693667595357 / 800) := by
  exact
    packedTile65536 2116997376 2117128448 14 6011 46010 31 _ _ (85893 / 4000) (67104 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2117128448 :
    ThetaLowerSegment 2117128448 2117259520 (1693667595357 / 800) (52930406897493 / 25000) := by
  exact
    packedTile65536 2117128448 2117259520 14 6137 46012 31 _ _ (2147331 / 100000) (1073667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2117259520 :
    ThetaLowerSegment 2117259520 2117390592 (52930406897493 / 25000)
      (211734578179419 / 100000) := by
  exact
    packedTile65536 2117259520 2117390592 14 6031 46013 31 _ _ (2147337 / 100000) (107367 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2117390592 :
    ThetaLowerSegment 2117390592 2117521664 (211734578179419 / 100000)
      (211747734956107 / 100000) := by
  exact
    packedTile65536 2117390592 2117521664 14 6127 46015 31 _ _ (134209 / 6250) (2147347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2117521664 :
    ThetaLowerSegment 2117521664 2117652736 (211747734956107 / 100000)
      (211760767223257 / 100000) := by
  exact
    packedTile65536 2117521664 2117652736 14 6069 46016 31 _ _ (42947 / 2000) (2147353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2117652736 :
    ThetaLowerSegment 2117652736 2117783808 (211760767223257 / 100000)
      (211773747990277 / 100000) := by
  exact
    packedTile65536 2117652736 2117783808 14 6045 46017 31 _ _ (536839 / 25000) (2147359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2117783808 :
    ThetaLowerSegment 2117783808 2117914880 (211773747990277 / 100000)
      (211787061634677 / 100000) := by
  exact
    packedTile65536 2117783808 2117914880 14 6200 46019 31 _ _ (1073681 / 50000) (429473 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2117914880 :
    ThetaLowerSegment 2117914880 2118045952 (211787061634677 / 100000)
      (211800197084733 / 100000) := by
  exact
    packedTile65536 2117914880 2118045952 14 6117 46020 31 _ _ (268421 / 12500) (2147371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118045952 :
    ThetaLowerSegment 2118045952 2118177024 (211800197084733 / 100000) (1694506505961 / 800) := by
  exact
    packedTile65536 2118045952 2118177024 14 6108 46022 31 _ _ (1073687 / 50000) (2147377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118177024 :
    ThetaLowerSegment 2118177024 2118308096 (1694506505961 / 800) (52956615414747 / 25000) := by
  exact
    packedTile65536 2118177024 2118308096 14 6123 46023 31 _ _ (2147381 / 100000) (268423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118308096 :
    ThetaLowerSegment 2118308096 2118439168 (52956615414747 / 25000)
      (211839549982753 / 100000) := by
  exact
    packedTile65536 2118308096 2118439168 14 6095 46025 31 _ _ (2147387 / 100000) (214739 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118439168 :
    ThetaLowerSegment 2118439168 2118570240 (211839549982753 / 100000)
      (26481594824637 / 12500) := by
  exact
    packedTile65536 2118439168 2118570240 14 6151 46026 31 _ _ (2147393 / 100000) (536849 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118570240 :
    ThetaLowerSegment 2118570240 2118701312 (26481594824637 / 12500) (423731268803 / 200) := by
  exact
    packedTile65536 2118570240 2118701312 14 5996 46027 31 _ _ (2147399 / 100000) (1073701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118701312 :
    ThetaLowerSegment 2118701312 2118832384 (423731268803 / 200) (42375746284919 / 20000) := by
  exact
    packedTile65536 2118701312 2118832384 14 6099 46029 31 _ _ (429481 / 20000) (134213 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118832384 :
    ThetaLowerSegment 2118832384 2118963456 (42375746284919 / 20000)
      (211891807016263 / 100000) := by
  exact
    packedTile65536 2118832384 2118963456 14 6089 46030 31 _ _ (536853 / 25000) (429483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118963456 :
    ThetaLowerSegment 2118963456 2119094528 (211891807016263 / 100000)
      (42380965791803 / 20000) := by
  exact
    packedTile65536 2118963456 2119094528 14 6064 46032 31 _ _ (1073709 / 50000) (2147421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2119094528 :
    ThetaLowerSegment 2119094528 2119225600 (42380965791803 / 20000)
      (211917975488743 / 100000) := by
  exact
    packedTile65536 2119094528 2119225600 14 6122 46033 31 _ _ (67107 / 3125) (2147427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2119225600 :
    ThetaLowerSegment 2119225600 2119356672 (211917975488743 / 100000)
      (211931165003803 / 100000) := by
  exact
    packedTile65536 2119225600 2119356672 14 6142 46035 31 _ _ (214743 / 10000) (2147433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2119356672 :
    ThetaLowerSegment 2119356672 2119487744 (211931165003803 / 100000)
      (211944315901867 / 100000) := by
  exact
    packedTile65536 2119356672 2119487744 14 6124 46036 31 _ _ (536859 / 25000) (2147439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2119487744 :
    ThetaLowerSegment 2119487744 2119618816 (211944315901867 / 100000)
      (211957484022343 / 100000) := by
  exact
    packedTile65536 2119487744 2119618816 14 6132 46037 31 _ _ (2147443 / 100000) (1073723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2119618816 :
    ThetaLowerSegment 2119618816 2119749888 (211957484022343 / 100000)
      (42394111538371 / 20000) := by
  exact
    packedTile65536 2119618816 2119749888 14 6088 46039 31 _ _ (2147449 / 100000) (536863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2119749888 :
    ThetaLowerSegment 2119749888 2119880960 (42394111538371 / 20000) (10599183609977 / 5000) := by
  exact
    packedTile65536 2119749888 2119880960 14 6107 46040 31 _ _ (429491 / 20000) (1073729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2119880960 :
    ThetaLowerSegment 2119880960 2120012032 (10599183609977 / 5000) (211996881232151 / 100000) := by
  exact
    packedTile65536 2119880960 2120012032 14 6151 46042 31 _ _ (2147461 / 100000) (268433 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2120012032 :
    ThetaLowerSegment 2120012032 2120143104 (211996881232151 / 100000)
      (106005025823631 / 50000) := by
  exact
    packedTile65536 2120012032 2120143104 14 6133 46043 31 _ _ (2147467 / 100000) (214747 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2120143104 :
    ThetaLowerSegment 2120143104 2120274176 (106005025823631 / 50000) (53005745932417 / 25000) := by
  exact
    packedTile65536 2120143104 2120274176 14 6022 46045 31 _ _ (2147473 / 100000) (536869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2120274176 :
    ThetaLowerSegment 2120274176 2120405248 (53005745932417 / 25000) (53009013860107 / 25000) := by
  exact
    packedTile65536 2120274176 2120405248 14 6087 46046 31 _ _ (53687 / 2500) (2147483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2120405248 :
    ThetaLowerSegment 2120405248 2120536320 (53009013860107 / 25000) (53012247974023 / 25000) := by
  exact
    packedTile65536 2120405248 2120536320 14 6024 46047 31 _ _ (1073743 / 50000) (2147489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2120536320 :
    ThetaLowerSegment 2120536320 2120667392 (53012247974023 / 25000) (6626935866104 / 3125) := by
  exact
    packedTile65536 2120536320 2120667392 14 6033 46049 31 _ _ (536873 / 25000) (429499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2120667392 :
    ThetaLowerSegment 2120667392 2120798464 (6626935866104 / 3125) (106037520505317 / 50000) := by
  exact
    packedTile65536 2120667392 2120798464 14 6097 46050 31 _ _ (1073749 / 50000) (2147501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2120798464 :
    ThetaLowerSegment 2120798464 2120929536 (106037520505317 / 50000)
      (106044089720053 / 50000) := by
  exact
    packedTile65536 2120798464 2120929536 14 6118 46052 31 _ _ (134219 / 6250) (2147507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2120929536 :
    ThetaLowerSegment 2120929536 2121060608 (106044089720053 / 50000) (10605071908651 / 5000) := by
  exact
    packedTile65536 2120929536 2121060608 14 6174 46053 31 _ _ (2147511 / 100000) (1073757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121060608 :
    ThetaLowerSegment 2121060608 2121191680 (10605071908651 / 5000) (1060573119637 / 500) := by
  exact
    packedTile65536 2121060608 2121191680 14 6140 46054 31 _ _ (2147517 / 100000) (13422 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121191680 :
    ThetaLowerSegment 2121191680 2121322752 (1060573119637 / 500) (212127700194947 / 100000) := by
  exact
    packedTile65536 2121191680 2121322752 14 6089 46056 31 _ _ (2147523 / 100000) (1073763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121322752 :
    ThetaLowerSegment 2121322752 2121339136 (212127700194947 / 100000)
      (212129362382393 / 100000) := by
  exact
    packedTile65536 2121322752 2121339136 11 774 46057 31 _ _ (2147529 / 100000) (536883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121339136 :
    ThetaLowerSegment 2121339136 2121341184 (212129362382393 / 100000)
      (212129564250213 / 100000) := by
  exact
    packedTile65536 2121339136 2121341184 8 94 46057 31 _ _ (214753 / 10000) (2147533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2089341184_2121341184 :
    ThetaLowerSegment 2089341184 2121341184 (104463976484627 / 50000)
      (212129564250213 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2089341184 cell2089472256)
                  (ThetaLowerSegment.join cell2089603328 cell2089734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2089865472 cell2089996544)
                  (ThetaLowerSegment.join cell2090127616 cell2090258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2090389760 cell2090520832)
                  (ThetaLowerSegment.join cell2090651904 cell2090782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2090914048 cell2091045120)
                  (ThetaLowerSegment.join cell2091176192 cell2091307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2091438336 cell2091569408)
                  (ThetaLowerSegment.join cell2091700480 cell2091831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2091962624 cell2092093696)
                  (ThetaLowerSegment.join cell2092224768 cell2092355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2092486912 cell2092617984)
                  (ThetaLowerSegment.join cell2092749056 cell2092880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2093011200 cell2093142272)
                  (ThetaLowerSegment.join cell2093273344 cell2093404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2093535488 cell2093666560)
                  (ThetaLowerSegment.join cell2093797632 cell2093928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2094059776 cell2094190848)
                  (ThetaLowerSegment.join cell2094321920 cell2094452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2094584064 cell2094715136)
                  (ThetaLowerSegment.join cell2094846208 cell2094977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2095108352 cell2095239424)
                  (ThetaLowerSegment.join cell2095370496 cell2095501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2095632640 cell2095763712)
                  (ThetaLowerSegment.join cell2095894784 cell2096025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2096156928 cell2096288000)
                  (ThetaLowerSegment.join cell2096419072 cell2096550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2096681216 cell2096812288)
                  (ThetaLowerSegment.join cell2096943360 cell2097074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2097205504 cell2097336576)
                  (ThetaLowerSegment.join cell2097467648 cell2097598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2097729792 cell2097860864)
                  (ThetaLowerSegment.join cell2097991936 cell2098123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2098254080 cell2098385152)
                  (ThetaLowerSegment.join cell2098516224 cell2098647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2098778368 cell2098909440)
                  (ThetaLowerSegment.join cell2099040512 cell2099171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2099302656 cell2099433728)
                  (ThetaLowerSegment.join cell2099564800 cell2099695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2099826944 cell2099958016)
                  (ThetaLowerSegment.join cell2100089088 cell2100220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2100351232 cell2100482304)
                  (ThetaLowerSegment.join cell2100613376 cell2100744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2100875520 cell2101006592)
                  (ThetaLowerSegment.join cell2101137664 cell2101268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2101399808 cell2101530880)
                  (ThetaLowerSegment.join cell2101661952 cell2101793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2101924096 cell2102055168)
                  (ThetaLowerSegment.join cell2102186240 cell2102317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2102448384 cell2102579456)
                  (ThetaLowerSegment.join cell2102710528 cell2102841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2102972672 cell2103103744)
                  (ThetaLowerSegment.join cell2103234816 cell2103365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2103496960 cell2103628032)
                  (ThetaLowerSegment.join cell2103759104 cell2103890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2104021248 cell2104152320)
                  (ThetaLowerSegment.join cell2104283392 cell2104414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2104545536 cell2104676608)
                  (ThetaLowerSegment.join cell2104807680 cell2104938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2105069824 cell2105200896)
                  (ThetaLowerSegment.join cell2105331968 cell2105463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2105594112 cell2105725184)
                  (ThetaLowerSegment.join cell2105856256 cell2105987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2106118400 cell2106249472)
                  (ThetaLowerSegment.join cell2106380544 cell2106511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2106642688 cell2106773760)
                  (ThetaLowerSegment.join cell2106904832 cell2107035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2107166976 cell2107298048)
                  (ThetaLowerSegment.join cell2107429120 cell2107560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2107691264 cell2107822336)
                  (ThetaLowerSegment.join cell2107953408 cell2108084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2108215552 cell2108346624)
                  (ThetaLowerSegment.join cell2108477696 cell2108608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2108739840 cell2108870912)
                  (ThetaLowerSegment.join cell2109001984 cell2109133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2109264128 cell2109395200)
                  (ThetaLowerSegment.join cell2109526272 cell2109657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2109788416 cell2109919488)
                  (ThetaLowerSegment.join cell2110050560 cell2110181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2110312704 cell2110443776)
                  (ThetaLowerSegment.join cell2110574848 cell2110705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2110836992 cell2110968064)
                  (ThetaLowerSegment.join cell2111099136 cell2111230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2111361280 cell2111492352)
                  (ThetaLowerSegment.join cell2111623424 cell2111754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2111885568 cell2112016640)
                  (ThetaLowerSegment.join cell2112147712 cell2112278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2112409856 cell2112540928)
                  (ThetaLowerSegment.join cell2112672000 cell2112803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2112934144 cell2113065216)
                  (ThetaLowerSegment.join cell2113196288 cell2113327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2113458432 cell2113589504)
                  (ThetaLowerSegment.join cell2113720576 cell2113851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2113982720 cell2114113792)
                  (ThetaLowerSegment.join cell2114244864 cell2114375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2114507008 cell2114638080)
                  (ThetaLowerSegment.join cell2114769152 cell2114900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2115031296 cell2115162368)
                  (ThetaLowerSegment.join cell2115293440 cell2115424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2115555584 cell2115686656)
                  (ThetaLowerSegment.join cell2115817728 cell2115948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2116079872 cell2116210944)
                  (ThetaLowerSegment.join cell2116342016 cell2116473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2116604160 cell2116735232)
                  (ThetaLowerSegment.join cell2116866304 cell2116997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2117128448 cell2117259520)
                  (ThetaLowerSegment.join cell2117390592 cell2117521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2117652736 cell2117783808)
                  (ThetaLowerSegment.join cell2117914880 cell2118045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2118177024 cell2118308096)
                  (ThetaLowerSegment.join cell2118439168 cell2118570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2118701312 cell2118832384)
                  (ThetaLowerSegment.join cell2118963456 cell2119094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2119225600 cell2119356672)
                  (ThetaLowerSegment.join cell2119487744 cell2119618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2119749888 cell2119880960)
                  (ThetaLowerSegment.join cell2120012032 cell2120143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2120274176 cell2120405248)
                  (ThetaLowerSegment.join cell2120536320 cell2120667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2120798464 cell2120929536)
                (ThetaLowerSegment.join cell2121060608 cell2121191680))
              (ThetaLowerSegment.join cell2121322752 cell2121339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
