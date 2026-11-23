/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 204712192 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell177432832 :
    ThetaLowerSegment 177432832 177465600 (17742096478069 / 100000) (8872678881661 / 50000) := by
  exact
    packedTile16384 177432832 177465600 12 1717 13320 27 _ _ (1899409 / 100000) (474853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177465600 :
    ThetaLowerSegment 177465600 177498368 (8872678881661 / 50000) (443717233957 / 2500) := by
  exact
    packedTile16384 177465600 177498368 12 1754 13321 27 _ _ (1899427 / 100000) (189943 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177498368 :
    ThetaLowerSegment 177498368 177531136 (443717233957 / 2500) (8876007644113 / 50000) := by
  exact
    packedTile16384 177498368 177531136 12 1751 13322 27 _ _ (949723 / 50000) (1899449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177531136 :
    ThetaLowerSegment 177531136 177563904 (8876007644113 / 50000) (8877597495481 / 50000) := by
  exact
    packedTile16384 177531136 177563904 12 1674 13324 27 _ _ (237433 / 12500) (1899467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177563904 :
    ThetaLowerSegment 177563904 177596672 (8877597495481 / 50000) (8879272839487 / 50000) := by
  exact
    packedTile16384 177563904 177596672 12 1764 13325 27 _ _ (1899483 / 100000) (949743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177596672 :
    ThetaLowerSegment 177596672 177629440 (8879272839487 / 50000) (17761727343149 / 100000) := by
  exact
    packedTile16384 177596672 177629440 12 1675 13326 27 _ _ (1899501 / 100000) (118719 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177629440 :
    ThetaLowerSegment 177629440 177662208 (17761727343149 / 100000) (17765004015149 / 100000) := by
  exact
    packedTile16384 177629440 177662208 12 1725 13327 27 _ _ (11872 / 625) (1899523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177662208 :
    ThetaLowerSegment 177662208 177694976 (17765004015149 / 100000) (17768263622357 / 100000) := by
  exact
    packedTile16384 177662208 177694976 12 1716 13328 27 _ _ (949769 / 50000) (1899541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177694976 :
    ThetaLowerSegment 177694976 177727744 (17768263622357 / 100000) (17771568849797 / 100000) := by
  exact
    packedTile16384 177694976 177727744 12 1740 13330 27 _ _ (474889 / 25000) (1899559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177727744 :
    ThetaLowerSegment 177727744 177760512 (17771568849797 / 100000) (8887424707911 / 50000) := by
  exact
    packedTile16384 177727744 177760512 12 1727 13331 27 _ _ (75983 / 4000) (949789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177760512 :
    ThetaLowerSegment 177760512 177793280 (8887424707911 / 50000) (17778183201537 / 100000) := by
  exact
    packedTile16384 177760512 177793280 12 1755 13332 27 _ _ (1899593 / 100000) (474899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177793280 :
    ThetaLowerSegment 177793280 177826048 (17778183201537 / 100000) (17781482827581 / 100000) := by
  exact
    packedTile16384 177793280 177826048 12 1737 13333 27 _ _ (474903 / 25000) (379923 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177826048 :
    ThetaLowerSegment 177826048 177858816 (17781482827581 / 100000) (17784717897471 / 100000) := by
  exact
    packedTile16384 177826048 177858816 12 1703 13335 27 _ _ (189963 / 10000) (1899633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177858816 :
    ThetaLowerSegment 177858816 177891584 (17784717897471 / 100000) (4447013895191 / 25000) := by
  exact
    packedTile16384 177858816 177891584 12 1757 13336 27 _ _ (1899649 / 100000) (474913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177891584 :
    ThetaLowerSegment 177891584 177924352 (4447013895191 / 25000) (17791332506339 / 100000) := by
  exact
    packedTile16384 177891584 177924352 12 1725 13337 27 _ _ (1899667 / 100000) (189967 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177924352 :
    ThetaLowerSegment 177924352 177957120 (17791332506339 / 100000) (17794622760759 / 100000) := by
  exact
    packedTile16384 177924352 177957120 12 1732 13338 27 _ _ (379937 / 20000) (237461 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177957120 :
    ThetaLowerSegment 177957120 177989888 (17794622760759 / 100000) (17797960540687 / 100000) := by
  exact
    packedTile16384 177957120 177989888 12 1757 13340 27 _ _ (237463 / 12500) (1899707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177989888 :
    ThetaLowerSegment 177989888 178022656 (17797960540687 / 100000) (17801247059747 / 100000) := by
  exact
    packedTile16384 177989888 178022656 12 1730 13341 27 _ _ (949861 / 50000) (75989 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178022656 :
    ThetaLowerSegment 178022656 178055424 (17801247059747 / 100000) (2225564564251 / 12500) := by
  exact
    packedTile16384 178022656 178055424 12 1721 13342 27 _ _ (1899741 / 100000) (59367 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178055424 :
    ThetaLowerSegment 178055424 178088192 (2225564564251 / 12500) (3561561759271 / 20000) := by
  exact
    packedTile16384 178055424 178088192 12 1733 13343 27 _ _ (1899759 / 100000) (949881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178088192 :
    ThetaLowerSegment 178088192 178120960 (3561561759271 / 20000) (17811167602091 / 100000) := by
  exact
    packedTile16384 178088192 178120960 12 1768 13344 27 _ _ (1899777 / 100000) (94989 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178120960 :
    ThetaLowerSegment 178120960 178153728 (17811167602091 / 100000) (17814475146927 / 100000) := by
  exact
    packedTile16384 178120960 178153728 12 1741 13346 27 _ _ (474949 / 25000) (1899799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178153728 :
    ThetaLowerSegment 178153728 178186496 (17814475146927 / 100000) (17817759925333 / 100000) := by
  exact
    packedTile16384 178153728 178186496 12 1729 13347 27 _ _ (949907 / 50000) (1899817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178186496 :
    ThetaLowerSegment 178186496 178219264 (17817759925333 / 100000) (17821065634753 / 100000) := by
  exact
    packedTile16384 178186496 178219264 12 1740 13348 27 _ _ (1899833 / 100000) (474959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178219264 :
    ThetaLowerSegment 178219264 178252032 (17821065634753 / 100000) (8912188537523 / 50000) := by
  exact
    packedTile16384 178219264 178252032 12 1743 13349 27 _ _ (1899851 / 100000) (949927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178252032 :
    ThetaLowerSegment 178252032 178284800 (8912188537523 / 50000) (17827566955097 / 100000) := by
  exact
    packedTile16384 178252032 178284800 12 1679 13351 27 _ _ (1899869 / 100000) (59371 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178284800 :
    ThetaLowerSegment 178284800 178317568 (17827566955097 / 100000) (17830690370969 / 100000) := by
  exact
    packedTile16384 178284800 178317568 12 1644 13352 27 _ _ (118743 / 6250) (1899891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178317568 :
    ThetaLowerSegment 178317568 178350336 (17830690370969 / 100000) (17833954409477 / 100000) := by
  exact
    packedTile16384 178317568 178350336 12 1718 13353 27 _ _ (949953 / 50000) (1899909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178350336 :
    ThetaLowerSegment 178350336 178383104 (17833954409477 / 100000) (17837229880177 / 100000) := by
  exact
    packedTile16384 178350336 178383104 12 1724 13354 27 _ _ (75997 / 4000) (237491 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178383104 :
    ThetaLowerSegment 178383104 178415872 (17837229880177 / 100000) (17840512981681 / 100000) := by
  exact
    packedTile16384 178383104 178415872 12 1728 13356 27 _ _ (1899943 / 100000) (949973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178415872 :
    ThetaLowerSegment 178415872 178448640 (17840512981681 / 100000) (1784372201581 / 10000) := by
  exact
    packedTile16384 178415872 178448640 12 1689 13357 27 _ _ (1899961 / 100000) (474991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178448640 :
    ThetaLowerSegment 178448640 178481408 (1784372201581 / 10000) (1784701658113 / 10000) := by
  exact
    packedTile16384 178448640 178481408 12 1734 13358 27 _ _ (94999 / 5000) (1899983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178481408 :
    ThetaLowerSegment 178481408 178514176 (1784701658113 / 10000) (1115639579859 / 6250) := by
  exact
    packedTile16384 178481408 178514176 12 1693 13359 27 _ _ (949999 / 50000) (1900001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178514176 :
    ThetaLowerSegment 178514176 178546944 (1115639579859 / 6250) (557923518928 / 3125) := by
  exact
    packedTile16384 178514176 178546944 12 1747 13360 27 _ _ (118751 / 6250) (1900019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178546944 :
    ThetaLowerSegment 178546944 178579712 (557923518928 / 3125) (17856833966141 / 100000) := by
  exact
    packedTile16384 178546944 178579712 12 1727 13362 27 _ _ (380007 / 20000) (950019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178579712 :
    ThetaLowerSegment 178579712 178612480 (17856833966141 / 100000) (3572019651439 / 20000) := by
  exact
    packedTile16384 178579712 178612480 12 1718 13363 27 _ _ (1900053 / 100000) (237507 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178612480 :
    ThetaLowerSegment 178612480 178645248 (3572019651439 / 20000) (558228952432 / 3125) := by
  exact
    packedTile16384 178612480 178645248 12 1699 13364 27 _ _ (1900071 / 100000) (950037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178645248 :
    ThetaLowerSegment 178645248 178678016 (558228952432 / 3125) (8933326767707 / 50000) := by
  exact
    packedTile16384 178645248 178678016 12 1751 13365 27 _ _ (190009 / 10000) (1900093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178678016 :
    ThetaLowerSegment 178678016 178710784 (8933326767707 / 50000) (357398320417 / 2000) := by
  exact
    packedTile16384 178678016 178710784 12 1717 13367 27 _ _ (475027 / 25000) (1900111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178710784 :
    ThetaLowerSegment 178710784 178743552 (357398320417 / 2000) (4468291784109 / 25000) := by
  exact
    packedTile16384 178710784 178743552 12 1711 13368 27 _ _ (950063 / 50000) (1900129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178743552 :
    ThetaLowerSegment 178743552 178776320 (4468291784109 / 25000) (17876467688301 / 100000) := by
  exact
    packedTile16384 178743552 178776320 12 1737 13369 27 _ _ (380029 / 20000) (475037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178776320 :
    ThetaLowerSegment 178776320 178809088 (17876467688301 / 100000) (1117484566883 / 6250) := by
  exact
    packedTile16384 178776320 178809088 12 1729 13370 27 _ _ (1900163 / 100000) (950083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178809088 :
    ThetaLowerSegment 178809088 178841856 (1117484566883 / 6250) (1788306318543 / 10000) := by
  exact
    packedTile16384 178809088 178841856 12 1742 13371 27 _ _ (1900181 / 100000) (237523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178841856 :
    ThetaLowerSegment 178841856 178874624 (1788306318543 / 10000) (1788642463923 / 10000) := by
  exact
    packedTile16384 178841856 178874624 12 1769 13373 27 _ _ (9501 / 500) (1900203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178874624 :
    ThetaLowerSegment 178874624 178907392 (1788642463923 / 10000) (8944867409493 / 50000) := by
  exact
    packedTile16384 178874624 178907392 12 1742 13374 27 _ _ (950109 / 50000) (1900221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178907392 :
    ThetaLowerSegment 178907392 178940160 (8944867409493 / 50000) (1789295381877 / 10000) := by
  exact
    packedTile16384 178907392 178940160 12 1694 13375 27 _ _ (475059 / 25000) (1900239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178940160 :
    ThetaLowerSegment 178940160 178972928 (1789295381877 / 10000) (1789616905023 / 10000) := by
  exact
    packedTile16384 178940160 178972928 12 1692 13376 27 _ _ (380051 / 20000) (950129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell178972928 :
    ThetaLowerSegment 178972928 179005696 (1789616905023 / 10000) (8949730161533 / 50000) := by
  exact
    packedTile16384 178972928 179005696 12 1732 13378 27 _ _ (1900273 / 100000) (475069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179005696 :
    ThetaLowerSegment 179005696 179038464 (8949730161533 / 50000) (8951391015867 / 50000) := by
  exact
    packedTile16384 179005696 179038464 12 1748 13379 27 _ _ (1900291 / 100000) (950147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179038464 :
    ThetaLowerSegment 179038464 179071232 (8951391015867 / 50000) (4476511216001 / 25000) := by
  exact
    packedTile16384 179038464 179071232 12 1717 13380 27 _ _ (190031 / 10000) (1900313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179071232 :
    ThetaLowerSegment 179071232 179104000 (4476511216001 / 25000) (4477326456713 / 25000) := by
  exact
    packedTile16384 179071232 179104000 12 1716 13381 27 _ _ (237541 / 12500) (1900331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179104000 :
    ThetaLowerSegment 179104000 179136768 (4477326456713 / 25000) (223908082939 / 1250) := by
  exact
    packedTile16384 179104000 179136768 12 1758 13382 27 _ _ (950173 / 50000) (1900349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179136768 :
    ThetaLowerSegment 179136768 179169536 (223908082939 / 1250) (3583183432657 / 20000) := by
  exact
    packedTile16384 179136768 179169536 12 1721 13384 27 _ _ (380073 / 20000) (118773 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179169536 :
    ThetaLowerSegment 179169536 179202304 (3583183432657 / 20000) (2239895614729 / 12500) := by
  exact
    packedTile16384 179169536 179202304 12 1709 13385 27 _ _ (1900383 / 100000) (950193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179202304 :
    ThetaLowerSegment 179202304 179235072 (2239895614729 / 12500) (17922446910359 / 100000) := by
  exact
    packedTile16384 179202304 179235072 12 1727 13386 27 _ _ (1900401 / 100000) (475101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179235072 :
    ThetaLowerSegment 179235072 179267840 (17922446910359 / 100000) (560179266739 / 3125) := by
  exact
    packedTile16384 179235072 179267840 12 1731 13387 27 _ _ (1900419 / 100000) (950211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179267840 :
    ThetaLowerSegment 179267840 179300608 (560179266739 / 3125) (8964478889029 / 50000) := by
  exact
    packedTile16384 179267840 179300608 12 1695 13389 27 _ _ (950219 / 50000) (1900441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179300608 :
    ThetaLowerSegment 179300608 179333376 (8964478889029 / 50000) (8966137987117 / 50000) := by
  exact
    packedTile16384 179300608 179333376 12 1746 13390 27 _ _ (237557 / 12500) (1900459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179333376 :
    ThetaLowerSegment 179333376 179366144 (8966137987117 / 50000) (4483896174867 / 25000) := by
  exact
    packedTile16384 179333376 179366144 12 1741 13391 27 _ _ (950237 / 50000) (1900477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179366144 :
    ThetaLowerSegment 179366144 179398912 (4483896174867 / 25000) (4484719087903 / 25000) := by
  exact
    packedTile16384 179366144 179398912 12 1732 13392 27 _ _ (475123 / 25000) (380099 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179398912 :
    ThetaLowerSegment 179398912 179431680 (4484719087903 / 25000) (897108021731 / 5000) := by
  exact
    packedTile16384 179398912 179431680 12 1728 13393 27 _ _ (1900511 / 100000) (950257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179431680 :
    ThetaLowerSegment 179431680 179464448 (897108021731 / 5000) (35890858689 / 200) := by
  exact
    packedTile16384 179431680 179464448 12 1720 13395 27 _ _ (1900529 / 100000) (475133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179464448 :
    ThetaLowerSegment 179464448 179497216 (35890858689 / 200) (17948700185887 / 100000) := by
  exact
    packedTile16384 179464448 179497216 12 1721 13396 27 _ _ (1900547 / 100000) (38011 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179497216 :
    ThetaLowerSegment 179497216 179529984 (17948700185887 / 100000) (17951967258841 / 100000) := by
  exact
    packedTile16384 179497216 179529984 12 1719 13397 27 _ _ (950283 / 50000) (1900569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179529984 :
    ThetaLowerSegment 179529984 179562752 (17951967258841 / 100000) (17955211555729 / 100000) := by
  exact
    packedTile16384 179529984 179562752 12 1707 13398 27 _ _ (237573 / 12500) (1900587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179562752 :
    ThetaLowerSegment 179562752 179595520 (17955211555729 / 100000) (17958594627289 / 100000) := by
  exact
    packedTile16384 179562752 179595520 12 1780 13400 27 _ _ (950301 / 50000) (380121 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179595520 :
    ThetaLowerSegment 179595520 179628288 (17958594627289 / 100000) (17961875097409 / 100000) := by
  exact
    packedTile16384 179595520 179628288 12 1726 13401 27 _ _ (95031 / 5000) (1900623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179628288 :
    ThetaLowerSegment 179628288 179661056 (17961875097409 / 100000) (17965102382431 / 100000) := by
  exact
    packedTile16384 179628288 179661056 12 1698 13402 27 _ _ (1900639 / 100000) (950321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179661056 :
    ThetaLowerSegment 179661056 179693824 (17965102382431 / 100000) (17968443737437 / 100000) := by
  exact
    packedTile16384 179661056 179693824 12 1758 13403 27 _ _ (1900657 / 100000) (95033 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179693824 :
    ThetaLowerSegment 179693824 179726592 (17968443737437 / 100000) (8985874505631 / 50000) := by
  exact
    packedTile16384 179693824 179726592 12 1739 13404 27 _ _ (76027 / 4000) (950339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179726592 :
    ThetaLowerSegment 179726592 179759360 (8985874505631 / 50000) (179751056351 / 1000) := by
  exact
    packedTile16384 179726592 179759360 12 1766 13406 27 _ _ (1900693 / 100000) (237587 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179759360 :
    ThetaLowerSegment 179759360 179792128 (179751056351 / 1000) (8989193131143 / 50000) := by
  exact
    packedTile16384 179759360 179792128 12 1726 13407 27 _ _ (1900711 / 100000) (950357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179792128 :
    ThetaLowerSegment 179792128 179824896 (8989193131143 / 50000) (4495436213049 / 25000) := by
  exact
    packedTile16384 179792128 179824896 12 1767 13408 27 _ _ (190073 / 10000) (1900733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179824896 :
    ThetaLowerSegment 179824896 179857664 (4495436213049 / 25000) (562031513641 / 3125) := by
  exact
    packedTile16384 179824896 179857664 12 1717 13409 27 _ _ (475187 / 25000) (1900751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179857664 :
    ThetaLowerSegment 179857664 179890432 (562031513641 / 3125) (2248537570403 / 12500) := by
  exact
    packedTile16384 179857664 179890432 12 1732 13411 27 _ _ (950383 / 50000) (1900769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179890432 :
    ThetaLowerSegment 179890432 179923200 (2248537570403 / 12500) (2248946238963 / 12500) := by
  exact
    packedTile16384 179890432 179923200 12 1720 13412 27 _ _ (118799 / 6250) (1900787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179923200 :
    ThetaLowerSegment 179923200 179955968 (2248946238963 / 12500) (8997379729569 / 50000) := by
  exact
    packedTile16384 179923200 179955968 12 1678 13413 27 _ _ (1900803 / 100000) (950403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179955968 :
    ThetaLowerSegment 179955968 179988736 (8997379729569 / 50000) (8999048650407 / 50000) := by
  exact
    packedTile16384 179955968 179988736 12 1756 13414 27 _ _ (1900821 / 100000) (237603 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell179988736 :
    ThetaLowerSegment 179988736 180021504 (8999048650407 / 50000) (9000664363557 / 50000) := by
  exact
    packedTile16384 179988736 180021504 12 1700 13415 27 _ _ (1900839 / 100000) (950421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180021504 :
    ThetaLowerSegment 180021504 180054272 (9000664363557 / 50000) (9002276290293 / 50000) := by
  exact
    packedTile16384 180021504 180054272 12 1696 13417 27 _ _ (1900857 / 100000) (95043 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180054272 :
    ThetaLowerSegment 180054272 180087040 (9002276290293 / 50000) (18007900021461 / 100000) := by
  exact
    packedTile16384 180054272 180087040 12 1761 13418 27 _ _ (15207 / 800) (950439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180087040 :
    ThetaLowerSegment 180087040 180119808 (18007900021461 / 100000) (18011211378809 / 100000) := by
  exact
    packedTile16384 180087040 180119808 12 1742 13419 27 _ _ (950447 / 50000) (1900897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180119808 :
    ThetaLowerSegment 180119808 180152576 (18011211378809 / 100000) (18014454334681 / 100000) := by
  exact
    packedTile16384 180119808 180152576 12 1706 13420 27 _ _ (118807 / 6250) (380183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180152576 :
    ThetaLowerSegment 180152576 180185344 (18014454334681 / 100000) (18017720132421 / 100000) := by
  exact
    packedTile16384 180152576 180185344 12 1718 13422 27 _ _ (190093 / 10000) (1900933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180185344 :
    ThetaLowerSegment 180185344 180218112 (18017720132421 / 100000) (18021035385733 / 100000) := by
  exact
    packedTile16384 180185344 180218112 12 1744 13423 27 _ _ (475237 / 25000) (1900951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180218112 :
    ThetaLowerSegment 180218112 180250880 (18021035385733 / 100000) (18024236612477 / 100000) := by
  exact
    packedTile16384 180218112 180250880 12 1684 13424 27 _ _ (950483 / 50000) (1900969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180250880 :
    ThetaLowerSegment 180250880 180283648 (18024236612477 / 100000) (9013754103831 / 50000) := by
  exact
    packedTile16384 180250880 180283648 12 1721 13425 27 _ _ (380197 / 20000) (475247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180283648 :
    ThetaLowerSegment 180283648 180316416 (9013754103831 / 50000) (4507684027689 / 25000) := by
  exact
    packedTile16384 180283648 180316416 12 1698 13426 27 _ _ (1901003 / 100000) (950503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180316416 :
    ThetaLowerSegment 180316416 180349184 (4507684027689 / 25000) (18034064798527 / 100000) := by
  exact
    packedTile16384 180316416 180349184 12 1751 13428 27 _ _ (1901021 / 100000) (59407 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180349184 :
    ThetaLowerSegment 180349184 180381952 (18034064798527 / 100000) (18037311773139 / 100000) := by
  exact
    packedTile16384 180349184 180381952 12 1708 13429 27 _ _ (1901039 / 100000) (950521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180381952 :
    ThetaLowerSegment 180381952 180414720 (18037311773139 / 100000) (18040554976381 / 100000) := by
  exact
    packedTile16384 180381952 180414720 12 1706 13430 27 _ _ (1901057 / 100000) (95053 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180414720 :
    ThetaLowerSegment 180414720 180447488 (18040554976381 / 100000) (18043836231831 / 100000) := by
  exact
    packedTile16384 180414720 180447488 12 1726 13431 27 _ _ (76043 / 4000) (950539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180447488 :
    ThetaLowerSegment 180447488 180480256 (18043836231831 / 100000) (18047062388349 / 100000) := by
  exact
    packedTile16384 180447488 180480256 12 1697 13433 27 _ _ (950547 / 50000) (1901097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180480256 :
    ThetaLowerSegment 180480256 180513024 (18047062388349 / 100000) (18050330399877 / 100000) := by
  exact
    packedTile16384 180480256 180513024 12 1719 13434 27 _ _ (237639 / 12500) (380223 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180513024 :
    ThetaLowerSegment 180513024 180545792 (18050330399877 / 100000) (18053621255907 / 100000) := by
  exact
    packedTile16384 180513024 180545792 12 1731 13435 27 _ _ (190113 / 10000) (1901133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180545792 :
    ThetaLowerSegment 180545792 180578560 (18053621255907 / 100000) (18056904538503 / 100000) := by
  exact
    packedTile16384 180545792 180578560 12 1727 13436 27 _ _ (475287 / 25000) (1901151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180578560 :
    ThetaLowerSegment 180578560 180611328 (18056904538503 / 100000) (18060165038193 / 100000) := by
  exact
    packedTile16384 180578560 180611328 12 1715 13437 27 _ _ (950583 / 50000) (1901169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180611328 :
    ThetaLowerSegment 180611328 180644096 (18060165038193 / 100000) (18063400853361 / 100000) := by
  exact
    packedTile16384 180611328 180644096 12 1702 13439 27 _ _ (59412 / 3125) (1901187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180644096 :
    ThetaLowerSegment 180644096 180676864 (18063400853361 / 100000) (18066581564307 / 100000) := by
  exact
    packedTile16384 180644096 180676864 12 1673 13440 27 _ _ (950601 / 50000) (380241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180676864 :
    ThetaLowerSegment 180676864 180709632 (18066581564307 / 100000) (1129365847853 / 6250) := by
  exact
    packedTile16384 180676864 180709632 12 1721 13441 27 _ _ (1901221 / 100000) (237653 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180709632 :
    ThetaLowerSegment 180709632 180742400 (1129365847853 / 6250) (72292479577 / 400) := by
  exact
    packedTile16384 180709632 180742400 12 1718 13442 27 _ _ (1901239 / 100000) (950621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180742400 :
    ThetaLowerSegment 180742400 180775168 (72292479577 / 400) (18076433785201 / 100000) := by
  exact
    packedTile16384 180742400 180775168 12 1743 13444 27 _ _ (1901257 / 100000) (95063 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180775168 :
    ThetaLowerSegment 180775168 180807936 (18076433785201 / 100000) (18079738201151 / 100000) := by
  exact
    packedTile16384 180775168 180807936 12 1738 13445 27 _ _ (76051 / 4000) (950639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180807936 :
    ThetaLowerSegment 180807936 180840704 (18079738201151 / 100000) (18082993214767 / 100000) := by
  exact
    packedTile16384 180807936 180840704 12 1712 13446 27 _ _ (1901293 / 100000) (118831 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180840704 :
    ThetaLowerSegment 180840704 180873472 (18082993214767 / 100000) (9043117475011 / 50000) := by
  exact
    packedTile16384 180840704 180873472 12 1705 13447 27 _ _ (1901311 / 100000) (950657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180873472 :
    ThetaLowerSegment 180873472 180906240 (9043117475011 / 50000) (4522390568943 / 25000) := by
  exact
    packedTile16384 180873472 180906240 12 1750 13448 27 _ _ (1901329 / 100000) (475333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180906240 :
    ThetaLowerSegment 180906240 180939008 (4522390568943 / 25000) (18092788861631 / 100000) := by
  exact
    packedTile16384 180906240 180939008 12 1697 13450 27 _ _ (1901347 / 100000) (38027 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180939008 :
    ThetaLowerSegment 180939008 180971776 (18092788861631 / 100000) (18096068717981 / 100000) := by
  exact
    packedTile16384 180939008 180971776 12 1725 13451 27 _ _ (950683 / 50000) (1901369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell180971776 :
    ThetaLowerSegment 180971776 181004544 (18096068717981 / 100000) (18099266845869 / 100000) := by
  exact
    packedTile16384 180971776 181004544 12 1682 13452 27 _ _ (237673 / 12500) (1901387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181004544 :
    ThetaLowerSegment 181004544 181037312 (18099266845869 / 100000) (18102565778339 / 100000) := by
  exact
    packedTile16384 181004544 181037312 12 1735 13453 27 _ _ (950701 / 50000) (380281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181037312 :
    ThetaLowerSegment 181037312 181070080 (18102565778339 / 100000) (18105857136359 / 100000) := by
  exact
    packedTile16384 181037312 181070080 12 1731 13455 27 _ _ (95071 / 5000) (1901423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181070080 :
    ThetaLowerSegment 181070080 181102848 (18105857136359 / 100000) (18109133314033 / 100000) := by
  exact
    packedTile16384 181070080 181102848 12 1723 13456 27 _ _ (950719 / 50000) (1901441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181102848 :
    ThetaLowerSegment 181102848 181135616 (18109133314033 / 100000) (18112386705249 / 100000) := by
  exact
    packedTile16384 181102848 181135616 12 1711 13457 27 _ _ (118841 / 6250) (1901459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181135616 :
    ThetaLowerSegment 181135616 181168384 (18112386705249 / 100000) (18115695270009 / 100000) := by
  exact
    packedTile16384 181135616 181168384 12 1740 13458 27 _ _ (950737 / 50000) (1901477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181168384 :
    ThetaLowerSegment 181168384 181201152 (18115695270009 / 100000) (18118929707901 / 100000) := by
  exact
    packedTile16384 181168384 181201152 12 1701 13459 27 _ _ (475373 / 25000) (380299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181201152 :
    ThetaLowerSegment 181201152 181233920 (18118929707901 / 100000) (18122190797551 / 100000) := by
  exact
    packedTile16384 181201152 181233920 12 1715 13461 27 _ _ (190151 / 10000) (1901513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181233920 :
    ThetaLowerSegment 181233920 181266688 (18122190797551 / 100000) (18125446213487 / 100000) := by
  exact
    packedTile16384 181233920 181266688 12 1712 13462 27 _ _ (237691 / 12500) (1901531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181266688 :
    ThetaLowerSegment 181266688 181299456 (18125446213487 / 100000) (18128749198889 / 100000) := by
  exact
    packedTile16384 181266688 181299456 12 1737 13463 27 _ _ (950773 / 50000) (1901549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181299456 :
    ThetaLowerSegment 181299456 181332224 (18128749198889 / 100000) (18132035103209 / 100000) := by
  exact
    packedTile16384 181299456 181332224 12 1728 13464 27 _ _ (380313 / 20000) (59424 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181332224 :
    ThetaLowerSegment 181332224 181364992 (18132035103209 / 100000) (18135263991143 / 100000) := by
  exact
    packedTile16384 181332224 181364992 12 1698 13465 27 _ _ (1901583 / 100000) (950793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181364992 :
    ThetaLowerSegment 181364992 181397760 (18135263991143 / 100000) (18138553760873 / 100000) := by
  exact
    packedTile16384 181364992 181397760 12 1730 13467 27 _ _ (1901601 / 100000) (475401 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181397760 :
    ThetaLowerSegment 181397760 181430528 (18138553760873 / 100000) (362835083713 / 2000) := by
  exact
    packedTile16384 181397760 181430528 12 1683 13468 27 _ _ (1901619 / 100000) (950811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181430528 :
    ThetaLowerSegment 181430528 181463296 (362835083713 / 2000) (9072542926837 / 50000) := by
  exact
    packedTile16384 181430528 181463296 12 1752 13469 27 _ _ (1901637 / 100000) (47541 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181463296 :
    ThetaLowerSegment 181463296 181496064 (9072542926837 / 50000) (18148309158899 / 100000) := by
  exact
    packedTile16384 181463296 181496064 12 1695 13470 27 _ _ (380331 / 20000) (950829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181496064 :
    ThetaLowerSegment 181496064 181528832 (18148309158899 / 100000) (2268948693103 / 12500) := by
  exact
    packedTile16384 181496064 181528832 12 1725 13472 27 _ _ (1901673 / 100000) (475419 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181528832 :
    ThetaLowerSegment 181528832 181561600 (2268948693103 / 12500) (1815483382967 / 10000) := by
  exact
    packedTile16384 181528832 181561600 12 1706 13473 27 _ _ (1901691 / 100000) (950847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181561600 :
    ThetaLowerSegment 181561600 181594368 (1815483382967 / 10000) (18157996371737 / 100000) := by
  exact
    packedTile16384 181561600 181594368 12 1663 13474 27 _ _ (1901709 / 100000) (118857 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181594368 :
    ThetaLowerSegment 181594368 181627136 (18157996371737 / 100000) (4540315409249 / 25000) := by
  exact
    packedTile16384 181594368 181627136 12 1717 13475 27 _ _ (1901727 / 100000) (190173 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181627136 :
    ThetaLowerSegment 181627136 181659904 (4540315409249 / 25000) (4541140766579 / 25000) := by
  exact
    packedTile16384 181627136 181659904 12 1736 13476 27 _ _ (380349 / 20000) (475437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181659904 :
    ThetaLowerSegment 181659904 181692672 (4541140766579 / 25000) (18167923481537 / 100000) := by
  exact
    packedTile16384 181659904 181692672 12 1767 13478 27 _ _ (1901763 / 100000) (950883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181692672 :
    ThetaLowerSegment 181692672 181725440 (18167923481537 / 100000) (9085651473187 / 50000) := by
  exact
    packedTile16384 181692672 181725440 12 1777 13479 27 _ _ (1901781 / 100000) (237723 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181725440 :
    ThetaLowerSegment 181725440 181758208 (9085651473187 / 50000) (3634914427771 / 20000) := by
  exact
    packedTile16384 181725440 181758208 12 1719 13480 27 _ _ (1901799 / 100000) (950901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181758208 :
    ThetaLowerSegment 181758208 181790976 (3634914427771 / 20000) (568056235072 / 3125) := by
  exact
    packedTile16384 181758208 181790976 12 1697 13481 27 _ _ (1901817 / 100000) (95091 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181790976 :
    ThetaLowerSegment 181790976 181823744 (568056235072 / 3125) (18181106813369 / 100000) := by
  exact
    packedTile16384 181790976 181823744 12 1739 13482 27 _ _ (380367 / 20000) (950919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181823744 :
    ThetaLowerSegment 181823744 181856512 (18181106813369 / 100000) (1818441033203 / 10000) := by
  exact
    packedTile16384 181823744 181856512 12 1737 13484 27 _ _ (1901853 / 100000) (59433 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181856512 :
    ThetaLowerSegment 181856512 181889280 (1818441033203 / 10000) (2273452110817 / 12500) := by
  exact
    packedTile16384 181856512 181889280 12 1686 13485 27 _ _ (1901871 / 100000) (950937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181889280 :
    ThetaLowerSegment 181889280 181922048 (2273452110817 / 12500) (4547708720681 / 25000) := by
  exact
    packedTile16384 181889280 181922048 12 1692 13486 27 _ _ (1901889 / 100000) (475473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181922048 :
    ThetaLowerSegment 181922048 181954816 (4547708720681 / 25000) (2274264221299 / 12500) := by
  exact
    packedTile16384 181922048 181954816 12 1724 13487 27 _ _ (1901907 / 100000) (190191 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181954816 :
    ThetaLowerSegment 181954816 181987584 (2274264221299 / 12500) (4549351976123 / 25000) := by
  exact
    packedTile16384 181954816 181987584 12 1732 13489 27 _ _ (76077 / 4000) (237741 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell181987584 :
    ThetaLowerSegment 181987584 182020352 (4549351976123 / 25000) (18200650717307 / 100000) := by
  exact
    packedTile16384 181987584 182020352 12 1705 13490 27 _ _ (1901943 / 100000) (950973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182020352 :
    ThetaLowerSegment 182020352 182053120 (18200650717307 / 100000) (910199242747 / 5000) := by
  exact
    packedTile16384 182020352 182053120 12 1753 13491 27 _ _ (1901961 / 100000) (475491 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182053120 :
    ThetaLowerSegment 182053120 182085888 (910199242747 / 5000) (455180455481 / 2500) := by
  exact
    packedTile16384 182053120 182085888 12 1700 13492 27 _ _ (1901979 / 100000) (950991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182085888 :
    ThetaLowerSegment 182085888 182118656 (455180455481 / 2500) (9105220101079 / 50000) := by
  exact
    packedTile16384 182085888 182118656 12 1694 13493 27 _ _ (1901997 / 100000) (951 / 50)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182118656 :
    ThetaLowerSegment 182118656 182151424 (9105220101079 / 50000) (9106840617859 / 50000) := by
  exact
    packedTile16384 182118656 182151424 12 1704 13495 27 _ _ (380403 / 20000) (951009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182151424 :
    ThetaLowerSegment 182151424 182184192 (9106840617859 / 50000) (728678794031 / 4000) := by
  exact
    packedTile16384 182151424 182184192 12 1729 13496 27 _ _ (1902033 / 100000) (475509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182184192 :
    ThetaLowerSegment 182184192 182216960 (728678794031 / 4000) (9110110227967 / 50000) := by
  exact
    packedTile16384 182184192 182216960 12 1709 13497 27 _ _ (1902051 / 100000) (951027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182216960 :
    ThetaLowerSegment 182216960 182249728 (9110110227967 / 50000) (4555875856757 / 25000) := by
  exact
    packedTile16384 182216960 182249728 12 1726 13498 27 _ _ (1902069 / 100000) (237759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182249728 :
    ThetaLowerSegment 182249728 182282496 (4555875856757 / 25000) (18226788331277 / 100000) := by
  exact
    packedTile16384 182249728 182282496 12 1727 13499 27 _ _ (1902087 / 100000) (190209 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182282496 :
    ThetaLowerSegment 182282496 182315264 (18226788331277 / 100000) (18230067560297 / 100000) := by
  exact
    packedTile16384 182282496 182315264 12 1724 13501 27 _ _ (380421 / 20000) (475527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182315264 :
    ThetaLowerSegment 182315264 182348032 (18230067560297 / 100000) (18233403884039 / 100000) := by
  exact
    packedTile16384 182315264 182348032 12 1754 13502 27 _ _ (1902123 / 100000) (951063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182348032 :
    ThetaLowerSegment 182348032 182380800 (18233403884039 / 100000) (1139789013047 / 6250) := by
  exact
    packedTile16384 182348032 182380800 12 1693 13503 27 _ _ (1902141 / 100000) (59442 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182380800 :
    ThetaLowerSegment 182380800 182413568 (1139789013047 / 6250) (1139990641901 / 6250) := by
  exact
    packedTile16384 182380800 182413568 12 1696 13504 27 _ _ (1902159 / 100000) (951081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182413568 :
    ThetaLowerSegment 182413568 182446336 (1139990641901 / 6250) (18243063047369 / 100000) := by
  exact
    packedTile16384 182413568 182446336 12 1689 13506 27 _ _ (1902177 / 100000) (95109 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182446336 :
    ThetaLowerSegment 182446336 182479104 (18243063047369 / 100000) (18246361453499 / 100000) := by
  exact
    packedTile16384 182446336 182479104 12 1734 13507 27 _ _ (380439 / 20000) (951099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182479104 :
    ThetaLowerSegment 182479104 182511872 (18246361453499 / 100000) (18249648477563 / 100000) := by
  exact
    packedTile16384 182479104 182511872 12 1728 13508 27 _ _ (1902213 / 100000) (237777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182511872 :
    ThetaLowerSegment 182511872 182544640 (18249648477563 / 100000) (18252874661339 / 100000) := by
  exact
    packedTile16384 182511872 182544640 12 1696 13509 27 _ _ (1902231 / 100000) (951117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182544640 :
    ThetaLowerSegment 182544640 182577408 (18252874661339 / 100000) (456405042371 / 2500) := by
  exact
    packedTile16384 182544640 182577408 12 1749 13510 27 _ _ (1902249 / 100000) (475563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182577408 :
    ThetaLowerSegment 182577408 182610176 (456405042371 / 2500) (18259414623803 / 100000) := by
  exact
    packedTile16384 182577408 182610176 12 1689 13512 27 _ _ (1902267 / 100000) (190227 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182610176 :
    ThetaLowerSegment 182610176 182642944 (18259414623803 / 100000) (18262774059113 / 100000) := by
  exact
    packedTile16384 182610176 182642944 12 1766 13513 27 _ _ (380457 / 20000) (118893 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182642944 :
    ThetaLowerSegment 182642944 182675712 (18262774059113 / 100000) (18266004169607 / 100000) := by
  exact
    packedTile16384 182642944 182675712 12 1698 13514 27 _ _ (1902303 / 100000) (951153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182675712 :
    ThetaLowerSegment 182675712 182708480 (18266004169607 / 100000) (18269207678171 / 100000) := by
  exact
    packedTile16384 182675712 182708480 12 1684 13515 27 _ _ (1902321 / 100000) (475581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182708480 :
    ThetaLowerSegment 182708480 182741248 (18269207678171 / 100000) (18272449263827 / 100000) := by
  exact
    packedTile16384 182708480 182741248 12 1704 13516 27 _ _ (1902339 / 100000) (951171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182741248 :
    ThetaLowerSegment 182741248 182774016 (18272449263827 / 100000) (18275675661299 / 100000) := by
  exact
    packedTile16384 182741248 182774016 12 1696 13518 27 _ _ (1902357 / 100000) (47559 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182774016 :
    ThetaLowerSegment 182774016 182806784 (18275675661299 / 100000) (571216344232 / 3125) := by
  exact
    packedTile16384 182774016 182806784 12 1707 13519 27 _ _ (15219 / 800) (951189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182806784 :
    ThetaLowerSegment 182806784 182839552 (571216344232 / 3125) (18282185619419 / 100000) := by
  exact
    packedTile16384 182806784 182839552 12 1715 13520 27 _ _ (1902393 / 100000) (475599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182839552 :
    ThetaLowerSegment 182839552 182872320 (18282185619419 / 100000) (18285396887499 / 100000) := by
  exact
    packedTile16384 182839552 182872320 12 1688 13521 27 _ _ (190241 / 10000) (1902413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182872320 :
    ThetaLowerSegment 182872320 182905088 (18285396887499 / 100000) (18288665258803 / 100000) := by
  exact
    packedTile16384 182872320 182905088 12 1718 13523 27 _ _ (475607 / 25000) (1902431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182905088 :
    ThetaLowerSegment 182905088 182937856 (18288665258803 / 100000) (18292047807791 / 100000) := by
  exact
    packedTile16384 182905088 182937856 12 1778 13524 27 _ _ (951223 / 50000) (1902449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182937856 :
    ThetaLowerSegment 182937856 182970624 (18292047807791 / 100000) (18295266776879 / 100000) := by
  exact
    packedTile16384 182937856 182970624 12 1692 13525 27 _ _ (59452 / 3125) (1902467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell182970624 :
    ThetaLowerSegment 182970624 183003392 (18295266776879 / 100000) (18298520021099 / 100000) := by
  exact
    packedTile16384 182970624 183003392 12 1710 13526 27 _ _ (951241 / 50000) (380497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183003392 :
    ThetaLowerSegment 183003392 183036160 (18298520021099 / 100000) (18301788516099 / 100000) := by
  exact
    packedTile16384 183003392 183036160 12 1718 13527 27 _ _ (761 / 40) (1902503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183036160 :
    ThetaLowerSegment 183036160 183068928 (18301788516099 / 100000) (18305062749577 / 100000) := by
  exact
    packedTile16384 183036160 183068928 12 1721 13529 27 _ _ (951259 / 50000) (1902521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183068928 :
    ThetaLowerSegment 183068928 183101696 (18305062749577 / 100000) (18308371259681 / 100000) := by
  exact
    packedTile16384 183068928 183101696 12 1739 13530 27 _ _ (237817 / 12500) (1902539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183101696 :
    ThetaLowerSegment 183101696 183134464 (18308371259681 / 100000) (18311641750007 / 100000) := by
  exact
    packedTile16384 183101696 183134464 12 1719 13531 27 _ _ (951277 / 50000) (1902557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183134464 :
    ThetaLowerSegment 183134464 183167232 (18311641750007 / 100000) (18314895148127 / 100000) := by
  exact
    packedTile16384 183134464 183167232 12 1710 13532 27 _ _ (475643 / 25000) (76103 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183167232 :
    ThetaLowerSegment 183167232 183200000 (18314895148127 / 100000) (18318272245377 / 100000) := by
  exact
    packedTile16384 183167232 183200000 12 1775 13533 27 _ _ (190259 / 10000) (1902593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183200000 :
    ThetaLowerSegment 183200000 183232768 (18318272245377 / 100000) (18321415352141 / 100000) := by
  exact
    packedTile16384 183200000 183232768 12 1652 13535 27 _ _ (1902607 / 100000) (190261 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183232768 :
    ThetaLowerSegment 183232768 183265536 (18321415352141 / 100000) (18324676451391 / 100000) := by
  exact
    packedTile16384 183232768 183265536 12 1714 13536 27 _ _ (15221 / 800) (475657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183265536 :
    ThetaLowerSegment 183265536 183298304 (18324676451391 / 100000) (3665592843699 / 20000) := by
  exact
    packedTile16384 183265536 183298304 12 1728 13537 27 _ _ (1902643 / 100000) (951323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183298304 :
    ThetaLowerSegment 183298304 183331072 (3665592843699 / 20000) (2291407691251 / 12500) := by
  exact
    packedTile16384 183298304 183331072 12 1733 13538 27 _ _ (1902661 / 100000) (237833 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183331072 :
    ThetaLowerSegment 183331072 183363840 (2291407691251 / 12500) (18334509403061 / 100000) := by
  exact
    packedTile16384 183331072 183363840 12 1707 13539 27 _ _ (1902679 / 100000) (951341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183363840 :
    ThetaLowerSegment 183363840 183396608 (18334509403061 / 100000) (4584452645589 / 25000) := by
  exact
    packedTile16384 183363840 183396608 12 1735 13541 27 _ _ (1902697 / 100000) (19027 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183396608 :
    ThetaLowerSegment 183396608 183429376 (4584452645589 / 25000) (4585286034759 / 25000) := by
  exact
    packedTile16384 183396608 183429376 12 1752 13542 27 _ _ (380543 / 20000) (951359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183429376 :
    ThetaLowerSegment 183429376 183462144 (4585286034759 / 25000) (733773857547 / 4000) := by
  exact
    packedTile16384 183429376 183462144 12 1683 13543 27 _ _ (1902733 / 100000) (118921 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183462144 :
    ThetaLowerSegment 183462144 183494912 (733773857547 / 4000) (733907811147 / 4000) := by
  exact
    packedTile16384 183462144 183494912 12 1760 13544 27 _ _ (7611 / 400) (1902753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183494912 :
    ThetaLowerSegment 183494912 183527680 (733907811147 / 4000) (3670203121767 / 20000) := by
  exact
    packedTile16384 183494912 183527680 12 1745 13546 27 _ _ (118923 / 6250) (1902771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183527680 :
    ThetaLowerSegment 183527680 183560448 (3670203121767 / 20000) (18354318845331 / 100000) := by
  exact
    packedTile16384 183527680 183560448 12 1736 13547 27 _ _ (951393 / 50000) (1902789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183560448 :
    ThetaLowerSegment 183560448 183593216 (18354318845331 / 100000) (18357646849527 / 100000) := by
  exact
    packedTile16384 183560448 183593216 12 1749 13548 27 _ _ (475701 / 25000) (1902807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183593216 :
    ThetaLowerSegment 183593216 183625984 (18357646849527 / 100000) (3672183560109 / 20000) := by
  exact
    packedTile16384 183593216 183625984 12 1719 13549 27 _ _ (951411 / 50000) (76113 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183625984 :
    ThetaLowerSegment 183625984 183658752 (3672183560109 / 20000) (3672843465021 / 20000) := by
  exact
    packedTile16384 183625984 183658752 12 1734 13550 27 _ _ (47571 / 2500) (1902843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183658752 :
    ThetaLowerSegment 183658752 183691520 (3672843465021 / 20000) (18367551130569 / 100000) := by
  exact
    packedTile16384 183658752 183691520 12 1752 13552 27 _ _ (1902857 / 100000) (95143 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183691520 :
    ThetaLowerSegment 183691520 183724288 (18367551130569 / 100000) (4592710300361 / 25000) := by
  exact
    packedTile16384 183691520 183724288 12 1729 13553 27 _ _ (15223 / 800) (951439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183724288 :
    ThetaLowerSegment 183724288 183757056 (4592710300361 / 25000) (18374142720799 / 100000) := by
  exact
    packedTile16384 183724288 183757056 12 1735 13554 27 _ _ (1902893 / 100000) (118931 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183757056 :
    ThetaLowerSegment 183757056 183789824 (18374142720799 / 100000) (1837737957241 / 10000) := by
  exact
    packedTile16384 183757056 183789824 12 1701 13555 27 _ _ (1902911 / 100000) (951457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183789824 :
    ThetaLowerSegment 183789824 183822592 (1837737957241 / 10000) (9190303469997 / 50000) := by
  exact
    packedTile16384 183789824 183822592 12 1696 13556 27 _ _ (1902929 / 100000) (475733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183822592 :
    ThetaLowerSegment 183822592 183855360 (9190303469997 / 50000) (3676773337641 / 20000) := by
  exact
    packedTile16384 183822592 183855360 12 1713 13558 27 _ _ (1902947 / 100000) (38059 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183855360 :
    ThetaLowerSegment 183855360 183888128 (3676773337641 / 20000) (3677426054293 / 20000) := by
  exact
    packedTile16384 183855360 183888128 12 1715 13559 27 _ _ (475741 / 25000) (1902967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183888128 :
    ThetaLowerSegment 183888128 183920896 (3677426054293 / 20000) (18390350117009 / 100000) := by
  exact
    packedTile16384 183888128 183920896 12 1692 13560 27 _ _ (951491 / 50000) (380597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183920896 :
    ThetaLowerSegment 183920896 183953664 (18390350117009 / 100000) (18393661337009 / 100000) := by
  exact
    packedTile16384 183920896 183953664 12 1740 13561 27 _ _ (1903 / 100) (1903003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183953664 :
    ThetaLowerSegment 183953664 183986432 (18393661337009 / 100000) (18396974491347 / 100000) := by
  exact
    packedTile16384 183953664 183986432 12 1741 13562 27 _ _ (951509 / 50000) (1903021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell183986432 :
    ThetaLowerSegment 183986432 184019200 (18396974491347 / 100000) (18400276258807 / 100000) := by
  exact
    packedTile16384 183986432 184019200 12 1735 13564 27 _ _ (475759 / 25000) (1903039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184019200 :
    ThetaLowerSegment 184019200 184051968 (18400276258807 / 100000) (18403595184983 / 100000) := by
  exact
    packedTile16384 184019200 184051968 12 1744 13565 27 _ _ (951527 / 50000) (1903057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184051968 :
    ThetaLowerSegment 184051968 184084736 (18403595184983 / 100000) (9203427572803 / 50000) := by
  exact
    packedTile16384 184051968 184084736 12 1713 13566 27 _ _ (1903071 / 100000) (951537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184084736 :
    ThetaLowerSegment 184084736 184117504 (9203427572803 / 50000) (3682018459999 / 20000) := by
  exact
    packedTile16384 184084736 184117504 12 1701 13567 27 _ _ (1903089 / 100000) (475773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184117504 :
    ThetaLowerSegment 184117504 184150272 (3682018459999 / 20000) (18413342806751 / 100000) := by
  exact
    packedTile16384 184117504 184150272 12 1708 13568 27 _ _ (1903107 / 100000) (190311 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184150272 :
    ThetaLowerSegment 184150272 184183040 (18413342806751 / 100000) (18416639019251 / 100000) := by
  exact
    packedTile16384 184150272 184183040 12 1732 13570 27 _ _ (609 / 32) (237891 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184183040 :
    ThetaLowerSegment 184183040 184215808 (18416639019251 / 100000) (18419893393781 / 100000) := by
  exact
    packedTile16384 184183040 184215808 12 1710 13571 27 _ _ (1903143 / 100000) (951573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184215808 :
    ThetaLowerSegment 184215808 184248576 (18419893393781 / 100000) (18423214407981 / 100000) := by
  exact
    packedTile16384 184215808 184248576 12 1745 13572 27 _ _ (47579 / 2500) (1903163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184248576 :
    ThetaLowerSegment 184248576 184281344 (18423214407981 / 100000) (3685312038981 / 20000) := by
  exact
    packedTile16384 184248576 184281344 12 1758 13573 27 _ _ (951589 / 50000) (1903181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184281344 :
    ThetaLowerSegment 184281344 184314112 (3685312038981 / 20000) (18429841304809 / 100000) := by
  exact
    packedTile16384 184281344 184314112 12 1724 13575 27 _ _ (475799 / 25000) (1903199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184314112 :
    ThetaLowerSegment 184314112 184346880 (18429841304809 / 100000) (18433038704329 / 100000) := by
  exact
    packedTile16384 184314112 184346880 12 1680 13576 27 _ _ (951607 / 50000) (1903217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184346880 :
    ThetaLowerSegment 184346880 184379648 (18433038704329 / 100000) (9218197050291 / 50000) := by
  exact
    packedTile16384 184346880 184379648 12 1763 13577 27 _ _ (1903231 / 100000) (951617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184379648 :
    ThetaLowerSegment 184379648 184412416 (9218197050291 / 50000) (2304964646667 / 12500) := by
  exact
    packedTile16384 184379648 184412416 12 1746 13578 27 _ _ (1903249 / 100000) (475813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184412416 :
    ThetaLowerSegment 184412416 184445184 (2304964646667 / 12500) (18443038374251 / 100000) := by
  exact
    packedTile16384 184412416 184445184 12 1745 13579 27 _ _ (1903267 / 100000) (190327 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184445184 :
    ThetaLowerSegment 184445184 184477952 (18443038374251 / 100000) (18446319637591 / 100000) := by
  exact
    packedTile16384 184445184 184477952 12 1724 13581 27 _ _ (380657 / 20000) (237911 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184477952 :
    ThetaLowerSegment 184477952 184510720 (18446319637591 / 100000) (737984341807 / 4000) := by
  exact
    packedTile16384 184477952 184510720 12 1728 13582 27 _ _ (1903303 / 100000) (951653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184510720 :
    ThetaLowerSegment 184510720 184543488 (737984341807 / 4000) (738115670887 / 4000) := by
  exact
    packedTile16384 184510720 184543488 12 1725 13583 27 _ _ (47583 / 2500) (1903323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184543488 :
    ThetaLowerSegment 184543488 184576256 (738115670887 / 4000) (147650161577 / 800) := by
  exact
    packedTile16384 184543488 184576256 12 1775 13584 27 _ _ (951669 / 50000) (1903341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184576256 :
    ThetaLowerSegment 184576256 184609024 (147650161577 / 800) (18459450705001 / 100000) := by
  exact
    packedTile16384 184576256 184609024 12 1671 13585 27 _ _ (475839 / 25000) (1903359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184609024 :
    ThetaLowerSegment 184609024 184641792 (18459450705001 / 100000) (18462770189257 / 100000) := by
  exact
    packedTile16384 184609024 184641792 12 1744 13587 27 _ _ (951687 / 50000) (1903377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184641792 :
    ThetaLowerSegment 184641792 184674560 (18462770189257 / 100000) (18466101123507 / 100000) := by
  exact
    packedTile16384 184641792 184674560 12 1750 13588 27 _ _ (1903391 / 100000) (951697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184674560 :
    ThetaLowerSegment 184674560 184707328 (18466101123507 / 100000) (18469386407441 / 100000) := by
  exact
    packedTile16384 184674560 184707328 12 1726 13589 27 _ _ (1903409 / 100000) (475853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184707328 :
    ThetaLowerSegment 184707328 184740096 (18469386407441 / 100000) (738908087091 / 4000) := by
  exact
    packedTile16384 184707328 184740096 12 1742 13590 27 _ _ (1903427 / 100000) (190343 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184740096 :
    ThetaLowerSegment 184740096 184772864 (738908087091 / 4000) (923800042373 / 5000) := by
  exact
    packedTile16384 184740096 184772864 12 1733 13591 27 _ _ (380689 / 20000) (237931 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184772864 :
    ThetaLowerSegment 184772864 184805632 (923800042373 / 5000) (9239653580477 / 50000) := by
  exact
    packedTile16384 184772864 184805632 12 1737 13593 27 _ _ (951731 / 50000) (380693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184805632 :
    ThetaLowerSegment 184805632 184838400 (9239653580477 / 50000) (9241269634997 / 50000) := by
  exact
    packedTile16384 184805632 184838400 12 1698 13594 27 _ _ (47587 / 2500) (1903483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184838400 :
    ThetaLowerSegment 184838400 184871168 (9241269634997 / 50000) (4621453797513 / 25000) := by
  exact
    packedTile16384 184838400 184871168 12 1721 13595 27 _ _ (951749 / 50000) (1903501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184871168 :
    ThetaLowerSegment 184871168 184903936 (4621453797513 / 25000) (18489136823727 / 100000) := by
  exact
    packedTile16384 184871168 184903936 12 1745 13596 27 _ _ (380703 / 20000) (951759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184903936 :
    ThetaLowerSegment 184903936 184936704 (18489136823727 / 100000) (4623118429269 / 25000) := by
  exact
    packedTile16384 184903936 184936704 12 1753 13597 27 _ _ (1903533 / 100000) (118971 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184936704 :
    ThetaLowerSegment 184936704 184969472 (4623118429269 / 25000) (3699145377147 / 20000) := by
  exact
    packedTile16384 184936704 184969472 12 1709 13599 27 _ _ (1903551 / 100000) (951777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell184969472 :
    ThetaLowerSegment 184969472 185002240 (3699145377147 / 20000) (9249461489043 / 50000) := by
  exact
    packedTile16384 184969472 185002240 12 1679 13600 27 _ _ (1903569 / 100000) (475893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185002240 :
    ThetaLowerSegment 185002240 185035008 (9249461489043 / 50000) (9251115705277 / 50000) := by
  exact
    packedTile16384 185002240 185035008 12 1738 13601 27 _ _ (951793 / 50000) (1903589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185035008 :
    ThetaLowerSegment 185035008 185067776 (9251115705277 / 50000) (9252706166419 / 50000) := by
  exact
    packedTile16384 185035008 185067776 12 1671 13602 27 _ _ (475901 / 25000) (1903607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185067776 :
    ThetaLowerSegment 185067776 185100544 (9252706166419 / 50000) (9254356606693 / 50000) := by
  exact
    packedTile16384 185067776 185100544 12 1734 13603 27 _ _ (951811 / 50000) (15229 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185100544 :
    ThetaLowerSegment 185100544 185133312 (9254356606693 / 50000) (18512023641607 / 100000) := by
  exact
    packedTile16384 185100544 185133312 12 1739 13605 27 _ _ (1903639 / 100000) (951821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185133312 :
    ThetaLowerSegment 185133312 185166080 (18512023641607 / 100000) (3703083953139 / 20000) := by
  exact
    packedTile16384 185133312 185166080 12 1784 13606 27 _ _ (1903657 / 100000) (95183 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185166080 :
    ThetaLowerSegment 185166080 185198848 (3703083953139 / 20000) (3703741101749 / 20000) := by
  exact
    packedTile16384 185166080 185198848 12 1726 13607 27 _ _ (76147 / 4000) (951839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185198848 :
    ThetaLowerSegment 185198848 185231616 (3703741101749 / 20000) (4630494489253 / 25000) := by
  exact
    packedTile16384 185198848 185231616 12 1719 13608 27 _ _ (1903693 / 100000) (118981 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185231616 :
    ThetaLowerSegment 185231616 185264384 (4630494489253 / 25000) (4631320699393 / 25000) := by
  exact
    packedTile16384 185231616 185264384 12 1736 13609 27 _ _ (190371 / 10000) (1903713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185264384 :
    ThetaLowerSegment 185264384 185297152 (4631320699393 / 25000) (926427955673 / 5000) := by
  exact
    packedTile16384 185264384 185297152 12 1721 13611 27 _ _ (118983 / 6250) (1903731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185297152 :
    ThetaLowerSegment 185297152 185329920 (926427955673 / 5000) (4632946966669 / 25000) := by
  exact
    packedTile16384 185297152 185329920 12 1696 13612 27 _ _ (951873 / 50000) (1903749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185329920 :
    ThetaLowerSegment 185329920 185362688 (4632946966669 / 25000) (463375987347 / 2500) := by
  exact
    packedTile16384 185329920 185362688 12 1708 13613 27 _ _ (1903763 / 100000) (951883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185362688 :
    ThetaLowerSegment 185362688 185395456 (463375987347 / 2500) (9269162709943 / 50000) := by
  exact
    packedTile16384 185362688 185395456 12 1726 13614 27 _ _ (1903781 / 100000) (237973 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185395456 :
    ThetaLowerSegment 185395456 185428224 (9269162709943 / 50000) (18541632318749 / 100000) := by
  exact
    packedTile16384 185395456 185428224 12 1737 13616 27 _ _ (1903799 / 100000) (951901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185428224 :
    ThetaLowerSegment 185428224 185460992 (18541632318749 / 100000) (18544933535693 / 100000) := by
  exact
    packedTile16384 185428224 185460992 12 1734 13617 27 _ _ (237977 / 12500) (1903819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185460992 :
    ThetaLowerSegment 185460992 185493760 (18544933535693 / 100000) (18548190995667 / 100000) := by
  exact
    packedTile16384 185460992 185493760 12 1711 13618 27 _ _ (951917 / 50000) (1903837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185493760 :
    ThetaLowerSegment 185493760 185526528 (18548190995667 / 100000) (3710290839599 / 20000) := by
  exact
    packedTile16384 185493760 185526528 12 1714 13619 27 _ _ (475963 / 25000) (380771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185526528 :
    ThetaLowerSegment 185526528 185559296 (3710290839599 / 20000) (18554740275889 / 100000) := by
  exact
    packedTile16384 185526528 185559296 12 1726 13620 27 _ _ (1903869 / 100000) (59496 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185559296 :
    ThetaLowerSegment 185559296 185592064 (18554740275889 / 100000) (3711602230751 / 20000) := by
  exact
    packedTile16384 185559296 185592064 12 1718 13622 27 _ _ (1903887 / 100000) (190389 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185592064 :
    ThetaLowerSegment 185592064 185624832 (3711602230751 / 20000) (1856123065711 / 10000) := by
  exact
    packedTile16384 185592064 185624832 12 1691 13623 27 _ _ (380781 / 20000) (475977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185624832 :
    ThetaLowerSegment 185624832 185657600 (1856123065711 / 10000) (9282235566177 / 50000) := by
  exact
    packedTile16384 185624832 185657600 12 1702 13624 27 _ _ (951961 / 50000) (76157 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185657600 :
    ThetaLowerSegment 185657600 185690368 (9282235566177 / 50000) (9283873906547 / 50000) := by
  exact
    packedTile16384 185657600 185690368 12 1721 13625 27 _ _ (95197 / 5000) (1903943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185690368 :
    ThetaLowerSegment 185690368 185723136 (9283873906547 / 50000) (1160691650743 / 6250) := by
  exact
    packedTile16384 185690368 185723136 12 1743 13626 27 _ _ (951979 / 50000) (1903961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185723136 :
    ThetaLowerSegment 185723136 185755904 (1160691650743 / 6250) (18574266993863 / 100000) := by
  exact
    packedTile16384 185723136 185755904 12 1681 13628 27 _ _ (76159 / 4000) (951989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185755904 :
    ThetaLowerSegment 185755904 185788672 (18574266993863 / 100000) (18577621829529 / 100000) := by
  exact
    packedTile16384 185755904 185788672 12 1762 13629 27 _ _ (1903993 / 100000) (475999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185788672 :
    ThetaLowerSegment 185788672 185821440 (18577621829529 / 100000) (18580915768559 / 100000) := by
  exact
    packedTile16384 185788672 185821440 12 1730 13630 27 _ _ (1904011 / 100000) (952007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185821440 :
    ThetaLowerSegment 185821440 185854208 (18580915768559 / 100000) (18584177368523 / 100000) := by
  exact
    packedTile16384 185821440 185854208 12 1713 13631 27 _ _ (476007 / 25000) (1904031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185854208 :
    ThetaLowerSegment 185854208 185886976 (18584177368523 / 100000) (18587404726493 / 100000) := by
  exact
    packedTile16384 185854208 185886976 12 1695 13632 27 _ _ (952023 / 50000) (1904049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185886976 :
    ThetaLowerSegment 185886976 185919744 (18587404726493 / 100000) (9295350329773 / 50000) := by
  exact
    packedTile16384 185886976 185919744 12 1731 13634 27 _ _ (1904063 / 100000) (952033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185919744 :
    ThetaLowerSegment 185919744 185952512 (9295350329773 / 50000) (9296999263919 / 50000) := by
  exact
    packedTile16384 185919744 185952512 12 1732 13635 27 _ _ (1904081 / 100000) (476021 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185952512 :
    ThetaLowerSegment 185952512 185985280 (9296999263919 / 50000) (1162335072917 / 6250) := by
  exact
    packedTile16384 185952512 185985280 12 1766 13636 27 _ _ (1904099 / 100000) (952051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell185985280 :
    ThetaLowerSegment 185985280 186018048 (1162335072917 / 6250) (465014858891 / 2500) := by
  exact
    packedTile16384 185985280 186018048 12 1698 13637 27 _ _ (476029 / 25000) (1904119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186018048 :
    ThetaLowerSegment 186018048 186050816 (465014858891 / 2500) (4650954989659 / 25000) := by
  exact
    packedTile16384 186018048 186050816 12 1694 13638 27 _ _ (952067 / 50000) (1904137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186050816 :
    ThetaLowerSegment 186050816 186083584 (4650954989659 / 25000) (930354469381 / 5000) := by
  exact
    packedTile16384 186050816 186083584 12 1717 13640 27 _ _ (238019 / 12500) (380831 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186083584 :
    ThetaLowerSegment 186083584 186116352 (930354469381 / 5000) (18610343612441 / 100000) := by
  exact
    packedTile16384 186083584 186116352 12 1709 13641 27 _ _ (1904169 / 100000) (476043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186116352 :
    ThetaLowerSegment 186116352 186149120 (18610343612441 / 100000) (9306800838199 / 50000) := by
  exact
    packedTile16384 186116352 186149120 12 1711 13642 27 _ _ (1904187 / 100000) (190419 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186149120 :
    ThetaLowerSegment 186149120 186181888 (9306800838199 / 50000) (1861689214091 / 10000) := by
  exact
    packedTile16384 186149120 186181888 12 1728 13643 27 _ _ (476051 / 25000) (1904207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186181888 :
    ThetaLowerSegment 186181888 186214656 (1861689214091 / 10000) (2327521639427 / 12500) := by
  exact
    packedTile16384 186181888 186214656 12 1723 13644 27 _ _ (952111 / 50000) (76169 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186214656 :
    ThetaLowerSegment 186214656 186247424 (2327521639427 / 12500) (2327939382077 / 12500) := by
  exact
    packedTile16384 186214656 186247424 12 1755 13646 27 _ _ (23803 / 1250) (1904243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186247424 :
    ThetaLowerSegment 186247424 186280192 (2327939382077 / 12500) (9313404710613 / 50000) := by
  exact
    packedTile16384 186247424 186280192 12 1730 13647 27 _ _ (1904257 / 100000) (95213 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186280192 :
    ThetaLowerSegment 186280192 186312960 (9313404710613 / 50000) (18629976230551 / 100000) := by
  exact
    packedTile16384 186280192 186312960 12 1663 13648 27 _ _ (76171 / 4000) (952139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186312960 :
    ThetaLowerSegment 186312960 186345728 (18629976230551 / 100000) (3726643467107 / 20000) := by
  exact
    packedTile16384 186312960 186345728 12 1702 13649 27 _ _ (476073 / 25000) (380859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186345728 :
    ThetaLowerSegment 186345728 186378496 (3726643467107 / 20000) (3727311118193 / 20000) := by
  exact
    packedTile16384 186345728 186378496 12 1753 13650 27 _ _ (190431 / 10000) (1904313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186378496 :
    ThetaLowerSegment 186378496 186411264 (3727311118193 / 20000) (18639779618269 / 100000) := by
  exact
    packedTile16384 186378496 186411264 12 1693 13652 27 _ _ (238041 / 12500) (1904331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186411264 :
    ThetaLowerSegment 186411264 186444032 (18639779618269 / 100000) (18643108413329 / 100000) := by
  exact
    packedTile16384 186411264 186444032 12 1748 13653 27 _ _ (380869 / 20000) (476087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186444032 :
    ThetaLowerSegment 186444032 186476800 (18643108413329 / 100000) (9323191006663 / 50000) := by
  exact
    packedTile16384 186444032 186476800 12 1719 13654 27 _ _ (1904363 / 100000) (952183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186476800 :
    ThetaLowerSegment 186476800 186509568 (9323191006663 / 50000) (9324830677843 / 50000) := by
  exact
    packedTile16384 186476800 186509568 12 1722 13655 27 _ _ (95219 / 5000) (1904383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186509568 :
    ThetaLowerSegment 186509568 186542336 (9324830677843 / 50000) (9326455129337 / 50000) := by
  exact
    packedTile16384 186509568 186542336 12 1706 13656 27 _ _ (952199 / 50000) (1904401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186542336 :
    ThetaLowerSegment 186542336 186575104 (9326455129337 / 50000) (9328089117407 / 50000) := by
  exact
    packedTile16384 186542336 186575104 12 1716 13658 27 _ _ (380883 / 20000) (952209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186575104 :
    ThetaLowerSegment 186575104 186607872 (9328089117407 / 50000) (4664858703811 / 25000) := by
  exact
    packedTile16384 186575104 186607872 12 1710 13659 27 _ _ (1904433 / 100000) (476109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186607872 :
    ThetaLowerSegment 186607872 186640640 (4664858703811 / 25000) (18662853304789 / 100000) := by
  exact
    packedTile16384 186607872 186640640 12 1795 13660 27 _ _ (1904451 / 100000) (952227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186640640 :
    ThetaLowerSegment 186640640 186673408 (18662853304789 / 100000) (3733230368673 / 20000) := by
  exact
    packedTile16384 186640640 186673408 12 1732 13661 27 _ _ (476117 / 25000) (1904471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186673408 :
    ThetaLowerSegment 186673408 186706176 (3733230368673 / 20000) (18669385660593 / 100000) := by
  exact
    packedTile16384 186673408 186706176 12 1698 13662 27 _ _ (952243 / 50000) (1904489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186706176 :
    ThetaLowerSegment 186706176 186738944 (18669385660593 / 100000) (583521680697 / 3125) := by
  exact
    packedTile16384 186706176 186738944 12 1737 13664 27 _ _ (1904503 / 100000) (952253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186738944 :
    ThetaLowerSegment 186738944 186771712 (583521680697 / 3125) (2334488576719 / 12500) := by
  exact
    packedTile16384 186738944 186771712 12 1688 13665 27 _ _ (1904521 / 100000) (476131 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186771712 :
    ThetaLowerSegment 186771712 186804480 (2334488576719 / 12500) (9339591257287 / 50000) := by
  exact
    packedTile16384 186771712 186804480 12 1719 13666 27 _ _ (952269 / 50000) (1904541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186804480 :
    ThetaLowerSegment 186804480 186837248 (9339591257287 / 50000) (9341241555061 / 50000) := by
  exact
    packedTile16384 186804480 186837248 12 1733 13667 27 _ _ (476139 / 25000) (1904559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186837248 :
    ThetaLowerSegment 186837248 186870016 (9341241555061 / 50000) (3737163603489 / 20000) := by
  exact
    packedTile16384 186837248 186870016 12 1751 13668 27 _ _ (1904573 / 100000) (59518 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186870016 :
    ThetaLowerSegment 186870016 186902784 (3737163603489 / 20000) (4672270145457 / 25000) := by
  exact
    packedTile16384 186870016 186902784 12 1713 13670 27 _ _ (1904591 / 100000) (952297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186902784 :
    ThetaLowerSegment 186902784 186935552 (4672270145457 / 25000) (934613444781 / 5000) := by
  exact
    packedTile16384 186902784 186935552 12 1674 13671 27 _ _ (59519 / 3125) (1904611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186935552 :
    ThetaLowerSegment 186935552 186968320 (934613444781 / 5000) (584237086066 / 3125) := by
  exact
    packedTile16384 186935552 186968320 12 1742 13672 27 _ _ (952313 / 50000) (1904629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell186968320 :
    ThetaLowerSegment 186968320 187001088 (584237086066 / 3125) (18698796077567 / 100000) := by
  exact
    packedTile16384 186968320 187001088 12 1685 13673 27 _ _ (1904643 / 100000) (952323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187001088 :
    ThetaLowerSegment 187001088 187033856 (18698796077567 / 100000) (18702102569063 / 100000) := by
  exact
    packedTile16384 187001088 187033856 12 1736 13674 27 _ _ (1904661 / 100000) (238083 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187033856 :
    ThetaLowerSegment 187033856 187066624 (18702102569063 / 100000) (9352675023379 / 50000) := by
  exact
    packedTile16384 187033856 187066624 12 1705 13676 27 _ _ (1904679 / 100000) (952341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187066624 :
    ThetaLowerSegment 187066624 187099392 (9352675023379 / 50000) (1870860136283 / 10000) := by
  exact
    packedTile16384 187066624 187099392 12 1707 13677 27 _ _ (238087 / 12500) (1904699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187099392 :
    ThetaLowerSegment 187099392 187132160 (1870860136283 / 10000) (9355952068453 / 50000) := by
  exact
    packedTile16384 187099392 187132160 12 1734 13678 27 _ _ (952357 / 50000) (1904717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187132160 :
    ThetaLowerSegment 187132160 187164928 (9355952068453 / 50000) (18715163131647 / 100000) := by
  exact
    packedTile16384 187132160 187164928 12 1711 13679 27 _ _ (1904731 / 100000) (952367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187164928 :
    ThetaLowerSegment 187164928 187197696 (18715163131647 / 100000) (18718530727879 / 100000) := by
  exact
    packedTile16384 187164928 187197696 12 1768 13680 27 _ _ (1904749 / 100000) (119047 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187197696 :
    ThetaLowerSegment 187197696 187230464 (18718530727879 / 100000) (18721841211187 / 100000) := by
  exact
    packedTile16384 187197696 187230464 12 1738 13682 27 _ _ (952383 / 50000) (1904769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187230464 :
    ThetaLowerSegment 187230464 187263232 (18721841211187 / 100000) (18725104106179 / 100000) := by
  exact
    packedTile16384 187230464 187263232 12 1713 13683 27 _ _ (119049 / 6250) (1904787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187263232 :
    ThetaLowerSegment 187263232 187296000 (18725104106179 / 100000) (18728441317531 / 100000) := by
  exact
    packedTile16384 187263232 187296000 12 1752 13684 27 _ _ (1904801 / 100000) (476201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187296000 :
    ThetaLowerSegment 187296000 187328768 (18728441317531 / 100000) (18731675700193 / 100000) := by
  exact
    packedTile16384 187296000 187328768 12 1698 13685 27 _ _ (1904819 / 100000) (952411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187328768 :
    ThetaLowerSegment 187328768 187361536 (18731675700193 / 100000) (18734923445573 / 100000) := by
  exact
    packedTile16384 187328768 187361536 12 1705 13686 27 _ _ (476209 / 25000) (1904839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187361536 :
    ThetaLowerSegment 187361536 187394304 (18734923445573 / 100000) (18738296942007 / 100000) := by
  exact
    packedTile16384 187361536 187394304 12 1771 13688 27 _ _ (952427 / 50000) (1904857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187394304 :
    ThetaLowerSegment 187394304 187427072 (18738296942007 / 100000) (4685425236621 / 25000) := by
  exact
    packedTile16384 187394304 187427072 12 1787 13689 27 _ _ (1904871 / 100000) (952437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187427072 :
    ThetaLowerSegment 187427072 187459840 (4685425236621 / 25000) (18744910684449 / 100000) := by
  exact
    packedTile16384 187427072 187459840 12 1685 13690 27 _ _ (1904889 / 100000) (476223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187459840 :
    ThetaLowerSegment 187459840 187492608 (18744910684449 / 100000) (18748242365043 / 100000) := by
  exact
    packedTile16384 187459840 187492608 12 1749 13691 27 _ _ (952453 / 50000) (1904909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187492608 :
    ThetaLowerSegment 187492608 187525376 (18748242365043 / 100000) (18751465494759 / 100000) := by
  exact
    packedTile16384 187492608 187525376 12 1692 13692 27 _ _ (1904923 / 100000) (952463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187525376 :
    ThetaLowerSegment 187525376 187558144 (18751465494759 / 100000) (9377331945349 / 50000) := by
  exact
    packedTile16384 187525376 187558144 12 1679 13693 27 _ _ (1904941 / 100000) (119059 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187558144 :
    ThetaLowerSegment 187558144 187590912 (9377331945349 / 50000) (9378943539817 / 50000) := by
  exact
    packedTile16384 187558144 187590912 12 1692 13695 27 _ _ (952479 / 50000) (1904961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187590912 :
    ThetaLowerSegment 187590912 187623680 (9378943539817 / 50000) (9380600868937 / 50000) := by
  exact
    packedTile16384 187590912 187623680 12 1740 13696 27 _ _ (119061 / 6250) (1904979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187623680 :
    ThetaLowerSegment 187623680 187656448 (9380600868937 / 50000) (234554597953 / 1250) := by
  exact
    packedTile16384 187623680 187656448 12 1662 13697 27 _ _ (1904993 / 100000) (476249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187656448 :
    ThetaLowerSegment 187656448 187689216 (234554597953 / 1250) (9383827942613 / 50000) := by
  exact
    packedTile16384 187656448 187689216 12 1726 13698 27 _ _ (1905011 / 100000) (952507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187689216 :
    ThetaLowerSegment 187689216 187721984 (9383827942613 / 50000) (9385467219207 / 50000) := by
  exact
    packedTile16384 187689216 187721984 12 1721 13699 27 _ _ (476257 / 25000) (1905031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187721984 :
    ThetaLowerSegment 187721984 187754752 (9385467219207 / 50000) (9387103653721 / 50000) := by
  exact
    packedTile16384 187721984 187754752 12 1718 13701 27 _ _ (952523 / 50000) (1905049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187754752 :
    ThetaLowerSegment 187754752 187787520 (9387103653721 / 50000) (18777489730991 / 100000) := by
  exact
    packedTile16384 187754752 187787520 12 1723 13702 27 _ _ (1905063 / 100000) (952533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187787520 :
    ThetaLowerSegment 187787520 187820288 (18777489730991 / 100000) (9390424194397 / 50000) := by
  exact
    packedTile16384 187787520 187820288 12 1763 13703 27 _ _ (1905081 / 100000) (476271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187820288 :
    ThetaLowerSegment 187820288 187853056 (9390424194397 / 50000) (4696003189143 / 25000) := by
  exact
    packedTile16384 187820288 187853056 12 1661 13704 27 _ _ (952549 / 50000) (1905101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187853056 :
    ThetaLowerSegment 187853056 187885824 (4696003189143 / 25000) (939365239851 / 5000) := by
  exact
    packedTile16384 187853056 187885824 12 1728 13705 27 _ _ (476279 / 25000) (1905119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187885824 :
    ThetaLowerSegment 187885824 187918592 (939365239851 / 5000) (4697660647509 / 25000) := by
  exact
    packedTile16384 187885824 187918592 12 1752 13707 27 _ _ (1905133 / 100000) (119071 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187918592 :
    ThetaLowerSegment 187918592 187951360 (4697660647509 / 25000) (9396985443543 / 50000) := by
  exact
    packedTile16384 187918592 187951360 12 1747 13708 27 _ _ (38103 / 2000) (1905153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187951360 :
    ThetaLowerSegment 187951360 187984128 (9396985443543 / 50000) (9398605788927 / 50000) := by
  exact
    packedTile16384 187951360 187984128 12 1701 13709 27 _ _ (119073 / 6250) (1905171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell187984128 :
    ThetaLowerSegment 187984128 188016896 (9398605788927 / 50000) (18800505642719 / 100000) := by
  exact
    packedTile16384 187984128 188016896 12 1729 13710 27 _ _ (381037 / 20000) (476297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188016896 :
    ThetaLowerSegment 188016896 188049664 (18800505642719 / 100000) (9401911300571 / 50000) := by
  exact
    packedTile16384 188016896 188049664 12 1741 13711 27 _ _ (1905203 / 100000) (952603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188049664 :
    ThetaLowerSegment 188049664 188082432 (9401911300571 / 50000) (9403553600211 / 50000) := by
  exact
    packedTile16384 188049664 188082432 12 1724 13713 27 _ _ (95261 / 5000) (1905223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188082432 :
    ThetaLowerSegment 188082432 188115200 (9403553600211 / 50000) (4702598433993 / 25000) := by
  exact
    packedTile16384 188082432 188115200 12 1725 13714 27 _ _ (952619 / 50000) (1905241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188115200 :
    ThetaLowerSegment 188115200 188147968 (4702598433993 / 25000) (4703425314663 / 25000) := by
  exact
    packedTile16384 188115200 188147968 12 1736 13715 27 _ _ (381051 / 20000) (952629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188147968 :
    ThetaLowerSegment 188147968 188180736 (4703425314663 / 25000) (4704244581623 / 25000) := by
  exact
    packedTile16384 188147968 188180736 12 1720 13716 27 _ _ (238159 / 12500) (76211 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188180736 :
    ThetaLowerSegment 188180736 188213504 (4704244581623 / 25000) (9410073411881 / 50000) := by
  exact
    packedTile16384 188180736 188213504 12 1663 13717 27 _ _ (190529 / 10000) (1905293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188213504 :
    ThetaLowerSegment 188213504 188246272 (9410073411881 / 50000) (18823387750969 / 100000) := by
  exact
    packedTile16384 188213504 188246272 12 1701 13719 27 _ _ (1905307 / 100000) (190531 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188246272 :
    ThetaLowerSegment 188246272 188279040 (18823387750969 / 100000) (2353330017593 / 12500) := by
  exact
    packedTile16384 188246272 188279040 12 1707 13720 27 _ _ (76213 / 4000) (119083 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188279040 :
    ThetaLowerSegment 188279040 188311808 (2353330017593 / 12500) (235373680811 / 1250) := by
  exact
    packedTile16384 188279040 188311808 12 1708 13721 27 _ _ (952671 / 50000) (381069 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188311808 :
    ThetaLowerSegment 188311808 188344576 (235373680811 / 1250) (18833234559207 / 100000) := by
  exact
    packedTile16384 188311808 188344576 12 1753 13722 27 _ _ (1905359 / 100000) (952681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188344576 :
    ThetaLowerSegment 188344576 188377344 (18833234559207 / 100000) (4709118901371 / 25000) := by
  exact
    packedTile16384 188344576 188377344 12 1701 13723 27 _ _ (1905377 / 100000) (95269 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188377344 :
    ThetaLowerSegment 188377344 188410112 (4709118901371 / 25000) (9419900259007 / 50000) := by
  exact
    packedTile16384 188377344 188410112 12 1745 13725 27 _ _ (952697 / 50000) (1905397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188410112 :
    ThetaLowerSegment 188410112 188442880 (9419900259007 / 50000) (9421504615911 / 50000) := by
  exact
    packedTile16384 188410112 188442880 12 1684 13726 27 _ _ (476353 / 25000) (381083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188442880 :
    ThetaLowerSegment 188442880 188475648 (9421504615911 / 50000) (18846303718563 / 100000) := by
  exact
    packedTile16384 188442880 188475648 12 1729 13727 27 _ _ (1905429 / 100000) (238179 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188475648 :
    ThetaLowerSegment 188475648 188508416 (18846303718563 / 100000) (18849577274791 / 100000) := by
  exact
    packedTile16384 188475648 188508416 12 1718 13728 27 _ _ (952723 / 50000) (1905449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188508416 :
    ThetaLowerSegment 188508416 188541184 (18849577274791 / 100000) (18852772737919 / 100000) := by
  exact
    packedTile16384 188508416 188541184 12 1677 13729 27 _ _ (238183 / 12500) (1905467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188541184 :
    ThetaLowerSegment 188541184 188573952 (18852772737919 / 100000) (1885599490629 / 10000) := by
  exact
    packedTile16384 188541184 188573952 12 1691 13731 27 _ _ (1905481 / 100000) (476371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188573952 :
    ThetaLowerSegment 188573952 188606720 (1885599490629 / 10000) (18859236160089 / 100000) := by
  exact
    packedTile16384 188573952 188606720 12 1701 13732 27 _ _ (1905499 / 100000) (952751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188606720 :
    ThetaLowerSegment 188606720 188639488 (18859236160089 / 100000) (18862523175189 / 100000) := by
  exact
    packedTile16384 188606720 188639488 12 1725 13733 27 _ _ (476379 / 25000) (1905519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188639488 :
    ThetaLowerSegment 188639488 188672256 (18862523175189 / 100000) (18865884535401 / 100000) := by
  exact
    packedTile16384 188639488 188672256 12 1764 13734 27 _ _ (1905533 / 100000) (59548 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188672256 :
    ThetaLowerSegment 188672256 188705024 (18865884535401 / 100000) (9434614388703 / 50000) := by
  exact
    packedTile16384 188672256 188705024 12 1755 13735 27 _ _ (1905551 / 100000) (952777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188705024 :
    ThetaLowerSegment 188705024 188737792 (9434614388703 / 50000) (1887240726483 / 10000) := by
  exact
    packedTile16384 188705024 188737792 12 1668 13736 27 _ _ (59549 / 3125) (1905571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188737792 :
    ThetaLowerSegment 188737792 188770560 (1887240726483 / 10000) (3775128970749 / 20000) := by
  exact
    packedTile16384 188737792 188770560 12 1699 13738 27 _ _ (381117 / 20000) (476397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188770560 :
    ThetaLowerSegment 188770560 188803328 (3775128970749 / 20000) (9439490782299 / 50000) := by
  exact
    packedTile16384 188770560 188803328 12 1751 13739 27 _ _ (1905603 / 100000) (952803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188803328 :
    ThetaLowerSegment 188803328 188836096 (9439490782299 / 50000) (9441097219959 / 50000) := by
  exact
    packedTile16384 188803328 188836096 12 1686 13740 27 _ _ (95281 / 5000) (1905623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188836096 :
    ThetaLowerSegment 188836096 188868864 (9441097219959 / 50000) (18885515965209 / 100000) := by
  exact
    packedTile16384 188836096 188868864 12 1743 13741 27 _ _ (1905637 / 100000) (47641 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188868864 :
    ThetaLowerSegment 188868864 188901632 (18885515965209 / 100000) (18888736522159 / 100000) := by
  exact
    packedTile16384 188868864 188901632 12 1690 13742 27 _ _ (381131 / 20000) (952829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188901632 :
    ThetaLowerSegment 188901632 188934400 (18888736522159 / 100000) (18892065731143 / 100000) := by
  exact
    packedTile16384 188901632 188934400 12 1747 13744 27 _ _ (238209 / 12500) (76227 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188934400 :
    ThetaLowerSegment 188934400 188967168 (18892065731143 / 100000) (18895339706563 / 100000) := by
  exact
    packedTile16384 188934400 188967168 12 1718 13745 27 _ _ (190569 / 10000) (1905693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188967168 :
    ThetaLowerSegment 188967168 188999936 (18895339706563 / 100000) (18898632768259 / 100000) := by
  exact
    packedTile16384 188967168 188999936 12 1728 13746 27 _ _ (1905707 / 100000) (190571 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell188999936 :
    ThetaLowerSegment 188999936 189032704 (18898632768259 / 100000) (18901904896367 / 100000) := by
  exact
    packedTile16384 188999936 189032704 12 1717 13747 27 _ _ (476431 / 25000) (1905727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189032704 :
    ThetaLowerSegment 189032704 189065472 (18901904896367 / 100000) (3781043796341 / 20000) := by
  exact
    packedTile16384 189032704 189065472 12 1739 13748 27 _ _ (952871 / 50000) (381149 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189065472 :
    ThetaLowerSegment 189065472 189098240 (3781043796341 / 20000) (1890852547357 / 10000) := by
  exact
    packedTile16384 189065472 189098240 12 1735 13750 27 _ _ (1905759 / 100000) (952881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189098240 :
    ThetaLowerSegment 189098240 189131008 (1890852547357 / 10000) (9455936961001 / 50000) := by
  exact
    packedTile16384 189098240 189131008 12 1757 13751 27 _ _ (119111 / 6250) (1905779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189131008 :
    ThetaLowerSegment 189131008 189163776 (9455936961001 / 50000) (9457570226459 / 50000) := by
  exact
    packedTile16384 189131008 189163776 12 1714 13752 27 _ _ (952897 / 50000) (1905797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189163776 :
    ThetaLowerSegment 189163776 189196544 (9457570226459 / 50000) (18918462281491 / 100000) := by
  exact
    packedTile16384 189163776 189196544 12 1743 13753 27 _ _ (1905811 / 100000) (952907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189196544 :
    ThetaLowerSegment 189196544 189229312 (18918462281491 / 100000) (18921763175587 / 100000) := by
  exact
    packedTile16384 189196544 189229312 12 1732 13754 27 _ _ (476457 / 25000) (1905831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189229312 :
    ThetaLowerSegment 189229312 189262080 (18921763175587 / 100000) (18924957373483 / 100000) := by
  exact
    packedTile16384 189229312 189262080 12 1676 13756 27 _ _ (952923 / 50000) (1905849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189262080 :
    ThetaLowerSegment 189262080 189294848 (18924957373483 / 100000) (4732073634899 / 25000) := by
  exact
    packedTile16384 189262080 189294848 12 1751 13757 27 _ _ (1905863 / 100000) (952933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189294848 :
    ThetaLowerSegment 189294848 189327616 (4732073634899 / 25000) (4732882680959 / 25000) := by
  exact
    packedTile16384 189294848 189327616 12 1698 13758 27 _ _ (47647 / 2500) (1905883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189327616 :
    ThetaLowerSegment 189327616 189360384 (4732882680959 / 25000) (18934826019749 / 100000) := by
  exact
    packedTile16384 189327616 189360384 12 1729 13759 27 _ _ (1905897 / 100000) (19059 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189360384 :
    ThetaLowerSegment 189360384 189393152 (18934826019749 / 100000) (9469032084667 / 50000) := by
  exact
    packedTile16384 189360384 189393152 12 1699 13760 27 _ _ (381183 / 20000) (952959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189393152 :
    ThetaLowerSegment 189393152 189425920 (9469032084667 / 50000) (9470725505249 / 50000) := by
  exact
    packedTile16384 189393152 189425920 12 1777 13762 27 _ _ (476483 / 25000) (381187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189425920 :
    ThetaLowerSegment 189425920 189458688 (9470725505249 / 50000) (9472341750001 / 50000) := by
  exact
    packedTile16384 189425920 189458688 12 1696 13763 27 _ _ (1905949 / 100000) (59561 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189458688 :
    ThetaLowerSegment 189458688 189491456 (9472341750001 / 50000) (18947963669209 / 100000) := by
  exact
    packedTile16384 189458688 189491456 12 1721 13764 27 _ _ (1905967 / 100000) (190597 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189491456 :
    ThetaLowerSegment 189491456 189524224 (18947963669209 / 100000) (18951177158233 / 100000) := by
  exact
    packedTile16384 189491456 189524224 12 1686 13765 27 _ _ (59562 / 3125) (1905987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189524224 :
    ThetaLowerSegment 189524224 189556992 (18951177158233 / 100000) (4738600051481 / 25000) := by
  exact
    packedTile16384 189524224 189556992 12 1691 13766 27 _ _ (1906001 / 100000) (476501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189556992 :
    ThetaLowerSegment 189556992 189589760 (4738600051481 / 25000) (947878591077 / 5000) := by
  exact
    packedTile16384 189556992 189589760 12 1664 13767 27 _ _ (1906019 / 100000) (953011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189589760 :
    ThetaLowerSegment 189589760 189622528 (947878591077 / 5000) (4740215409919 / 25000) := by
  exact
    packedTile16384 189589760 189622528 12 1726 13769 27 _ _ (476509 / 25000) (1906039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189622528 :
    ThetaLowerSegment 189622528 189655296 (4740215409919 / 25000) (1896413623873 / 10000) := by
  exact
    packedTile16384 189622528 189655296 12 1718 13770 27 _ _ (1906053 / 100000) (238257 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189655296 :
    ThetaLowerSegment 189655296 189688064 (1896413623873 / 10000) (379348141097 / 2000) := by
  exact
    packedTile16384 189655296 189688064 12 1716 13771 27 _ _ (190607 / 10000) (1906073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189688064 :
    ThetaLowerSegment 189688064 189720832 (379348141097 / 2000) (9485345622237 / 50000) := by
  exact
    packedTile16384 189688064 189720832 12 1723 13772 27 _ _ (238261 / 12500) (1906091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189720832 :
    ThetaLowerSegment 189720832 189753600 (9485345622237 / 50000) (9487030619057 / 50000) := by
  exact
    packedTile16384 189720832 189753600 12 1768 13773 27 _ _ (381221 / 20000) (476527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189753600 :
    ThetaLowerSegment 189753600 189786368 (9487030619057 / 50000) (9488624137049 / 50000) := by
  exact
    packedTile16384 189753600 189786368 12 1672 13775 27 _ _ (953061 / 50000) (15249 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189786368 :
    ThetaLowerSegment 189786368 189819136 (9488624137049 / 50000) (189805230209 / 1000) := by
  exact
    packedTile16384 189786368 189819136 12 1718 13776 27 _ _ (1906139 / 100000) (953071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189819136 :
    ThetaLowerSegment 189819136 189851904 (189805230209 / 1000) (18983834015609 / 100000) := by
  exact
    packedTile16384 189819136 189851904 12 1737 13777 28 _ _ (1906157 / 100000) (23827 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189851904 :
    ThetaLowerSegment 189851904 189884672 (18983834015609 / 100000) (759485572853 / 4000) := by
  exact
    packedTile16384 189851904 189884672 12 1734 13778 28 _ _ (953087 / 50000) (1906177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189884672 :
    ThetaLowerSegment 189884672 189917440 (759485572853 / 4000) (9495211844209 / 50000) := by
  exact
    packedTile16384 189884672 189917440 12 1723 13779 28 _ _ (1906191 / 100000) (953097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189917440 :
    ThetaLowerSegment 189917440 189950208 (9495211844209 / 50000) (9496851183949 / 50000) := by
  exact
    packedTile16384 189917440 189950208 12 1720 13781 28 _ _ (1906209 / 100000) (476553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189950208 :
    ThetaLowerSegment 189950208 189982976 (9496851183949 / 50000) (94984972101 / 500) := by
  exact
    packedTile16384 189950208 189982976 12 1727 13782 28 _ _ (953113 / 50000) (1906229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell189982976 :
    ThetaLowerSegment 189982976 190015744 (94984972101 / 500) (475008735197 / 2500) := by
  exact
    packedTile16384 189982976 190015744 12 1760 13783 28 _ _ (1906243 / 100000) (953123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190015744 :
    ThetaLowerSegment 190015744 190048512 (475008735197 / 2500) (950180360311 / 5000) := by
  exact
    packedTile16384 190015744 190048512 12 1709 13784 28 _ _ (95313 / 5000) (1906263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190048512 :
    ThetaLowerSegment 190048512 190081280 (950180360311 / 5000) (593965902437 / 3125) := by
  exact
    packedTile16384 190048512 190081280 12 1732 13785 28 _ _ (1906277 / 100000) (47657 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190081280 :
    ThetaLowerSegment 190081280 190114048 (593965902437 / 3125) (9505091946397 / 50000) := by
  exact
    packedTile16384 190081280 190114048 12 1718 13786 28 _ _ (381259 / 20000) (953149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190114048 :
    ThetaLowerSegment 190114048 190146816 (9505091946397 / 50000) (9506746625213 / 50000) := by
  exact
    packedTile16384 190114048 190146816 12 1736 13788 28 _ _ (238289 / 12500) (381263 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190146816 :
    ThetaLowerSegment 190146816 190179584 (9506746625213 / 50000) (9508355566889 / 50000) := by
  exact
    packedTile16384 190146816 190179584 12 1688 13789 28 _ _ (1906329 / 100000) (476583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190179584 :
    ThetaLowerSegment 190179584 190212352 (9508355566889 / 50000) (2377498517819 / 12500) := by
  exact
    packedTile16384 190179584 190212352 12 1719 13790 28 _ _ (953173 / 50000) (1906349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190212352 :
    ThetaLowerSegment 190212352 190245120 (2377498517819 / 12500) (2377909339261 / 12500) := by
  exact
    packedTile16384 190212352 190245120 12 1724 13791 28 _ _ (476591 / 25000) (1906367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190245120 :
    ThetaLowerSegment 190245120 190277888 (2377909339261 / 12500) (2378321117557 / 12500) := by
  exact
    packedTile16384 190245120 190277888 12 1728 13792 28 _ _ (1906381 / 100000) (119149 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190277888 :
    ThetaLowerSegment 190277888 190310656 (2378321117557 / 12500) (951490300213 / 5000) := by
  exact
    packedTile16384 190277888 190310656 12 1698 13794 28 _ _ (953199 / 50000) (1906401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190310656 :
    ThetaLowerSegment 190310656 190343424 (951490300213 / 5000) (1903307359957 / 10000) := by
  exact
    packedTile16384 190310656 190343424 12 1714 13795 28 _ _ (381283 / 20000) (953209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190343424 :
    ThetaLowerSegment 190343424 190376192 (1903307359957 / 10000) (19036392699423 / 100000) := by
  exact
    packedTile16384 190343424 190376192 12 1741 13796 28 _ _ (1906433 / 100000) (476609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190376192 :
    ThetaLowerSegment 190376192 190408960 (19036392699423 / 100000) (19039715641773 / 100000) := by
  exact
    packedTile16384 190376192 190408960 12 1743 13797 28 _ _ (38129 / 2000) (1906453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190408960 :
    ThetaLowerSegment 190408960 190441728 (19039715641773 / 100000) (19042914693399 / 100000) := by
  exact
    packedTile16384 190408960 190441728 12 1678 13798 28 _ _ (1906467 / 100000) (190647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190441728 :
    ThetaLowerSegment 190441728 190474496 (19042914693399 / 100000) (19046142370811 / 100000) := by
  exact
    packedTile16384 190441728 190474496 12 1693 13800 28 _ _ (476621 / 25000) (1906487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190474496 :
    ThetaLowerSegment 190474496 190507264 (19046142370811 / 100000) (1904941964603 / 10000) := by
  exact
    packedTile16384 190474496 190507264 12 1719 13801 28 _ _ (1906501 / 100000) (238313 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190507264 :
    ThetaLowerSegment 190507264 190540032 (1904941964603 / 10000) (9526345616317 / 50000) := by
  exact
    packedTile16384 190507264 190540032 12 1716 13802 28 _ _ (1906519 / 100000) (953261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190540032 :
    ThetaLowerSegment 190540032 190572800 (9526345616317 / 50000) (9527974751329 / 50000) := by
  exact
    packedTile16384 190540032 190572800 12 1709 13803 28 _ _ (238317 / 12500) (1906539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190572800 :
    ThetaLowerSegment 190572800 190605568 (9527974751329 / 50000) (19059181109993 / 100000) := by
  exact
    packedTile16384 190572800 190605568 12 1695 13804 28 _ _ (1906553 / 100000) (476639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190605568 :
    ThetaLowerSegment 190605568 190638336 (19059181109993 / 100000) (19062492822083 / 100000) := by
  exact
    packedTile16384 190605568 190638336 12 1737 13805 28 _ _ (190657 / 10000) (1906573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190638336 :
    ThetaLowerSegment 190638336 190671104 (19062492822083 / 100000) (19065817909811 / 100000) := by
  exact
    packedTile16384 190638336 190671104 12 1744 13807 28 _ _ (1906587 / 100000) (190659 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190671104 :
    ThetaLowerSegment 190671104 190703872 (19065817909811 / 100000) (19069082017571 / 100000) := by
  exact
    packedTile16384 190671104 190703872 12 1712 13808 28 _ _ (381321 / 20000) (119163 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190703872 :
    ThetaLowerSegment 190703872 190736640 (19069082017571 / 100000) (19072351874301 / 100000) := by
  exact
    packedTile16384 190703872 190736640 12 1715 13809 28 _ _ (953311 / 50000) (15253 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190736640 :
    ThetaLowerSegment 190736640 190769408 (19072351874301 / 100000) (9537780373869 / 50000) := by
  exact
    packedTile16384 190736640 190769408 12 1683 13810 28 _ _ (1906639 / 100000) (953321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190769408 :
    ThetaLowerSegment 190769408 190802176 (9537780373869 / 50000) (9539428677981 / 50000) := by
  exact
    packedTile16384 190769408 190802176 12 1729 13811 28 _ _ (59583 / 3125) (1906659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190802176 :
    ThetaLowerSegment 190802176 190834944 (9539428677981 / 50000) (3816423934693 / 20000) := by
  exact
    packedTile16384 190802176 190834944 12 1711 13813 28 _ _ (1906673 / 100000) (476669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190834944 :
    ThetaLowerSegment 190834944 190867712 (3816423934693 / 20000) (3817063819857 / 20000) := by
  exact
    packedTile16384 190834944 190867712 12 1678 13814 28 _ _ (190669 / 10000) (1906693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190867712 :
    ThetaLowerSegment 190867712 190900480 (3817063819857 / 20000) (3817721634117 / 20000) := by
  exact
    packedTile16384 190867712 190900480 12 1725 13815 28 _ _ (476677 / 25000) (1906711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190900480 :
    ThetaLowerSegment 190900480 190933248 (3817721634117 / 20000) (3818379835587 / 20000) := by
  exact
    packedTile16384 190900480 190933248 12 1726 13816 28 _ _ (76269 / 4000) (238341 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190933248 :
    ThetaLowerSegment 190933248 190966016 (3818379835587 / 20000) (3819024314383 / 20000) := by
  exact
    packedTile16384 190933248 190966016 12 1690 13817 28 _ _ (953371 / 50000) (381349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190966016 :
    ThetaLowerSegment 190966016 190998784 (3819024314383 / 20000) (19098336367589 / 100000) := by
  exact
    packedTile16384 190966016 190998784 12 1686 13819 28 _ _ (1906759 / 100000) (953381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell190998784 :
    ThetaLowerSegment 190998784 191031552 (19098336367589 / 100000) (19101610301981 / 100000) := by
  exact
    packedTile16384 190998784 191031552 12 1717 13820 28 _ _ (238347 / 12500) (1906779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191031552 :
    ThetaLowerSegment 191031552 191064320 (19101610301981 / 100000) (19104947189731 / 100000) := by
  exact
    packedTile16384 191031552 191064320 12 1750 13821 28 _ _ (1906793 / 100000) (476699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191064320 :
    ThetaLowerSegment 191064320 191097088 (19104947189731 / 100000) (9554125846597 / 50000) := by
  exact
    packedTile16384 191064320 191097088 12 1733 13822 28 _ _ (1906811 / 100000) (953407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191097088 :
    ThetaLowerSegment 191097088 191129856 (9554125846597 / 50000) (9555769532333 / 50000) := by
  exact
    packedTile16384 191097088 191129856 12 1724 13823 28 _ _ (476707 / 25000) (1906831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191129856 :
    ThetaLowerSegment 191129856 191162624 (9555769532333 / 50000) (19114736843731 / 100000) := by
  exact
    packedTile16384 191129856 191162624 12 1677 13824 28 _ _ (381369 / 20000) (59589 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191162624 :
    ThetaLowerSegment 191162624 191195392 (19114736843731 / 100000) (19117993764027 / 100000) := by
  exact
    packedTile16384 191162624 191195392 12 1708 13826 28 _ _ (953431 / 50000) (381373 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191195392 :
    ThetaLowerSegment 191195392 191228160 (19117993764027 / 100000) (19121311733487 / 100000) := by
  exact
    packedTile16384 191195392 191228160 12 1740 13827 28 _ _ (1906879 / 100000) (953441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191228160 :
    ThetaLowerSegment 191228160 191260928 (19121311733487 / 100000) (19124572525647 / 100000) := by
  exact
    packedTile16384 191228160 191260928 12 1710 13828 28 _ _ (119181 / 6250) (1906899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191260928 :
    ThetaLowerSegment 191260928 191293696 (19124572525647 / 100000) (3825568957671 / 20000) := by
  exact
    packedTile16384 191260928 191293696 12 1716 13829 28 _ _ (1906913 / 100000) (476729 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191293696 :
    ThetaLowerSegment 191293696 191326464 (3825568957671 / 20000) (19131101826503 / 100000) := by
  exact
    packedTile16384 191293696 191326464 12 1708 13830 28 _ _ (1906931 / 100000) (953467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191326464 :
    ThetaLowerSegment 191326464 191359232 (19131101826503 / 100000) (19134381777063 / 100000) := by
  exact
    packedTile16384 191326464 191359232 12 1720 13832 28 _ _ (476737 / 25000) (1906951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191359232 :
    ThetaLowerSegment 191359232 191392000 (19134381777063 / 100000) (598049844159 / 3125) := by
  exact
    packedTile16384 191359232 191392000 12 1685 13833 28 _ _ (381393 / 20000) (238371 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191392000 :
    ThetaLowerSegment 191392000 191424768 (598049844159 / 3125) (2392610331257 / 12500) := by
  exact
    packedTile16384 191392000 191424768 12 1724 13834 28 _ _ (953491 / 50000) (381397 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191424768 :
    ThetaLowerSegment 191424768 191457536 (2392610331257 / 12500) (2393010801047 / 12500) := by
  exact
    packedTile16384 191424768 191457536 12 1680 13835 28 _ _ (1906999 / 100000) (953501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191457536 :
    ThetaLowerSegment 191457536 191490304 (2393010801047 / 12500) (1196711239063 / 6250) := by
  exact
    packedTile16384 191457536 191490304 12 1727 13836 28 _ _ (238377 / 12500) (1907019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191490304 :
    ThetaLowerSegment 191490304 191523072 (1196711239063 / 6250) (9575320425719 / 50000) := by
  exact
    packedTile16384 191490304 191523072 12 1710 13838 28 _ _ (1907033 / 100000) (476759 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191523072 :
    ThetaLowerSegment 191523072 191555840 (9575320425719 / 50000) (4788468325297 / 25000) := by
  exact
    packedTile16384 191523072 191555840 12 1695 13839 28 _ _ (38141 / 2000) (1907053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191555840 :
    ThetaLowerSegment 191555840 191588608 (4788468325297 / 25000) (38314367939 / 200) := by
  exact
    packedTile16384 191555840 191588608 12 1736 13840 28 _ _ (1907067 / 100000) (190707 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191588608 :
    ThetaLowerSegment 191588608 191621376 (38314367939 / 200) (1916039168647 / 10000) := by
  exact
    packedTile16384 191588608 191621376 12 1682 13841 28 _ _ (381417 / 20000) (119193 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191621376 :
    ThetaLowerSegment 191621376 191654144 (1916039168647 / 10000) (9581811158629 / 50000) := by
  exact
    packedTile16384 191621376 191654144 12 1694 13842 28 _ _ (953551 / 50000) (381421 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191654144 :
    ThetaLowerSegment 191654144 191686912 (9581811158629 / 50000) (1197927834273 / 6250) := by
  exact
    packedTile16384 191654144 191686912 12 1690 13843 28 _ _ (1907119 / 100000) (953561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191686912 :
    ThetaLowerSegment 191686912 191719680 (1197927834273 / 6250) (1198132970589 / 6250) := by
  exact
    packedTile16384 191686912 191719680 12 1721 13845 28 _ _ (59598 / 3125) (1907139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191719680 :
    ThetaLowerSegment 191719680 191752448 (1198132970589 / 6250) (19173417368349 / 100000) := by
  exact
    packedTile16384 191719680 191752448 12 1725 13846 28 _ _ (1907153 / 100000) (476789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191752448 :
    ThetaLowerSegment 191752448 191785216 (19173417368349 / 100000) (19176714865279 / 100000) := by
  exact
    packedTile16384 191752448 191785216 12 1729 13847 28 _ _ (190717 / 10000) (1907173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191785216 :
    ThetaLowerSegment 191785216 191817984 (19176714865279 / 100000) (1198748152093 / 6250) := by
  exact
    packedTile16384 191785216 191817984 12 1707 13848 28 _ _ (1907187 / 100000) (190719 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191817984 :
    ThetaLowerSegment 191817984 191850752 (1198748152093 / 6250) (4795813182893 / 25000) := by
  exact
    packedTile16384 191817984 191850752 12 1721 13849 28 _ _ (476801 / 25000) (1907207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191850752 :
    ThetaLowerSegment 191850752 191883520 (4795813182893 / 25000) (19186466398957 / 100000) := by
  exact
    packedTile16384 191850752 191883520 12 1685 13851 28 _ _ (1907221 / 100000) (238403 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191883520 :
    ThetaLowerSegment 191883520 191916288 (19186466398957 / 100000) (3837949751111 / 20000) := by
  exact
    packedTile16384 191883520 191916288 12 1721 13852 28 _ _ (953619 / 50000) (1907241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191916288 :
    ThetaLowerSegment 191916288 191949056 (3837949751111 / 20000) (767723000331 / 4000) := by
  exact
    packedTile16384 191916288 191949056 12 1744 13853 28 _ _ (381451 / 20000) (953629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191949056 :
    ThetaLowerSegment 191949056 191981824 (767723000331 / 4000) (19196328816013 / 100000) := by
  exact
    packedTile16384 191949056 191981824 12 1706 13854 28 _ _ (1907273 / 100000) (476819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell191981824 :
    ThetaLowerSegment 191981824 192014592 (19196328816013 / 100000) (19199525434053 / 100000) := by
  exact
    packedTile16384 191981824 192014592 12 1676 13855 28 _ _ (190729 / 10000) (1907293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192014592 :
    ThetaLowerSegment 192014592 192047360 (19199525434053 / 100000) (19202771670567 / 100000) := by
  exact
    packedTile16384 192014592 192047360 12 1702 13856 28 _ _ (1907307 / 100000) (190731 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192047360 :
    ThetaLowerSegment 192047360 192080128 (19202771670567 / 100000) (19206050360523 / 100000) := by
  exact
    packedTile16384 192047360 192080128 12 1719 13858 28 _ _ (476831 / 25000) (1907327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192080128 :
    ThetaLowerSegment 192080128 192112896 (19206050360523 / 100000) (960466263251 / 5000) := by
  exact
    packedTile16384 192080128 192112896 12 1717 13859 28 _ _ (1907341 / 100000) (119209 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192112896 :
    ThetaLowerSegment 192112896 192145664 (960466263251 / 5000) (240156381911 / 1250) := by
  exact
    packedTile16384 192112896 192145664 12 1670 13860 28 _ _ (953679 / 50000) (1907361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192145664 :
    ThetaLowerSegment 192145664 192178432 (240156381911 / 1250) (120099362818 / 625) := by
  exact
    packedTile16384 192145664 192178432 12 1776 13861 28 _ _ (15259 / 800) (953689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192178432 :
    ThetaLowerSegment 192178432 192211200 (120099362818 / 625) (600601541832 / 3125) := by
  exact
    packedTile16384 192178432 192211200 12 1757 13862 28 _ _ (59606 / 3125) (381479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192211200 :
    ThetaLowerSegment 192211200 192243968 (600601541832 / 3125) (4805630613117 / 25000) := by
  exact
    packedTile16384 192211200 192243968 12 1716 13864 28 _ _ (1907409 / 100000) (476853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192243968 :
    ThetaLowerSegment 192243968 192276736 (4805630613117 / 25000) (1201609602007 / 6250) := by
  exact
    packedTile16384 192243968 192276736 12 1694 13865 28 _ _ (953713 / 50000) (1907429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192276736 :
    ThetaLowerSegment 192276736 192309504 (1201609602007 / 6250) (9614526754251 / 50000) := by
  exact
    packedTile16384 192276736 192309504 12 1730 13866 28 _ _ (1907443 / 100000) (953723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192309504 :
    ThetaLowerSegment 192309504 192342272 (9614526754251 / 50000) (9616170031041 / 50000) := by
  exact
    packedTile16384 192309504 192342272 12 1723 13867 28 _ _ (95373 / 5000) (1907463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192342272 :
    ThetaLowerSegment 192342272 192375040 (9616170031041 / 50000) (9617844795847 / 50000) := by
  exact
    packedTile16384 192342272 192375040 12 1756 13868 28 _ _ (1907477 / 100000) (47687 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192375040 :
    ThetaLowerSegment 192375040 192407808 (9617844795847 / 50000) (4809739282229 / 25000) := by
  exact
    packedTile16384 192375040 192407808 12 1713 13869 28 _ _ (953747 / 50000) (1907497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192407808 :
    ThetaLowerSegment 192407808 192440576 (4809739282229 / 25000) (19242190360061 / 100000) := by
  exact
    packedTile16384 192407808 192440576 12 1695 13871 28 _ _ (1907511 / 100000) (953757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192440576 :
    ThetaLowerSegment 192440576 192473344 (19242190360061 / 100000) (19245484660917 / 100000) := by
  exact
    packedTile16384 192440576 192473344 12 1727 13872 28 _ _ (238441 / 12500) (1907531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192473344 :
    ThetaLowerSegment 192473344 192506112 (19245484660917 / 100000) (19248746562867 / 100000) := by
  exact
    packedTile16384 192473344 192506112 12 1710 13873 28 _ _ (381509 / 20000) (476887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192506112 :
    ThetaLowerSegment 192506112 192538880 (19248746562867 / 100000) (19252002771201 / 100000) := by
  exact
    packedTile16384 192506112 192538880 12 1707 13874 28 _ _ (953781 / 50000) (381513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192538880 :
    ThetaLowerSegment 192538880 192571648 (19252002771201 / 100000) (19255268546449 / 100000) := by
  exact
    packedTile16384 192538880 192571648 12 1712 13875 28 _ _ (1907579 / 100000) (953791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192571648 :
    ThetaLowerSegment 192571648 192604416 (19255268546449 / 100000) (19258547703973 / 100000) := by
  exact
    packedTile16384 192571648 192604416 12 1719 13877 28 _ _ (476899 / 25000) (1907599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192604416 :
    ThetaLowerSegment 192604416 192637184 (19258547703973 / 100000) (1203866088283 / 6250) := by
  exact
    packedTile16384 192604416 192637184 12 1735 13878 28 _ _ (1907613 / 100000) (59613 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192637184 :
    ThetaLowerSegment 192637184 192669952 (1203866088283 / 6250) (9632627450779 / 50000) := by
  exact
    packedTile16384 192637184 192669952 12 1781 13879 28 _ _ (190763 / 10000) (1907633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192669952 :
    ThetaLowerSegment 192669952 192702720 (9632627450779 / 50000) (1926852842381 / 10000) := by
  exact
    packedTile16384 192669952 192702720 12 1716 13880 28 _ _ (1907647 / 100000) (38153 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192702720 :
    ThetaLowerSegment 192702720 192735488 (1926852842381 / 10000) (1927182868253 / 10000) := by
  exact
    packedTile16384 192702720 192735488 12 1730 13881 28 _ _ (119229 / 6250) (1907667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192735488 :
    ThetaLowerSegment 192735488 192768256 (1927182868253 / 10000) (9637543500839 / 50000) := by
  exact
    packedTile16384 192735488 192768256 12 1708 13882 28 _ _ (1907681 / 100000) (476921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192768256 :
    ThetaLowerSegment 192768256 192801024 (9637543500839 / 50000) (481960589137 / 2500) := by
  exact
    packedTile16384 192768256 192801024 12 1749 13884 28 _ _ (953849 / 50000) (1907701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192801024 :
    ThetaLowerSegment 192801024 192833792 (481960589137 / 2500) (19281720097 / 100) := by
  exact
    packedTile16384 192801024 192833792 12 1728 13885 28 _ _ (381543 / 20000) (953859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192833792 :
    ThetaLowerSegment 192833792 192866560 (19281720097 / 100) (964249592869 / 5000) := by
  exact
    packedTile16384 192833792 192866560 12 1715 13886 28 _ _ (476933 / 25000) (381547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192866560 :
    ThetaLowerSegment 192866560 192899328 (964249592869 / 5000) (19288256015919 / 100000) := by
  exact
    packedTile16384 192866560 192899328 12 1711 13887 28 _ _ (1907749 / 100000) (238469 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192899328 :
    ThetaLowerSegment 192899328 192932096 (19288256015919 / 100000) (19291533557907 / 100000) := by
  exact
    packedTile16384 192899328 192932096 12 1718 13888 28 _ _ (953883 / 50000) (1907769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192932096 :
    ThetaLowerSegment 192932096 192964864 (19291533557907 / 100000) (9647385532829 / 50000) := by
  exact
    packedTile16384 192932096 192964864 12 1697 13889 28 _ _ (1907783 / 100000) (953893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192964864 :
    ThetaLowerSegment 192964864 192997632 (9647385532829 / 50000) (9649041503229 / 50000) := by
  exact
    packedTile16384 192964864 192997632 12 1736 13891 28 _ _ (9539 / 500) (1907803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell192997632 :
    ThetaLowerSegment 192997632 193030400 (9649041503229 / 50000) (1930135682043 / 10000) := by
  exact
    packedTile16384 192997632 193030400 12 1716 13892 28 _ _ (1907817 / 100000) (95391 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193030400 :
    ThetaLowerSegment 193030400 193063168 (1930135682043 / 10000) (2413080025343 / 12500) := by
  exact
    packedTile16384 193030400 193063168 12 1721 13893 28 _ _ (953917 / 50000) (1907837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193063168 :
    ThetaLowerSegment 193063168 193095936 (2413080025343 / 12500) (19307900720103 / 100000) := by
  exact
    packedTile16384 193063168 193095936 12 1709 13894 28 _ _ (1907851 / 100000) (953927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193095936 :
    ThetaLowerSegment 193095936 193128704 (19307900720103 / 100000) (19311140279967 / 100000) := by
  exact
    packedTile16384 193095936 193128704 12 1698 13895 28 _ _ (476967 / 25000) (1907871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193128704 :
    ThetaLowerSegment 193128704 193161472 (19311140279967 / 100000) (1207151007407 / 6250) := by
  exact
    packedTile16384 193128704 193161472 12 1717 13897 28 _ _ (381577 / 20000) (119243 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193161472 :
    ThetaLowerSegment 193161472 193194240 (1207151007407 / 6250) (9658859348437 / 50000) := by
  exact
    packedTile16384 193161472 193194240 12 1731 13898 28 _ _ (953951 / 50000) (381581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193194240 :
    ThetaLowerSegment 193194240 193227008 (9658859348437 / 50000) (19320944987903 / 100000) := by
  exact
    packedTile16384 193194240 193227008 12 1691 13899 28 _ _ (1907919 / 100000) (953961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193227008 :
    ThetaLowerSegment 193227008 193259776 (19320944987903 / 100000) (3864834643123 / 20000) := by
  exact
    packedTile16384 193227008 193259776 12 1692 13900 28 _ _ (59623 / 3125) (1907939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193259776 :
    ThetaLowerSegment 193259776 193292544 (3864834643123 / 20000) (4831862292729 / 25000) := by
  exact
    packedTile16384 193259776 193292544 12 1717 13901 28 _ _ (1907953 / 100000) (476989 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193292544 :
    ThetaLowerSegment 193292544 193325312 (4831862292729 / 25000) (604085697723 / 3125) := by
  exact
    packedTile16384 193292544 193325312 12 1726 13902 28 _ _ (190797 / 10000) (1907973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193325312 :
    ThetaLowerSegment 193325312 193358080 (604085697723 / 3125) (19333987813023 / 100000) := by
  exact
    packedTile16384 193325312 193358080 12 1701 13904 28 _ _ (1907987 / 100000) (190799 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193358080 :
    ThetaLowerSegment 193358080 193390848 (19333987813023 / 100000) (19337298199963 / 100000) := by
  exact
    packedTile16384 193358080 193390848 12 1735 13905 28 _ _ (477001 / 25000) (1908007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193390848 :
    ThetaLowerSegment 193390848 193423616 (19337298199963 / 100000) (19340496043159 / 100000) := by
  exact
    packedTile16384 193390848 193423616 12 1676 13906 28 _ _ (1908021 / 100000) (238503 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193423616 :
    ThetaLowerSegment 193423616 193456384 (19340496043159 / 100000) (19343745431873 / 100000) := by
  exact
    packedTile16384 193423616 193456384 12 1703 13907 28 _ _ (954019 / 50000) (1908041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193456384 :
    ThetaLowerSegment 193456384 193489152 (19343745431873 / 100000) (9673577563079 / 50000) := by
  exact
    packedTile16384 193456384 193489152 12 1787 13908 28 _ _ (381611 / 20000) (954029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193489152 :
    ThetaLowerSegment 193489152 193521920 (9673577563079 / 50000) (9675236631683 / 50000) := by
  exact
    packedTile16384 193489152 193521920 12 1739 13910 28 _ _ (238509 / 12500) (76323 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193521920 :
    ThetaLowerSegment 193521920 193554688 (9675236631683 / 50000) (19353753268357 / 100000) := by
  exact
    packedTile16384 193521920 193554688 12 1719 13911 28 _ _ (1908089 / 100000) (477023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193554688 :
    ThetaLowerSegment 193554688 193587456 (19353753268357 / 100000) (19357058107949 / 100000) := by
  exact
    packedTile16384 193554688 193587456 12 1732 13912 28 _ _ (954053 / 50000) (1908109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193587456 :
    ThetaLowerSegment 193587456 193620224 (19357058107949 / 100000) (19360322904691 / 100000) := by
  exact
    packedTile16384 193587456 193620224 12 1711 13913 28 _ _ (954061 / 50000) (3053 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193620224 :
    ThetaLowerSegment 193620224 193652992 (19360322904691 / 100000) (19363662147941 / 100000) := by
  exact
    packedTile16384 193620224 193652992 12 1750 13914 28 _ _ (1908139 / 100000) (954071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193652992 :
    ThetaLowerSegment 193652992 193685760 (19363662147941 / 100000) (3873390361777 / 20000) := by
  exact
    packedTile16384 193652992 193685760 12 1724 13915 28 _ _ (477039 / 25000) (1908159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193685760 :
    ThetaLowerSegment 193685760 193718528 (3873390361777 / 20000) (3874058222327 / 20000) := by
  exact
    packedTile16384 193685760 193718528 12 1750 13917 28 _ _ (1908173 / 100000) (119261 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193718528 :
    ThetaLowerSegment 193718528 193751296 (3874058222327 / 20000) (3874701282357 / 20000) := by
  exact
    packedTile16384 193718528 193751296 12 1685 13918 28 _ _ (190819 / 10000) (1908193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193751296 :
    ThetaLowerSegment 193751296 193784064 (3874701282357 / 20000) (4844191884387 / 25000) := by
  exact
    packedTile16384 193751296 193784064 12 1709 13919 28 _ _ (1908207 / 100000) (190821 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193784064 :
    ThetaLowerSegment 193784064 193816832 (4844191884387 / 25000) (4845030071779 / 25000) := by
  exact
    packedTile16384 193784064 193816832 12 1757 13920 28 _ _ (59632 / 3125) (1908227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193816832 :
    ThetaLowerSegment 193816832 193849600 (4845030071779 / 25000) (9691699322577 / 50000) := by
  exact
    packedTile16384 193816832 193849600 12 1718 13921 28 _ _ (1908241 / 100000) (477061 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193849600 :
    ThetaLowerSegment 193849600 193882368 (9691699322577 / 50000) (9693336607941 / 50000) := by
  exact
    packedTile16384 193849600 193882368 12 1716 13922 28 _ _ (954129 / 50000) (1908261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193882368 :
    ThetaLowerSegment 193882368 193915136 (9693336607941 / 50000) (19390003155757 / 100000) := by
  exact
    packedTile16384 193882368 193915136 12 1745 13924 28 _ _ (76331 / 4000) (954139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193915136 :
    ThetaLowerSegment 193915136 193947904 (19390003155757 / 100000) (19393304500917 / 100000) := by
  exact
    packedTile16384 193915136 193947904 12 1730 13925 28 _ _ (477073 / 25000) (381659 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193947904 :
    ThetaLowerSegment 193947904 193980672 (19393304500917 / 100000) (9698263817409 / 50000) := by
  exact
    packedTile16384 193947904 193980672 12 1689 13926 28 _ _ (1908309 / 100000) (238539 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell193980672 :
    ThetaLowerSegment 193980672 194013440 (9698263817409 / 50000) (9699908793559 / 50000) := by
  exact
    packedTile16384 193980672 194013440 12 1724 13927 28 _ _ (76333 / 4000) (238541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194013440 :
    ThetaLowerSegment 194013440 194046208 (9699908793559 / 50000) (9701553784363 / 50000) := by
  exact
    packedTile16384 194013440 194046208 12 1724 13928 28 _ _ (954171 / 50000) (381669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194046208 :
    ThetaLowerSegment 194046208 194078976 (9701553784363 / 50000) (9703187339667 / 50000) := by
  exact
    packedTile16384 194046208 194078976 12 1712 13930 28 _ _ (1908359 / 100000) (954181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194078976 :
    ThetaLowerSegment 194078976 194111744 (9703187339667 / 50000) (1940970670383 / 10000) := by
  exact
    packedTile16384 194078976 194111744 12 1746 13931 28 _ _ (238547 / 12500) (1908379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194111744 :
    ThetaLowerSegment 194111744 194144512 (1940970670383 / 10000) (9706464035607 / 50000) := by
  exact
    packedTile16384 194111744 194144512 12 1688 13932 28 _ _ (1908393 / 100000) (477099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194144512 :
    ThetaLowerSegment 194144512 194177280 (9706464035607 / 50000) (4854052157001 / 25000) := by
  exact
    packedTile16384 194144512 194177280 12 1719 13933 28 _ _ (190841 / 10000) (1908413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194177280 :
    ThetaLowerSegment 194177280 194210048 (4854052157001 / 25000) (3883895552691 / 20000) := by
  exact
    packedTile16384 194177280 194210048 12 1713 13934 28 _ _ (1908427 / 100000) (190843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194210048 :
    ThetaLowerSegment 194210048 194242816 (3883895552691 / 20000) (19422735477363 / 100000) := by
  exact
    packedTile16384 194210048 194242816 12 1707 13935 28 _ _ (477111 / 25000) (1908447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194242816 :
    ThetaLowerSegment 194242816 194275584 (19422735477363 / 100000) (19426004669343 / 100000) := by
  exact
    packedTile16384 194242816 194275584 12 1713 13937 28 _ _ (95423 / 5000) (1908463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194275584 :
    ThetaLowerSegment 194275584 194308352 (19426004669343 / 100000) (1942930824303 / 10000) := by
  exact
    packedTile16384 194275584 194308352 12 1731 13938 28 _ _ (1908477 / 100000) (11928 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194308352 :
    ThetaLowerSegment 194308352 194341120 (1942930824303 / 10000) (9716308785813 / 50000) := by
  exact
    packedTile16384 194308352 194341120 12 1734 13939 28 _ _ (954247 / 50000) (1908497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194341120 :
    ThetaLowerSegment 194341120 194373888 (9716308785813 / 50000) (19435886850969 / 100000) := by
  exact
    packedTile16384 194341120 194373888 12 1713 13940 28 _ _ (1908511 / 100000) (954257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194373888 :
    ThetaLowerSegment 194373888 194406656 (19435886850969 / 100000) (19439190512937 / 100000) := by
  exact
    packedTile16384 194373888 194406656 12 1731 13941 28 _ _ (119283 / 6250) (1908531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194406656 :
    ThetaLowerSegment 194406656 194439424 (19439190512937 / 100000) (19442572454677 / 100000) := by
  exact
    packedTile16384 194406656 194439424 12 1772 13942 28 _ _ (381709 / 20000) (477137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194439424 :
    ThetaLowerSegment 194439424 194472192 (19442572454677 / 100000) (3889159203179 / 20000) := by
  exact
    packedTile16384 194439424 194472192 12 1689 13944 28 _ _ (954281 / 50000) (381713 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194472192 :
    ThetaLowerSegment 194472192 194504960 (3889159203179 / 20000) (19449032964183 / 100000) := by
  exact
    packedTile16384 194472192 194504960 12 1696 13945 28 _ _ (954289 / 50000) (1908581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194504960 :
    ThetaLowerSegment 194504960 194537728 (19449032964183 / 100000) (4863074642557 / 25000) := by
  exact
    packedTile16384 194504960 194537728 12 1711 13946 28 _ _ (381719 / 20000) (954299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194537728 :
    ThetaLowerSegment 194537728 194570496 (4863074642557 / 25000) (486388627981 / 2500) := by
  exact
    packedTile16384 194537728 194570496 12 1701 13947 28 _ _ (477153 / 25000) (381723 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194570496 :
    ThetaLowerSegment 194570496 194603264 (486388627981 / 2500) (4864705081651 / 25000) := by
  exact
    packedTile16384 194570496 194603264 12 1716 13948 28 _ _ (1908629 / 100000) (238579 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194603264 :
    ThetaLowerSegment 194603264 194636032 (4864705081651 / 25000) (9731018197557 / 50000) := by
  exact
    packedTile16384 194603264 194636032 12 1685 13950 28 _ _ (954323 / 50000) (1908649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194636032 :
    ThetaLowerSegment 194636032 194668800 (9731018197557 / 50000) (4866332686863 / 25000) := by
  exact
    packedTile16384 194636032 194668800 12 1726 13951 28 _ _ (1908663 / 100000) (954333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194668800 :
    ThetaLowerSegment 194668800 194701568 (4866332686863 / 25000) (4867167734363 / 25000) := by
  exact
    packedTile16384 194668800 194701568 12 1750 13952 28 _ _ (47717 / 2500) (1908683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194701568 :
    ThetaLowerSegment 194701568 194734336 (4867167734363 / 25000) (4867973681249 / 25000) := by
  exact
    packedTile16384 194701568 194734336 12 1689 13953 28 _ _ (238587 / 12500) (1908699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194734336 :
    ThetaLowerSegment 194734336 194767104 (4867973681249 / 25000) (4868794427839 / 25000) := by
  exact
    packedTile16384 194734336 194767104 12 1720 13954 28 _ _ (1908713 / 100000) (477179 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194767104 :
    ThetaLowerSegment 194767104 194799872 (4868794427839 / 25000) (9739258040063 / 50000) := by
  exact
    packedTile16384 194767104 194799872 12 1749 13955 28 _ _ (190873 / 10000) (1908733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194799872 :
    ThetaLowerSegment 194799872 194832640 (9739258040063 / 50000) (779271735949 / 4000) := by
  exact
    packedTile16384 194799872 194832640 12 1717 13957 28 _ _ (1908747 / 100000) (1527 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194832640 :
    ThetaLowerSegment 194832640 194865408 (779271735949 / 4000) (3897015294561 / 20000) := by
  exact
    packedTile16384 194832640 194865408 12 1720 13958 28 _ _ (477191 / 25000) (1908767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194865408 :
    ThetaLowerSegment 194865408 194898176 (3897015294561 / 20000) (3897693674973 / 20000) := by
  exact
    packedTile16384 194865408 194898176 12 1777 13959 28 _ _ (95439 / 5000) (1908783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194898176 :
    ThetaLowerSegment 194898176 194930944 (3897693674973 / 20000) (9745838531311 / 50000) := by
  exact
    packedTile16384 194898176 194930944 12 1681 13960 28 _ _ (1908797 / 100000) (2386 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194930944 :
    ThetaLowerSegment 194930944 194963712 (9745838531311 / 50000) (9747533558143 / 50000) := by
  exact
    packedTile16384 194930944 194963712 12 1776 13961 28 _ _ (954407 / 50000) (1908817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194963712 :
    ThetaLowerSegment 194963712 194996480 (9747533558143 / 50000) (4874588530817 / 25000) := by
  exact
    packedTile16384 194963712 194996480 12 1722 13962 28 _ _ (1908831 / 100000) (954417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell194996480 :
    ThetaLowerSegment 194996480 195029248 (4874588530817 / 25000) (4875415539213 / 25000) := by
  exact
    packedTile16384 194996480 195029248 12 1733 13964 28 _ _ (119303 / 6250) (1908851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195029248 :
    ThetaLowerSegment 195029248 195062016 (4875415539213 / 25000) (9752459340271 / 50000) := by
  exact
    packedTile16384 195029248 195062016 12 1706 13965 28 _ _ (381773 / 20000) (477217 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195062016 :
    ThetaLowerSegment 195062016 195094784 (9752459340271 / 50000) (19508177140409 / 100000) := by
  exact
    packedTile16384 195062016 195094784 12 1707 13966 28 _ _ (1908881 / 100000) (477221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195094784 :
    ThetaLowerSegment 195094784 195127552 (19508177140409 / 100000) (19511437538193 / 100000) := by
  exact
    packedTile16384 195094784 195127552 12 1708 13967 28 _ _ (954449 / 50000) (1908901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195127552 :
    ThetaLowerSegment 195127552 195160320 (19511437538193 / 100000) (9757363299369 / 50000) := by
  exact
    packedTile16384 195127552 195160320 12 1723 13968 28 _ _ (381783 / 20000) (954459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195160320 :
    ThetaLowerSegment 195160320 195193088 (9757363299369 / 50000) (9759046977393 / 50000) := by
  exact
    packedTile16384 195160320 195193088 12 1764 13969 28 _ _ (477233 / 25000) (381787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195193088 :
    ThetaLowerSegment 195193088 195225856 (9759046977393 / 50000) (9760636176603 / 50000) := by
  exact
    packedTile16384 195193088 195225856 12 1665 13971 28 _ _ (477237 / 25000) (1908951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195225856 :
    ThetaLowerSegment 195225856 195258624 (9760636176603 / 50000) (19524488959231 / 100000) := by
  exact
    packedTile16384 195225856 195258624 12 1685 13972 28 _ _ (381793 / 20000) (238621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195258624 :
    ThetaLowerSegment 195258624 195291392 (19524488959231 / 100000) (19527745682523 / 100000) := by
  exact
    packedTile16384 195258624 195291392 12 1706 13973 28 _ _ (954491 / 50000) (381797 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195291392 :
    ThetaLowerSegment 195291392 195324160 (19527745682523 / 100000) (2441371724979 / 12500) := by
  exact
    packedTile16384 195291392 195324160 12 1691 13974 28 _ _ (1908999 / 100000) (954501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195324160 :
    ThetaLowerSegment 195324160 195356928 (2441371724979 / 12500) (1220886428483 / 6250) := by
  exact
    packedTile16384 195324160 195356928 12 1681 13975 28 _ _ (238627 / 12500) (1909019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195356928 :
    ThetaLowerSegment 195356928 195389696 (1220886428483 / 6250) (2442189264571 / 12500) := by
  exact
    packedTile16384 195356928 195389696 12 1745 13977 28 _ _ (238629 / 12500) (381807 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195389696 :
    ThetaLowerSegment 195389696 195422464 (2442189264571 / 12500) (19540769045113 / 100000) := by
  exact
    packedTile16384 195389696 195422464 12 1705 13978 28 _ _ (1909049 / 100000) (477263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195422464 :
    ThetaLowerSegment 195422464 195455232 (19540769045113 / 100000) (19544035457039 / 100000) := by
  exact
    packedTile16384 195422464 195455232 12 1711 13979 28 _ _ (954533 / 50000) (1909069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195455232 :
    ThetaLowerSegment 195455232 195488000 (19544035457039 / 100000) (9773626130947 / 50000) := by
  exact
    packedTile16384 195455232 195488000 12 1685 13980 28 _ _ (1909083 / 100000) (954543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195488000 :
    ThetaLowerSegment 195488000 195520768 (9773626130947 / 50000) (4887646387187 / 25000) := by
  exact
    packedTile16384 195488000 195520768 12 1746 13981 28 _ _ (1909099 / 100000) (954551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195520768 :
    ThetaLowerSegment 195520768 195553536 (4887646387187 / 25000) (977697470557 / 5000) := by
  exact
    packedTile16384 195520768 195553536 12 1762 13982 28 _ _ (477279 / 25000) (1909119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195553536 :
    ThetaLowerSegment 195553536 195586304 (977697470557 / 5000) (4889304461709 / 25000) := by
  exact
    packedTile16384 195553536 195586304 12 1712 13984 28 _ _ (1909133 / 100000) (119321 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195586304 :
    ThetaLowerSegment 195586304 195619072 (4889304461709 / 25000) (611264839273 / 3125) := by
  exact
    packedTile16384 195586304 195619072 12 1706 13985 28 _ _ (38183 / 2000) (1909153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195619072 :
    ThetaLowerSegment 195619072 195651840 (611264839273 / 3125) (2445472691531 / 12500) := by
  exact
    packedTile16384 195619072 195651840 12 1732 13986 28 _ _ (954583 / 50000) (1909169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195651840 :
    ThetaLowerSegment 195651840 195684608 (2445472691531 / 12500) (4891752967471 / 25000) := by
  exact
    packedTile16384 195651840 195684608 12 1692 13987 28 _ _ (1909183 / 100000) (954593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195684608 :
    ThetaLowerSegment 195684608 195717376 (4891752967471 / 25000) (4892553876871 / 25000) := by
  exact
    packedTile16384 195684608 195717376 12 1678 13988 28 _ _ (4773 / 250) (1909203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195717376 :
    ThetaLowerSegment 195717376 195750144 (4892553876871 / 25000) (489340729687 / 2500) := by
  exact
    packedTile16384 195717376 195750144 12 1788 13989 28 _ _ (1909217 / 100000) (95461 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195750144 :
    ThetaLowerSegment 195750144 195782912 (489340729687 / 2500) (9788401166363 / 50000) := by
  exact
    packedTile16384 195750144 195782912 12 1662 13991 28 _ _ (1909233 / 100000) (477309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195782912 :
    ThetaLowerSegment 195782912 195815680 (9788401166363 / 50000) (9790024028863 / 50000) := by
  exact
    packedTile16384 195782912 195815680 12 1700 13992 28 _ _ (7637 / 400) (1909253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195815680 :
    ThetaLowerSegment 195815680 195848448 (9790024028863 / 50000) (244791220377 / 1250) := by
  exact
    packedTile16384 195815680 195848448 12 1702 13993 28 _ _ (1909267 / 100000) (190927 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195848448 :
    ThetaLowerSegment 195848448 195881216 (244791220377 / 1250) (4896645876981 / 25000) := by
  exact
    packedTile16384 195848448 195881216 12 1721 13994 28 _ _ (477321 / 25000) (1909287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195881216 :
    ThetaLowerSegment 195881216 195913984 (4896645876981 / 25000) (1224367076989 / 6250) := by
  exact
    packedTile16384 195881216 195913984 12 1723 13995 28 _ _ (19093 / 1000) (1909303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195913984 :
    ThetaLowerSegment 195913984 195946752 (1224367076989 / 6250) (9796572900581 / 50000) := by
  exact
    packedTile16384 195913984 195946752 12 1714 13996 28 _ _ (1909317 / 100000) (47733 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195946752 :
    ThetaLowerSegment 195946752 195979520 (9796572900581 / 50000) (612389924656 / 3125) := by
  exact
    packedTile16384 195946752 195979520 12 1745 13998 28 _ _ (954667 / 50000) (1909337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell195979520 :
    ThetaLowerSegment 195979520 196012288 (612389924656 / 3125) (1959987241507 / 10000) := by
  exact
    packedTile16384 195979520 196012288 12 1778 13999 28 _ _ (1909351 / 100000) (954677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196012288 :
    ThetaLowerSegment 196012288 196045056 (1959987241507 / 10000) (9801551532017 / 50000) := by
  exact
    packedTile16384 196012288 196045056 12 1692 14000 28 _ _ (1909367 / 100000) (190937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196045056 :
    ThetaLowerSegment 196045056 196077824 (9801551532017 / 50000) (9803175463109 / 50000) := by
  exact
    packedTile16384 196045056 196077824 12 1701 14001 28 _ _ (238673 / 12500) (1909387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196077824 :
    ThetaLowerSegment 196077824 196110592 (9803175463109 / 50000) (3921925873547 / 20000) := by
  exact
    packedTile16384 196077824 196110592 12 1717 14002 28 _ _ (1909401 / 100000) (477351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196110592 :
    ThetaLowerSegment 196110592 196143360 (3921925873547 / 20000) (980642336769 / 5000) := by
  exact
    packedTile16384 196110592 196143360 12 1685 14003 28 _ _ (1909417 / 100000) (95471 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196143360 :
    ThetaLowerSegment 196143360 196176128 (980642336769 / 5000) (490401841971 / 2500) := by
  exact
    packedTile16384 196143360 196176128 12 1690 14005 28 _ _ (954717 / 50000) (1909437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196176128 :
    ThetaLowerSegment 196176128 196208896 (490401841971 / 2500) (9809711427947 / 50000) := by
  exact
    packedTile16384 196176128 196208896 12 1754 14006 28 _ _ (1909451 / 100000) (954727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196208896 :
    ThetaLowerSegment 196208896 196241664 (9809711427947 / 50000) (9811329702077 / 50000) := by
  exact
    packedTile16384 196208896 196241664 12 1695 14007 28 _ _ (477367 / 25000) (1909471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196241664 :
    ThetaLowerSegment 196241664 196274432 (9811329702077 / 50000) (9812922211733 / 50000) := by
  exact
    packedTile16384 196241664 196274432 12 1668 14008 28 _ _ (477371 / 25000) (1909487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196274432 :
    ThetaLowerSegment 196274432 196307200 (9812922211733 / 50000) (981452046407 / 5000) := by
  exact
    packedTile16384 196274432 196307200 12 1674 14009 28 _ _ (1909501 / 100000) (59672 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196307200 :
    ThetaLowerSegment 196307200 196339968 (981452046407 / 5000) (2454039230249 / 12500) := by
  exact
    packedTile16384 196307200 196339968 12 1714 14010 28 _ _ (954759 / 50000) (1909521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196339968 :
    ThetaLowerSegment 196339968 196372736 (2454039230249 / 12500) (613611251556 / 3125) := by
  exact
    packedTile16384 196339968 196372736 12 1700 14012 28 _ _ (954767 / 50000) (1909537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196372736 :
    ThetaLowerSegment 196372736 196405504 (613611251556 / 3125) (9819435605613 / 50000) := by
  exact
    packedTile16384 196372736 196405504 12 1734 14013 28 _ _ (1909551 / 100000) (954777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196405504 :
    ThetaLowerSegment 196405504 196438272 (9819435605613 / 50000) (9821044416653 / 50000) := by
  exact
    packedTile16384 196405504 196438272 12 1685 14014 28 _ _ (59674 / 3125) (1909571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196438272 :
    ThetaLowerSegment 196438272 196471040 (9821044416653 / 50000) (9822712438277 / 50000) := by
  exact
    packedTile16384 196438272 196471040 12 1747 14015 28 _ _ (119349 / 6250) (1909587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196471040 :
    ThetaLowerSegment 196471040 196503808 (9822712438277 / 50000) (157189690399 / 800) := by
  exact
    packedTile16384 196471040 196503808 12 1721 14016 28 _ _ (1909601 / 100000) (477401 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196503808 :
    ThetaLowerSegment 196503808 196536576 (157189690399 / 800) (19651999662071 / 100000) := by
  exact
    packedTile16384 196503808 196536576 12 1722 14017 28 _ _ (954809 / 50000) (1909621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196536576 :
    ThetaLowerSegment 196536576 196569344 (19651999662071 / 100000) (19655335792669 / 100000) := by
  exact
    packedTile16384 196536576 196569344 12 1747 14019 28 _ _ (954817 / 50000) (1909637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196569344 :
    ThetaLowerSegment 196569344 196602112 (19655335792669 / 100000) (19658578380067 / 100000) := by
  exact
    packedTile16384 196569344 196602112 12 1698 14020 28 _ _ (1909651 / 100000) (954827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196602112 :
    ThetaLowerSegment 196602112 196634880 (19658578380067 / 100000) (19661805718987 / 100000) := by
  exact
    packedTile16384 196602112 196634880 12 1690 14021 28 _ _ (477417 / 25000) (1909671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196634880 :
    ThetaLowerSegment 196634880 196667648 (19661805718987 / 100000) (19665073188311 / 100000) := by
  exact
    packedTile16384 196634880 196667648 12 1711 14022 28 _ _ (477421 / 25000) (1909687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196667648 :
    ThetaLowerSegment 196667648 196700416 (19665073188311 / 100000) (19668331138217 / 100000) := by
  exact
    packedTile16384 196667648 196700416 12 1706 14023 28 _ _ (1909701 / 100000) (238713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196700416 :
    ThetaLowerSegment 196700416 196733184 (19668331138217 / 100000) (19671638769793 / 100000) := by
  exact
    packedTile16384 196700416 196733184 12 1732 14024 28 _ _ (954859 / 50000) (1909721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196733184 :
    ThetaLowerSegment 196733184 196765952 (19671638769793 / 100000) (19674829935307 / 100000) := by
  exact
    packedTile16384 196733184 196765952 12 1671 14026 28 _ _ (954867 / 50000) (1909737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196765952 :
    ThetaLowerSegment 196765952 196798720 (19674829935307 / 100000) (2459768874037 / 12500) := by
  exact
    packedTile16384 196765952 196798720 12 1739 14027 28 _ _ (1909751 / 100000) (954877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196798720 :
    ThetaLowerSegment 196798720 196831488 (2459768874037 / 12500) (2460179951599 / 12500) := by
  exact
    packedTile16384 196798720 196831488 12 1722 14028 28 _ _ (238721 / 12500) (1909771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196831488 :
    ThetaLowerSegment 196831488 196864256 (2460179951599 / 12500) (615149727616 / 3125) := by
  exact
    packedTile16384 196831488 196864256 12 1755 14029 28 _ _ (238723 / 12500) (1909787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196864256 :
    ThetaLowerSegment 196864256 196897024 (615149727616 / 3125) (2461013337281 / 12500) := by
  exact
    packedTile16384 196864256 196897024 12 1736 14030 28 _ _ (1909801 / 100000) (477451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196897024 :
    ThetaLowerSegment 196897024 196929792 (2461013337281 / 12500) (9845664280607 / 50000) := by
  exact
    packedTile16384 196897024 196929792 12 1687 14032 28 _ _ (954909 / 50000) (1909821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196929792 :
    ThetaLowerSegment 196929792 196962560 (9845664280607 / 50000) (123091202922 / 625) := by
  exact
    packedTile16384 196929792 196962560 12 1709 14033 28 _ _ (954917 / 50000) (1909837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196962560 :
    ThetaLowerSegment 196962560 196995328 (123091202922 / 625) (19697860222581 / 100000) := by
  exact
    packedTile16384 196962560 196995328 12 1711 14034 28 _ _ (1909851 / 100000) (954927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell196995328 :
    ThetaLowerSegment 196995328 197028096 (19697860222581 / 100000) (3940237824501 / 20000) := by
  exact
    packedTile16384 196995328 197028096 12 1743 14035 28 _ _ (477467 / 25000) (1909871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197028096 :
    ThetaLowerSegment 197028096 197060864 (3940237824501 / 20000) (19704374809017 / 100000) := by
  exact
    packedTile16384 197028096 197060864 12 1668 14036 28 _ _ (477471 / 25000) (1909887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197060864 :
    ThetaLowerSegment 197060864 197093632 (19704374809017 / 100000) (19707659838737 / 100000) := by
  exact
    packedTile16384 197060864 197093632 12 1720 14037 28 _ _ (1909901 / 100000) (119369 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197093632 :
    ThetaLowerSegment 197093632 197126400 (19707659838737 / 100000) (492772619693 / 2500) := by
  exact
    packedTile16384 197093632 197126400 12 1699 14039 28 _ _ (1909917 / 100000) (11937 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197126400 :
    ThetaLowerSegment 197126400 197159168 (492772619693 / 2500) (2464269914407 / 12500) := by
  exact
    packedTile16384 197126400 197159168 12 1704 14040 28 _ _ (954967 / 50000) (1909937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197159168 :
    ThetaLowerSegment 197159168 197191936 (2464269914407 / 12500) (3943492324107 / 20000) := by
  exact
    packedTile16384 197159168 197191936 12 1729 14041 28 _ _ (1909951 / 100000) (954977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197191936 :
    ThetaLowerSegment 197191936 197224704 (3943492324107 / 20000) (19720700924567 / 100000) := by
  exact
    packedTile16384 197191936 197224704 12 1696 14042 28 _ _ (1909967 / 100000) (190997 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197224704 :
    ThetaLowerSegment 197224704 197257472 (19720700924567 / 100000) (3944801803371 / 20000) := by
  exact
    packedTile16384 197224704 197257472 12 1732 14043 28 _ _ (59687 / 3125) (1909987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197257472 :
    ThetaLowerSegment 197257472 197290240 (3944801803371 / 20000) (4931837402151 / 25000) := by
  exact
    packedTile16384 197257472 197290240 12 1749 14044 28 _ _ (1910001 / 100000) (477501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197290240 :
    ThetaLowerSegment 197290240 197323008 (4931837402151 / 25000) (1973063101781 / 10000) := by
  exact
    packedTile16384 197290240 197323008 12 1718 14046 28 _ _ (1910017 / 100000) (95501 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197323008 :
    ThetaLowerSegment 197323008 197355776 (1973063101781 / 10000) (1973391627629 / 10000) := by
  exact
    packedTile16384 197323008 197355776 12 1720 14047 28 _ _ (955017 / 50000) (1910037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197355776 :
    ThetaLowerSegment 197355776 197388544 (1973391627629 / 10000) (1973714426079 / 10000) := by
  exact
    packedTile16384 197355776 197388544 12 1690 14048 28 _ _ (38201 / 2000) (1910053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197388544 :
    ThetaLowerSegment 197388544 197421312 (1973714426079 / 10000) (19740374184087 / 100000) := by
  exact
    packedTile16384 197388544 197421312 12 1691 14049 28 _ _ (1910067 / 100000) (191007 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197421312 :
    ThetaLowerSegment 197421312 197454080 (19740374184087 / 100000) (19743680539491 / 100000) := by
  exact
    packedTile16384 197421312 197454080 12 1731 14050 28 _ _ (477521 / 25000) (1910087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197454080 :
    ThetaLowerSegment 197454080 197486848 (19743680539491 / 100000) (19746900968091 / 100000) := by
  exact
    packedTile16384 197454080 197486848 12 1686 14051 28 _ _ (19101 / 1000) (1910103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197486848 :
    ThetaLowerSegment 197486848 197519616 (19746900968091 / 100000) (9875073128437 / 50000) := by
  exact
    packedTile16384 197486848 197519616 12 1699 14053 28 _ _ (1910117 / 100000) (47753 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197519616 :
    ThetaLowerSegment 197519616 197552384 (9875073128437 / 50000) (4938347415677 / 25000) := by
  exact
    packedTile16384 197519616 197552384 12 1698 14054 28 _ _ (1910133 / 100000) (238767 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197552384 :
    ThetaLowerSegment 197552384 197585152 (4938347415677 / 25000) (617394784294 / 3125) := by
  exact
    packedTile16384 197552384 197585152 12 1698 14055 28 _ _ (38203 / 2000) (1910153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197585152 :
    ThetaLowerSegment 197585152 197617920 (617394784294 / 3125) (19759847908469 / 100000) := by
  exact
    packedTile16384 197585152 197617920 12 1683 14056 28 _ _ (1910167 / 100000) (191017 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197617920 :
    ThetaLowerSegment 197617920 197650688 (19759847908469 / 100000) (19763068477007 / 100000) := by
  exact
    packedTile16384 197617920 197650688 12 1686 14057 28 _ _ (1910183 / 100000) (955093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197650688 :
    ThetaLowerSegment 197650688 197683456 (19763068477007 / 100000) (19766394135207 / 100000) := by
  exact
    packedTile16384 197650688 197683456 12 1741 14058 28 _ _ (9551 / 500) (1910203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197683456 :
    ThetaLowerSegment 197683456 197716224 (19766394135207 / 100000) (19769612849167 / 100000) := by
  exact
    packedTile16384 197683456 197716224 12 1685 14059 28 _ _ (238777 / 12500) (1910219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197716224 :
    ThetaLowerSegment 197716224 197748992 (19769612849167 / 100000) (39545724311 / 200) := by
  exact
    packedTile16384 197716224 197748992 12 1701 14061 28 _ _ (1910233 / 100000) (477559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197748992 :
    ThetaLowerSegment 197748992 197781760 (39545724311 / 200) (4944033125447 / 25000) := by
  exact
    packedTile16384 197748992 197781760 12 1712 14062 28 _ _ (1910249 / 100000) (477563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197781760 :
    ThetaLowerSegment 197781760 197814528 (4944033125447 / 25000) (2472428702613 / 12500) := by
  exact
    packedTile16384 197781760 197814528 12 1726 14063 28 _ _ (955133 / 50000) (1910269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197814528 :
    ThetaLowerSegment 197814528 197847296 (2472428702613 / 12500) (19782679012287 / 100000) := by
  exact
    packedTile16384 197814528 197847296 12 1701 14064 28 _ _ (1910283 / 100000) (955143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197847296 :
    ThetaLowerSegment 197847296 197880064 (19782679012287 / 100000) (19785945623577 / 100000) := by
  exact
    packedTile16384 197847296 197880064 12 1710 14065 28 _ _ (1910299 / 100000) (955151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197880064 :
    ThetaLowerSegment 197880064 197912832 (19785945623577 / 100000) (19789172147301 / 100000) := by
  exact
    packedTile16384 197880064 197912832 12 1689 14066 28 _ _ (477579 / 25000) (1910319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197912832 :
    ThetaLowerSegment 197912832 197945600 (19789172147301 / 100000) (19792513317969 / 100000) := by
  exact
    packedTile16384 197912832 197945600 12 1749 14068 28 _ _ (477583 / 25000) (382067 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197945600 :
    ThetaLowerSegment 197945600 197978368 (19792513317969 / 100000) (3959161351929 / 20000) := by
  exact
    packedTile16384 197945600 197978368 12 1724 14069 28 _ _ (1910349 / 100000) (119397 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell197978368 :
    ThetaLowerSegment 197978368 198011136 (3959161351929 / 20000) (98995147727 / 500) := by
  exact
    packedTile16384 197978368 198011136 12 1687 14070 28 _ _ (382073 / 20000) (59699 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198011136 :
    ThetaLowerSegment 198011136 198043904 (98995147727 / 500) (4950566433127 / 25000) := by
  exact
    packedTile16384 198011136 198043904 12 1694 14071 28 _ _ (955191 / 50000) (382077 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198043904 :
    ThetaLowerSegment 198043904 198076672 (4950566433127 / 25000) (2475694429733 / 12500) := by
  exact
    packedTile16384 198043904 198076672 12 1722 14072 28 _ _ (955199 / 50000) (1910401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198076672 :
    ThetaLowerSegment 198076672 198109440 (2475694429733 / 12500) (619025337032 / 3125) := by
  exact
    packedTile16384 198076672 198109440 12 1704 14073 28 _ _ (382083 / 20000) (955209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198109440 :
    ThetaLowerSegment 198109440 198142208 (619025337032 / 3125) (619126231722 / 3125) := by
  exact
    packedTile16384 198109440 198142208 12 1690 14075 28 _ _ (59701 / 3125) (382087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198142208 :
    ThetaLowerSegment 198142208 198174976 (619126231722 / 3125) (123845449332 / 625) := by
  exact
    packedTile16384 198142208 198174976 12 1692 14076 28 _ _ (119403 / 6250) (1910451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198174976 :
    ThetaLowerSegment 198174976 198207744 (123845449332 / 625) (1981861520687 / 10000) := by
  exact
    packedTile16384 198174976 198207744 12 1750 14077 28 _ _ (382093 / 20000) (477617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198207744 :
    ThetaLowerSegment 198207744 198240512 (1981861520687 / 10000) (4955474353307 / 25000) := by
  exact
    packedTile16384 198207744 198240512 12 1718 14078 28 _ _ (1910481 / 100000) (477621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198240512 :
    ThetaLowerSegment 198240512 198273280 (4955474353307 / 25000) (2478143635103 / 12500) := by
  exact
    packedTile16384 198240512 198273280 12 1702 14079 28 _ _ (955249 / 50000) (1910501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198273280 :
    ThetaLowerSegment 198273280 198306048 (2478143635103 / 12500) (247855535087 / 1250) := by
  exact
    packedTile16384 198273280 198306048 12 1724 14080 28 _ _ (955257 / 50000) (1910517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198306048 :
    ThetaLowerSegment 198306048 198338816 (247855535087 / 1250) (9915870191733 / 50000) := by
  exact
    packedTile16384 198306048 198338816 12 1726 14082 28 _ _ (1910531 / 100000) (955267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198338816 :
    ThetaLowerSegment 198338816 198371584 (9915870191733 / 50000) (99175151727 / 500) := by
  exact
    packedTile16384 198338816 198371584 12 1722 14083 28 _ _ (1910547 / 100000) (38211 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198371584 :
    ThetaLowerSegment 198371584 198404352 (99175151727 / 500) (619947510519 / 3125) := by
  exact
    packedTile16384 198371584 198404352 12 1722 14084 28 _ _ (477641 / 25000) (1910567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198404352 :
    ThetaLowerSegment 198404352 198437120 (619947510519 / 3125) (2480205115581 / 12500) := by
  exact
    packedTile16384 198404352 198437120 12 1738 14085 28 _ _ (95529 / 5000) (1910583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198437120 :
    ThetaLowerSegment 198437120 198469888 (2480205115581 / 12500) (19844860280593 / 100000) := by
  exact
    packedTile16384 198437120 198469888 12 1685 14086 28 _ _ (1910597 / 100000) (9553 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198469888 :
    ThetaLowerSegment 198469888 198502656 (19844860280593 / 100000) (2481030497027 / 12500) := by
  exact
    packedTile16384 198469888 198502656 12 1771 14087 28 _ _ (1910613 / 100000) (238827 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198502656 :
    ThetaLowerSegment 198502656 198535424 (2481030497027 / 12500) (9925756532073 / 50000) := by
  exact
    packedTile16384 198502656 198535424 12 1711 14089 28 _ _ (191063 / 10000) (1910633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198535424 :
    ThetaLowerSegment 198535424 198568192 (9925756532073 / 50000) (9927401598279 / 50000) := by
  exact
    packedTile16384 198535424 198568192 12 1722 14090 28 _ _ (955323 / 50000) (1910649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198568192 :
    ThetaLowerSegment 198568192 198600960 (9927401598279 / 50000) (19858171695427 / 100000) := by
  exact
    packedTile16384 198568192 198600960 12 1763 14091 28 _ _ (1910663 / 100000) (955333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198600960 :
    ThetaLowerSegment 198600960 198633728 (19858171695427 / 100000) (4965360216799 / 25000) := by
  exact
    packedTile16384 198600960 198633728 12 1711 14092 28 _ _ (1910679 / 100000) (955341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198633728 :
    ThetaLowerSegment 198633728 198666496 (4965360216799 / 25000) (4966185159797 / 25000) := by
  exact
    packedTile16384 198633728 198666496 12 1727 14093 28 _ _ (238837 / 12500) (1910699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198666496 :
    ThetaLowerSegment 198666496 198699264 (4966185159797 / 25000) (993400971049 / 5000) := by
  exact
    packedTile16384 198666496 198699264 12 1716 14094 28 _ _ (238839 / 12500) (382143 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198699264 :
    ThetaLowerSegment 198699264 198732032 (993400971049 / 5000) (19871235177887 / 100000) := by
  exact
    packedTile16384 198699264 198732032 12 1683 14096 28 _ _ (1910729 / 100000) (477683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198732032 :
    ThetaLowerSegment 198732032 198764800 (19871235177887 / 100000) (19874494908857 / 100000) := by
  exact
    packedTile16384 198732032 198764800 12 1706 14097 28 _ _ (382149 / 20000) (477687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198764800 :
    ThetaLowerSegment 198764800 198797568 (19874494908857 / 100000) (19877790973307 / 100000) := by
  exact
    packedTile16384 198764800 198797568 12 1725 14098 28 _ _ (955381 / 50000) (382153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198797568 :
    ThetaLowerSegment 198797568 198830336 (19877790973307 / 100000) (19881071779133 / 100000) := by
  exact
    packedTile16384 198797568 198830336 12 1717 14099 28 _ _ (955389 / 50000) (1910781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198830336 :
    ThetaLowerSegment 198830336 198863104 (19881071779133 / 100000) (19884308665863 / 100000) := by
  exact
    packedTile16384 198830336 198863104 12 1694 14100 28 _ _ (382159 / 20000) (955399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198863104 :
    ThetaLowerSegment 198863104 198895872 (19884308665863 / 100000) (9943752726333 / 50000) := by
  exact
    packedTile16384 198863104 198895872 12 1673 14101 28 _ _ (1910811 / 100000) (955407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198895872 :
    ThetaLowerSegment 198895872 198928640 (9943752726333 / 50000) (9945399860069 / 50000) := by
  exact
    packedTile16384 198895872 198928640 12 1724 14103 28 _ _ (477707 / 25000) (1910831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198928640 :
    ThetaLowerSegment 198928640 198961408 (9945399860069 / 50000) (9947019300359 / 50000) := by
  exact
    packedTile16384 198928640 198961408 12 1695 14104 28 _ _ (477711 / 25000) (1910847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198961408 :
    ThetaLowerSegment 198961408 198994176 (9947019300359 / 50000) (19897304262167 / 100000) := by
  exact
    packedTile16384 198961408 198994176 12 1709 14105 28 _ _ (1910861 / 100000) (119429 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell198994176 :
    ThetaLowerSegment 198994176 199026944 (19897304262167 / 100000) (9950263955833 / 50000) := by
  exact
    packedTile16384 198994176 199026944 12 1687 14106 28 _ _ (1910877 / 100000) (11943 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199026944 :
    ThetaLowerSegment 199026944 199059712 (9950263955833 / 50000) (9951926433613 / 50000) := by
  exact
    packedTile16384 199026944 199059712 12 1740 14107 28 _ _ (955447 / 50000) (1910897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199059712 :
    ThetaLowerSegment 199059712 199092480 (9951926433613 / 50000) (9953548796203 / 50000) := by
  exact
    packedTile16384 199059712 199092480 12 1698 14108 28 _ _ (191091 / 10000) (1910913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199092480 :
    ThetaLowerSegment 199092480 199125248 (9953548796203 / 50000) (2488805452979 / 12500) := by
  exact
    packedTile16384 199092480 199125248 12 1751 14110 28 _ _ (955463 / 50000) (1910929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199125248 :
    ThetaLowerSegment 199125248 199158016 (2488805452979 / 12500) (3982735005689 / 20000) := by
  exact
    packedTile16384 199125248 199158016 12 1691 14111 28 _ _ (1910943 / 100000) (955473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199158016 :
    ThetaLowerSegment 199158016 199190784 (3982735005689 / 20000) (19916950412171 / 100000) := by
  exact
    packedTile16384 199158016 199190784 12 1714 14112 28 _ _ (1910959 / 100000) (955481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199190784 :
    ThetaLowerSegment 199190784 199223552 (19916950412171 / 100000) (19920166584779 / 100000) := by
  exact
    packedTile16384 199190784 199223552 12 1683 14113 28 _ _ (59718 / 3125) (1910979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199223552 :
    ThetaLowerSegment 199223552 199256320 (19920166584779 / 100000) (19923482155899 / 100000) := by
  exact
    packedTile16384 199223552 199256320 12 1735 14114 28 _ _ (119437 / 6250) (382199 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199256320 :
    ThetaLowerSegment 199256320 199289088 (19923482155899 / 100000) (9963425632383 / 50000) := by
  exact
    packedTile16384 199256320 199289088 12 1763 14115 28 _ _ (1911009 / 100000) (477753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199289088 :
    ThetaLowerSegment 199289088 199321856 (9963425632383 / 50000) (9965061469783 / 50000) := by
  exact
    packedTile16384 199289088 199321856 12 1712 14116 28 _ _ (76441 / 4000) (477757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199321856 :
    ThetaLowerSegment 199321856 199354624 (9965061469783 / 50000) (1245839195699 / 6250) := by
  exact
    packedTile16384 199321856 199354624 12 1729 14118 28 _ _ (955521 / 50000) (382209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199354624 :
    ThetaLowerSegment 199354624 199387392 (1245839195699 / 6250) (9968358031001 / 50000) := by
  exact
    packedTile16384 199354624 199387392 12 1721 14119 28 _ _ (955529 / 50000) (1911061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199387392 :
    ThetaLowerSegment 199387392 199420160 (9968358031001 / 50000) (19940050887877 / 100000) := by
  exact
    packedTile16384 199387392 199420160 12 1745 14120 28 _ _ (76443 / 4000) (955539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199420160 :
    ThetaLowerSegment 199420160 199452928 (19940050887877 / 100000) (19943383830581 / 100000) := by
  exact
    packedTile16384 199420160 199452928 12 1744 14121 28 _ _ (1911091 / 100000) (955547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199452928 :
    ThetaLowerSegment 199452928 199485696 (19943383830581 / 100000) (19946575379271 / 100000) := by
  exact
    packedTile16384 199452928 199485696 12 1670 14122 28 _ _ (1911107 / 100000) (191111 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199485696 :
    ThetaLowerSegment 199485696 199518464 (19946575379271 / 100000) (19949852956931 / 100000) := by
  exact
    packedTile16384 199485696 199518464 12 1715 14123 28 _ _ (477781 / 25000) (1911127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199518464 :
    ThetaLowerSegment 199518464 199551232 (19949852956931 / 100000) (19953151584571 / 100000) := by
  exact
    packedTile16384 199518464 199551232 12 1726 14125 28 _ _ (95557 / 5000) (1911143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199551232 :
    ThetaLowerSegment 199551232 199584000 (19953151584571 / 100000) (19956362328331 / 100000) := by
  exact
    packedTile16384 199551232 199584000 12 1680 14126 28 _ _ (1911157 / 100000) (47779 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199584000 :
    ThetaLowerSegment 199584000 199616768 (19956362328331 / 100000) (19959706881081 / 100000) := by
  exact
    packedTile16384 199584000 199616768 12 1750 14127 28 _ _ (1911173 / 100000) (238897 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199616768 :
    ThetaLowerSegment 199616768 199649536 (19959706881081 / 100000) (2495373071277 / 12500) := by
  exact
    packedTile16384 199616768 199649536 12 1715 14128 28 _ _ (1911189 / 100000) (238899 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199649536 :
    ThetaLowerSegment 199649536 199682304 (2495373071277 / 12500) (2495768690919 / 12500) := by
  exact
    packedTile16384 199649536 199682304 12 1656 14129 28 _ _ (955603 / 50000) (1911209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199682304 :
    ThetaLowerSegment 199682304 199715072 (2495768690919 / 12500) (9984723192651 / 50000) := by
  exact
    packedTile16384 199682304 199715072 12 1725 14130 28 _ _ (955611 / 50000) (76449 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199715072 :
    ThetaLowerSegment 199715072 199747840 (9984723192651 / 50000) (9986336278367 / 50000) := by
  exact
    packedTile16384 199715072 199747840 12 1688 14132 28 _ _ (1911239 / 100000) (955621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199747840 :
    ThetaLowerSegment 199747840 199780608 (9986336278367 / 50000) (19975935069019 / 100000) := by
  exact
    packedTile16384 199747840 199780608 12 1707 14133 28 _ _ (382251 / 20000) (955629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199780608 :
    ThetaLowerSegment 199780608 199813376 (19975935069019 / 100000) (19979201432867 / 100000) := by
  exact
    packedTile16384 199780608 199813376 12 1709 14134 28 _ _ (238909 / 12500) (76451 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199813376 :
    ThetaLowerSegment 199813376 199846144 (19979201432867 / 100000) (19982458267619 / 100000) := by
  exact
    packedTile16384 199813376 199846144 12 1704 14135 28 _ _ (238911 / 12500) (1911291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199846144 :
    ThetaLowerSegment 199846144 199878912 (19982458267619 / 100000) (19985703661811 / 100000) := by
  exact
    packedTile16384 199846144 199878912 12 1698 14136 28 _ _ (238913 / 12500) (1911307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199878912 :
    ThetaLowerSegment 199878912 199911680 (19985703661811 / 100000) (2498625086317 / 12500) := by
  exact
    packedTile16384 199878912 199911680 12 1725 14137 28 _ _ (1911321 / 100000) (477831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199911680 :
    ThetaLowerSegment 199911680 199944448 (2498625086317 / 12500) (4998081604229 / 25000) := by
  exact
    packedTile16384 199911680 199944448 12 1740 14139 28 _ _ (1911337 / 100000) (95567 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199944448 :
    ThetaLowerSegment 199944448 199977216 (4998081604229 / 25000) (9997815573991 / 50000) := by
  exact
    packedTile16384 199944448 199977216 12 1729 14140 28 _ _ (955677 / 50000) (1911357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell199977216 :
    ThetaLowerSegment 199977216 200009984 (9997815573991 / 50000) (1249934927697 / 6250) := by
  exact
    packedTile16384 199977216 200009984 12 1741 14141 28 _ _ (191137 / 10000) (1911373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200009984 :
    ThetaLowerSegment 200009984 200042752 (1249934927697 / 6250) (5000564473847 / 25000) := by
  exact
    packedTile16384 200009984 200042752 12 1726 14142 28 _ _ (955693 / 50000) (1911389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200042752 :
    ThetaLowerSegment 200042752 200075520 (5000564473847 / 25000) (5001405491167 / 25000) := by
  exact
    packedTile16384 200042752 200075520 12 1760 14143 28 _ _ (1911403 / 100000) (955703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200075520 :
    ThetaLowerSegment 200075520 200108288 (5001405491167 / 25000) (20008880934063 / 100000) := by
  exact
    packedTile16384 200075520 200108288 12 1705 14144 28 _ _ (1911419 / 100000) (955711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200108288 :
    ThetaLowerSegment 200108288 200141056 (20008880934063 / 100000) (2501517969201 / 12500) := by
  exact
    packedTile16384 200108288 200141056 12 1707 14145 28 _ _ (382287 / 20000) (955719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200141056 :
    ThetaLowerSegment 200141056 200173824 (2501517969201 / 12500) (2501939444367 / 12500) := by
  exact
    packedTile16384 200141056 200173824 12 1764 14147 28 _ _ (477863 / 25000) (382291 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200173824 :
    ThetaLowerSegment 200173824 200206592 (2501939444367 / 12500) (1251175443927 / 6250) := by
  exact
    packedTile16384 200173824 200206592 12 1722 14148 28 _ _ (477867 / 25000) (1911471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200206592 :
    ThetaLowerSegment 200206592 200239360 (1251175443927 / 6250) (10011087569701 / 50000) := by
  exact
    packedTile16384 200206592 200239360 12 1762 14149 28 _ _ (382297 / 20000) (59734 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200239360 :
    ThetaLowerSegment 200239360 200272128 (10011087569701 / 50000) (1251592149383 / 6250) := by
  exact
    packedTile16384 200239360 200272128 12 1726 14150 28 _ _ (1911501 / 100000) (119469 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200272128 :
    ThetaLowerSegment 200272128 200304896 (1251592149383 / 6250) (20028710588409 / 100000) := by
  exact
    packedTile16384 200272128 200304896 12 1693 14151 28 _ _ (1911517 / 100000) (11947 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200304896 :
    ThetaLowerSegment 200304896 200337664 (20028710588409 / 100000) (801278331387 / 4000) := by
  exact
    packedTile16384 200304896 200337664 12 1699 14152 28 _ _ (955767 / 50000) (1911537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200337664 :
    ThetaLowerSegment 200337664 200370432 (801278331387 / 4000) (160281189293 / 800) := by
  exact
    packedTile16384 200337664 200370432 12 1669 14154 28 _ _ (38231 / 2000) (1911553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200370432 :
    ThetaLowerSegment 200370432 200403200 (160281189293 / 800) (20038342888411 / 100000) := by
  exact
    packedTile16384 200370432 200403200 12 1671 14155 28 _ _ (955783 / 50000) (1911569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200403200 :
    ThetaLowerSegment 200403200 200435968 (20038342888411 / 100000) (20041615518507 / 100000) := by
  exact
    packedTile16384 200403200 200435968 12 1712 14156 28 _ _ (1911583 / 100000) (955793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200435968 :
    ThetaLowerSegment 200435968 200468736 (20041615518507 / 100000) (20044846120817 / 100000) := by
  exact
    packedTile16384 200435968 200468736 12 1690 14157 28 _ _ (1911599 / 100000) (955801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200468736 :
    ThetaLowerSegment 200468736 200501504 (20044846120817 / 100000) (20048179977377 / 100000) := by
  exact
    packedTile16384 200468736 200501504 12 1744 14158 28 _ _ (382323 / 20000) (955809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200501504 :
    ThetaLowerSegment 200501504 200534272 (20048179977377 / 100000) (4010298949453 / 20000) := by
  exact
    packedTile16384 200501504 200534272 12 1734 14159 28 _ _ (119477 / 6250) (382327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200534272 :
    ThetaLowerSegment 200534272 200567040 (4010298949453 / 20000) (20054788516769 / 100000) := by
  exact
    packedTile16384 200534272 200567040 12 1723 14161 28 _ _ (59739 / 3125) (1911651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200567040 :
    ThetaLowerSegment 200567040 200599808 (20054788516769 / 100000) (20058118635457 / 100000) := by
  exact
    packedTile16384 200567040 200599808 12 1742 14162 28 _ _ (119479 / 6250) (1911667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200599808 :
    ThetaLowerSegment 200599808 200632576 (20058118635457 / 100000) (5015341645369 / 25000) := by
  exact
    packedTile16384 200599808 200632576 12 1699 14163 28 _ _ (1911681 / 100000) (477921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200632576 :
    ThetaLowerSegment 200632576 200665344 (5015341645369 / 25000) (2508077058297 / 12500) := by
  exact
    packedTile16384 200632576 200665344 12 1700 14164 28 _ _ (1911697 / 100000) (19117 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200665344 :
    ThetaLowerSegment 200665344 200698112 (2508077058297 / 12500) (20067914171301 / 100000) := by
  exact
    packedTile16384 200665344 200698112 12 1725 14165 28 _ _ (1911713 / 100000) (477929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200698112 :
    ThetaLowerSegment 200698112 200730880 (20067914171301 / 100000) (20071169847491 / 100000) := by
  exact
    packedTile16384 200698112 200730880 12 1703 14166 28 _ _ (191173 / 10000) (1911733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200730880 :
    ThetaLowerSegment 200730880 200763648 (20071169847491 / 100000) (802977098507 / 4000) := by
  exact
    packedTile16384 200730880 200763648 12 1704 14167 28 _ _ (955873 / 50000) (1911749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200763648 :
    ThetaLowerSegment 200763648 200796416 (802977098507 / 4000) (20077702310981 / 100000) := by
  exact
    packedTile16384 200763648 200796416 12 1713 14169 28 _ _ (955881 / 50000) (382353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200796416 :
    ThetaLowerSegment 200796416 200829184 (20077702310981 / 100000) (10040509623773 / 50000) := by
  exact
    packedTile16384 200796416 200829184 12 1735 14170 28 _ _ (1911779 / 100000) (955891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200829184 :
    ThetaLowerSegment 200829184 200861952 (10040509623773 / 50000) (20084267387251 / 100000) := by
  exact
    packedTile16384 200829184 200861952 12 1699 14171 28 _ _ (382359 / 20000) (955899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200861952 :
    ThetaLowerSegment 200861952 200894720 (20084267387251 / 100000) (10043736747149 / 50000) := by
  exact
    packedTile16384 200861952 200894720 12 1677 14172 28 _ _ (1911811 / 100000) (955907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200894720 :
    ThetaLowerSegment 200894720 200927488 (10043736747149 / 50000) (10045397169767 / 50000) := by
  exact
    packedTile16384 200894720 200927488 12 1737 14173 28 _ _ (477957 / 25000) (1911831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200927488 :
    ThetaLowerSegment 200927488 200960256 (10045397169767 / 50000) (10047009810181 / 50000) := by
  exact
    packedTile16384 200927488 200960256 12 1687 14174 28 _ _ (477961 / 25000) (1911847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200960256 :
    ThetaLowerSegment 200960256 200993024 (10047009810181 / 50000) (10048653053851 / 50000) := by
  exact
    packedTile16384 200960256 200993024 12 1719 14176 28 _ _ (95593 / 5000) (1911863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell200993024 :
    ThetaLowerSegment 200993024 201025792 (10048653053851 / 50000) (10050297268071 / 50000) := by
  exact
    packedTile16384 200993024 201025792 12 1720 14177 28 _ _ (1911877 / 100000) (47797 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201025792 :
    ThetaLowerSegment 201025792 201058560 (10050297268071 / 50000) (20103858137493 / 100000) := by
  exact
    packedTile16384 201025792 201058560 12 1707 14178 28 _ _ (1911893 / 100000) (238987 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201058560 :
    ThetaLowerSegment 201058560 201091328 (20103858137493 / 100000) (10053593385531 / 50000) := by
  exact
    packedTile16384 201058560 201091328 12 1741 14179 28 _ _ (1911909 / 100000) (238989 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201091328 :
    ThetaLowerSegment 201091328 201124096 (10053593385531 / 50000) (10055256760281 / 50000) := by
  exact
    packedTile16384 201091328 201124096 12 1740 14180 28 _ _ (76477 / 4000) (238991 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201124096 :
    ThetaLowerSegment 201124096 201156864 (10055256760281 / 50000) (10056887646807 / 50000) := by
  exact
    packedTile16384 201124096 201156864 12 1706 14181 28 _ _ (955971 / 50000) (382389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201156864 :
    ThetaLowerSegment 201156864 201189632 (10056887646807 / 50000) (10058539578519 / 50000) := by
  exact
    packedTile16384 201156864 201189632 12 1728 14182 28 _ _ (955979 / 50000) (1911961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201189632 :
    ThetaLowerSegment 201189632 201222400 (10058539578519 / 50000) (503008381219 / 2500) := by
  exact
    packedTile16384 201189632 201222400 12 1703 14184 28 _ _ (955987 / 50000) (1911977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201222400 :
    ThetaLowerSegment 201222400 201255168 (503008381219 / 2500) (2515447248187 / 12500) := by
  exact
    packedTile16384 201222400 201255168 12 1696 14185 28 _ _ (1911991 / 100000) (955997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201255168 :
    ThetaLowerSegment 201255168 201287936 (2515447248187 / 12500) (20126872373557 / 100000) := by
  exact
    packedTile16384 201255168 201287936 12 1723 14186 28 _ _ (1912007 / 100000) (191201 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201287936 :
    ThetaLowerSegment 201287936 201320704 (20126872373557 / 100000) (20130092220289 / 100000) := by
  exact
    packedTile16384 201287936 201320704 12 1684 14187 28 _ _ (1912023 / 100000) (956013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201320704 :
    ThetaLowerSegment 201320704 201353472 (20130092220289 / 100000) (5033347621891 / 25000) := by
  exact
    packedTile16384 201320704 201353472 12 1725 14188 28 _ _ (1912039 / 100000) (956021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201353472 :
    ThetaLowerSegment 201353472 201386240 (5033347621891 / 25000) (5034177932209 / 25000) := by
  exact
    packedTile16384 201353472 201386240 12 1737 14189 28 _ _ (239007 / 12500) (1912059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201386240 :
    ThetaLowerSegment 201386240 201419008 (5034177932209 / 25000) (1007000215841 / 5000) := by
  exact
    packedTile16384 201386240 201419008 12 1722 14191 28 _ _ (239009 / 12500) (76483 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201419008 :
    ThetaLowerSegment 201419008 201451776 (1007000215841 / 5000) (1007162743321 / 5000) := by
  exact
    packedTile16384 201419008 201451776 12 1700 14192 28 _ _ (239011 / 12500) (1912091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201451776 :
    ThetaLowerSegment 201451776 201484544 (1007162743321 / 5000) (4029311414351 / 20000) := by
  exact
    packedTile16384 201451776 201484544 12 1727 14193 28 _ _ (382421 / 20000) (478027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201484544 :
    ThetaLowerSegment 201484544 201517312 (4029311414351 / 20000) (20149719719889 / 100000) := by
  exact
    packedTile16384 201484544 201517312 12 1654 14194 28 _ _ (1912121 / 100000) (478031 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201517312 :
    ThetaLowerSegment 201517312 201550080 (20149719719889 / 100000) (20152993298433 / 100000) := by
  exact
    packedTile16384 201517312 201550080 12 1712 14195 28 _ _ (1912137 / 100000) (95607 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201550080 :
    ThetaLowerSegment 201550080 201582848 (20152993298433 / 100000) (503905095083 / 2500) := by
  exact
    packedTile16384 201550080 201582848 12 1679 14196 28 _ _ (1912153 / 100000) (478039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201582848 :
    ThetaLowerSegment 201582848 201615616 (503905095083 / 2500) (1007978652343 / 5000) := by
  exact
    packedTile16384 201582848 201615616 12 1762 14197 28 _ _ (191217 / 10000) (1912173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201615616 :
    ThetaLowerSegment 201615616 201648384 (1007978652343 / 5000) (5040707852951 / 25000) := by
  exact
    packedTile16384 201615616 201648384 12 1704 14199 28 _ _ (956093 / 50000) (1912189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201648384 :
    ThetaLowerSegment 201648384 201681152 (5040707852951 / 25000) (10083042033703 / 50000) := by
  exact
    packedTile16384 201648384 201681152 12 1701 14200 28 _ _ (956101 / 50000) (382441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201681152 :
    ThetaLowerSegment 201681152 201713920 (10083042033703 / 50000) (10084680804529 / 50000) := by
  exact
    packedTile16384 201681152 201713920 12 1714 14201 28 _ _ (956109 / 50000) (1912221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201713920 :
    ThetaLowerSegment 201713920 201746688 (10084680804529 / 50000) (20172675512313 / 100000) := by
  exact
    packedTile16384 201713920 201746688 12 1733 14202 28 _ _ (382447 / 20000) (956119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201746688 :
    ThetaLowerSegment 201746688 201779456 (20172675512313 / 100000) (252199485591 / 1250) := by
  exact
    packedTile16384 201746688 201779456 12 1717 14203 28 _ _ (1912251 / 100000) (956127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201779456 :
    ThetaLowerSegment 201779456 201812224 (252199485591 / 1250) (20179203964379 / 100000) := by
  exact
    packedTile16384 201779456 201812224 12 1697 14204 28 _ _ (1912267 / 100000) (191227 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201812224 :
    ThetaLowerSegment 201812224 201844992 (20179203964379 / 100000) (10091255150843 / 50000) := by
  exact
    packedTile16384 201812224 201844992 12 1729 14206 28 _ _ (1912283 / 100000) (956143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201844992 :
    ThetaLowerSegment 201844992 201877760 (10091255150843 / 50000) (10092893035793 / 50000) := by
  exact
    packedTile16384 201844992 201877760 12 1713 14207 28 _ _ (19123 / 1000) (1912303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201877760 :
    ThetaLowerSegment 201877760 201910528 (10092893035793 / 50000) (10094554838397 / 50000) := by
  exact
    packedTile16384 201877760 201910528 12 1738 14208 28 _ _ (478079 / 25000) (1912319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201910528 :
    ThetaLowerSegment 201910528 201943296 (10094554838397 / 50000) (10096204224747 / 50000) := by
  exact
    packedTile16384 201910528 201943296 12 1725 14209 28 _ _ (478083 / 25000) (382467 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201943296 :
    ThetaLowerSegment 201943296 201976064 (10096204224747 / 50000) (10097888047161 / 50000) := by
  exact
    packedTile16384 201943296 201976064 12 1761 14210 28 _ _ (478087 / 25000) (1912351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell201976064 :
    ThetaLowerSegment 201976064 202008832 (10097888047161 / 50000) (10099503038559 / 50000) := by
  exact
    packedTile16384 201976064 202008832 12 1689 14211 28 _ _ (478091 / 25000) (1912367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202008832 :
    ThetaLowerSegment 202008832 202041600 (10099503038559 / 50000) (20202274336247 / 100000) := by
  exact
    packedTile16384 202008832 202041600 12 1709 14212 28 _ _ (1912381 / 100000) (59762 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202041600 :
    ThetaLowerSegment 202041600 202074368 (20202274336247 / 100000) (10102777048551 / 50000) := by
  exact
    packedTile16384 202041600 202074368 12 1715 14214 28 _ _ (1912397 / 100000) (4781 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202074368 :
    ThetaLowerSegment 202074368 202107136 (10102777048551 / 50000) (4041757597497 / 20000) := by
  exact
    packedTile16384 202074368 202107136 12 1691 14215 28 _ _ (1912413 / 100000) (59763 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202107136 :
    ThetaLowerSegment 202107136 202139904 (4041757597497 / 20000) (2021204867893 / 10000) := by
  exact
    packedTile16384 202107136 202139904 12 1705 14216 28 _ _ (1912429 / 100000) (119527 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202139904 :
    ThetaLowerSegment 202139904 202172672 (2021204867893 / 10000) (10107674780363 / 50000) := by
  exact
    packedTile16384 202139904 202172672 12 1726 14217 28 _ _ (956223 / 50000) (1912449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202172672 :
    ThetaLowerSegment 202172672 202205440 (10107674780363 / 50000) (2527323897977 / 12500) := by
  exact
    packedTile16384 202172672 202205440 12 1695 14218 28 _ _ (956231 / 50000) (382493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202205440 :
    ThetaLowerSegment 202205440 202238208 (2527323897977 / 12500) (10110929804359 / 50000) := by
  exact
    packedTile16384 202205440 202238208 12 1709 14219 28 _ _ (956239 / 50000) (1912481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202238208 :
    ThetaLowerSegment 202238208 202270976 (10110929804359 / 50000) (1264071699119 / 6250) := by
  exact
    packedTile16384 202238208 202270976 12 1719 14221 28 _ _ (956247 / 50000) (1912497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202270976 :
    ThetaLowerSegment 202270976 202303744 (1264071699119 / 6250) (2528555544143 / 12500) := by
  exact
    packedTile16384 202270976 202303744 12 1724 14222 28 _ _ (191251 / 10000) (1912513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202303744 :
    ThetaLowerSegment 202303744 202336512 (2528555544143 / 12500) (10115861212211 / 50000) := by
  exact
    packedTile16384 202303744 202336512 12 1714 14223 28 _ _ (1912527 / 100000) (191253 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202336512 :
    ThetaLowerSegment 202336512 202369280 (10115861212211 / 50000) (809400556437 / 4000) := by
  exact
    packedTile16384 202336512 202369280 12 1721 14224 28 _ _ (1912543 / 100000) (956273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202369280 :
    ThetaLowerSegment 202369280 202402048 (809400556437 / 4000) (10119150799923 / 50000) := by
  exact
    packedTile16384 202369280 202402048 12 1719 14225 28 _ _ (1912559 / 100000) (956281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202402048 :
    ThetaLowerSegment 202402048 202434816 (10119150799923 / 50000) (20241589316271 / 100000) := by
  exact
    packedTile16384 202402048 202434816 12 1719 14226 28 _ _ (76503 / 4000) (956289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202434816 :
    ThetaLowerSegment 202434816 202467584 (20241589316271 / 100000) (4048958198721 / 20000) := by
  exact
    packedTile16384 202434816 202467584 12 1674 14227 28 _ _ (1912591 / 100000) (956297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202467584 :
    ThetaLowerSegment 202467584 202500352 (4048958198721 / 20000) (20248063465893 / 100000) := by
  exact
    packedTile16384 202467584 202500352 12 1711 14229 28 _ _ (59769 / 3125) (1912611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202500352 :
    ThetaLowerSegment 202500352 202533120 (20248063465893 / 100000) (20251299625701 / 100000) := by
  exact
    packedTile16384 202500352 202533120 12 1692 14230 28 _ _ (119539 / 6250) (1912627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202533120 :
    ThetaLowerSegment 202533120 202565888 (20251299625701 / 100000) (20254537725221 / 100000) := by
  exact
    packedTile16384 202533120 202565888 12 1693 14231 28 _ _ (11954 / 625) (1912643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202565888 :
    ThetaLowerSegment 202565888 202598656 (20254537725221 / 100000) (20257879135253 / 100000) := by
  exact
    packedTile16384 202565888 202598656 12 1747 14232 28 _ _ (119541 / 6250) (1912659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202598656 :
    ThetaLowerSegment 202598656 202631424 (20257879135253 / 100000) (20261073297493 / 100000) := by
  exact
    packedTile16384 202598656 202631424 12 1670 14233 28 _ _ (59771 / 3125) (76507 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202631424 :
    ThetaLowerSegment 202631424 202664192 (20261073297493 / 100000) (810575978477 / 4000) := by
  exact
    packedTile16384 202631424 202664192 12 1739 14234 28 _ _ (119543 / 6250) (1912691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202664192 :
    ThetaLowerSegment 202664192 202696960 (810575978477 / 4000) (2026765297313 / 10000) := by
  exact
    packedTile16384 202664192 202696960 12 1701 14236 28 _ _ (382541 / 20000) (478177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202696960 :
    ThetaLowerSegment 202696960 202729728 (2026765297313 / 10000) (5067717542463 / 25000) := by
  exact
    packedTile16384 202696960 202729728 12 1682 14237 28 _ _ (1912721 / 100000) (478181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202729728 :
    ThetaLowerSegment 202729728 202762496 (5067717542463 / 25000) (20274054876957 / 100000) := by
  exact
    packedTile16384 202729728 202762496 12 1665 14238 28 _ _ (1912737 / 100000) (95637 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202762496 :
    ThetaLowerSegment 202762496 202795264 (20274054876957 / 100000) (4055475083233 / 20000) := by
  exact
    packedTile16384 202762496 202795264 12 1736 14239 28 _ _ (1912753 / 100000) (478189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202795264 :
    ThetaLowerSegment 202795264 202828032 (4055475083233 / 20000) (4056152203459 / 20000) := by
  exact
    packedTile16384 202795264 202828032 12 1770 14240 28 _ _ (1912769 / 100000) (478193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202828032 :
    ThetaLowerSegment 202828032 202860800 (4056152203459 / 20000) (2028397258331 / 10000) := by
  exact
    packedTile16384 202828032 202860800 12 1679 14241 28 _ _ (382557 / 20000) (478197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202860800 :
    ThetaLowerSegment 202860800 202893568 (2028397258331 / 10000) (1014366477541 / 5000) := by
  exact
    packedTile16384 202860800 202893568 12 1755 14242 28 _ _ (956401 / 50000) (382561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202893568 :
    ThetaLowerSegment 202893568 202926336 (1014366477541 / 5000) (5072633858447 / 25000) := by
  exact
    packedTile16384 202893568 202926336 12 1676 14244 28 _ _ (956409 / 50000) (1912821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202926336 :
    ThetaLowerSegment 202926336 202959104 (5072633858447 / 25000) (2029381211843 / 10000) := by
  exact
    packedTile16384 202926336 202959104 12 1713 14245 28 _ _ (956417 / 50000) (1912837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202959104 :
    ThetaLowerSegment 202959104 202991872 (2029381211843 / 10000) (253713227811 / 1250) := by
  exact
    packedTile16384 202959104 202991872 12 1697 14246 28 _ _ (38257 / 2000) (1912853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell202991872 :
    ThetaLowerSegment 202991872 203024640 (253713227811 / 1250) (5075086132167 / 25000) := by
  exact
    packedTile16384 202991872 203024640 12 1718 14247 28 _ _ (956433 / 50000) (1912869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203024640 :
    ThetaLowerSegment 203024640 203057408 (5075086132167 / 25000) (2030363659859 / 10000) := by
  exact
    packedTile16384 203024640 203057408 12 1721 14248 28 _ _ (956441 / 50000) (382577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203057408 :
    ThetaLowerSegment 203057408 203090176 (2030363659859 / 10000) (507675321589 / 2500) := by
  exact
    packedTile16384 203057408 203090176 12 1765 14249 28 _ _ (956449 / 50000) (1912901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203090176 :
    ThetaLowerSegment 203090176 203122944 (507675321589 / 2500) (4062050285731 / 20000) := by
  exact
    packedTile16384 203090176 203122944 12 1693 14250 28 _ _ (382583 / 20000) (956459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203122944 :
    ThetaLowerSegment 203122944 203155712 (4062050285731 / 20000) (10156764139729 / 50000) := by
  exact
    packedTile16384 203122944 203155712 12 1713 14252 28 _ _ (1912931 / 100000) (956467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203155712 :
    ThetaLowerSegment 203155712 203188480 (10156764139729 / 50000) (5079211332389 / 25000) := by
  exact
    packedTile16384 203155712 203188480 12 1734 14253 28 _ _ (1912947 / 100000) (38259 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203188480 :
    ThetaLowerSegment 203188480 203221248 (5079211332389 / 25000) (20320114583323 / 100000) := by
  exact
    packedTile16384 203188480 203221248 12 1709 14254 28 _ _ (1912963 / 100000) (956483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203221248 :
    ThetaLowerSegment 203221248 203254016 (20320114583323 / 100000) (4064672564333 / 20000) := by
  exact
    packedTile16384 203221248 203254016 12 1698 14255 28 _ _ (1912979 / 100000) (956491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203254016 :
    ThetaLowerSegment 203254016 203286784 (4064672564333 / 20000) (1016331223907 / 5000) := by
  exact
    packedTile16384 203254016 203286784 12 1705 14256 28 _ _ (382599 / 20000) (956499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203286784 :
    ThetaLowerSegment 203286784 203319552 (1016331223907 / 5000) (20329893813939 / 100000) := by
  exact
    packedTile16384 203286784 203319552 12 1709 14257 28 _ _ (1913011 / 100000) (956507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203319552 :
    ThetaLowerSegment 203319552 203352320 (20329893813939 / 100000) (10166612196973 / 50000) := by
  exact
    packedTile16384 203319552 203352320 12 1741 14259 28 _ _ (1913027 / 100000) (191303 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203352320 :
    ThetaLowerSegment 203352320 203385088 (10166612196973 / 50000) (10168266023511 / 50000) := by
  exact
    packedTile16384 203352320 203385088 12 1729 14260 28 _ _ (478261 / 25000) (1913047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203385088 :
    ThetaLowerSegment 203385088 203417856 (10168266023511 / 50000) (10169936124891 / 50000) := by
  exact
    packedTile16384 203385088 203417856 12 1746 14261 28 _ _ (95653 / 5000) (1913063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203417856 :
    ThetaLowerSegment 203417856 203450624 (10169936124891 / 50000) (406862221749 / 2000) := by
  exact
    packedTile16384 203417856 203450624 12 1693 14262 28 _ _ (478269 / 25000) (1913079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203450624 :
    ThetaLowerSegment 203450624 203483392 (406862221749 / 2000) (10173166367189 / 50000) := by
  exact
    packedTile16384 203450624 203483392 12 1684 14263 28 _ _ (478273 / 25000) (382619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203483392 :
    ThetaLowerSegment 203483392 203516160 (10173166367189 / 50000) (10174823118717 / 50000) := by
  exact
    packedTile16384 203483392 203516160 12 1732 14264 28 _ _ (478277 / 25000) (1913111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203516160 :
    ThetaLowerSegment 203516160 203548928 (10174823118717 / 50000) (10176455013489 / 50000) := by
  exact
    packedTile16384 203516160 203548928 12 1706 14265 28 _ _ (478281 / 25000) (1913127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203548928 :
    ThetaLowerSegment 203548928 203581696 (10176455013489 / 50000) (10178042919689 / 50000) := by
  exact
    packedTile16384 203548928 203581696 12 1660 14267 28 _ _ (95657 / 5000) (1913143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203581696 :
    ThetaLowerSegment 203581696 203614464 (10178042919689 / 50000) (407185310093 / 2000) := by
  exact
    packedTile16384 203581696 203614464 12 1662 14268 28 _ _ (478289 / 25000) (1913159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203614464 :
    ThetaLowerSegment 203614464 203647232 (407185310093 / 2000) (10181279036831 / 50000) := by
  exact
    packedTile16384 203614464 203647232 12 1721 14269 28 _ _ (478293 / 25000) (76527 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203647232 :
    ThetaLowerSegment 203647232 203680000 (10181279036831 / 50000) (10182941597203 / 50000) := by
  exact
    packedTile16384 203647232 203680000 12 1738 14270 28 _ _ (478297 / 25000) (1913191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203680000 :
    ThetaLowerSegment 203680000 203712768 (10182941597203 / 50000) (20369214084311 / 100000) := by
  exact
    packedTile16384 203680000 203712768 12 1741 14271 28 _ _ (382641 / 20000) (239151 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203712768 :
    ThetaLowerSegment 203712768 203745536 (20369214084311 / 100000) (20372412989823 / 100000) := by
  exact
    packedTile16384 203712768 203745536 12 1672 14272 28 _ _ (1913221 / 100000) (239153 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203745536 :
    ThetaLowerSegment 203745536 203778304 (20372412989823 / 100000) (10187893013327 / 50000) := by
  exact
    packedTile16384 203745536 203778304 12 1763 14273 28 _ _ (1913237 / 100000) (47831 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203778304 :
    ThetaLowerSegment 203778304 203811072 (10187893013327 / 50000) (20379074908561 / 100000) := by
  exact
    packedTile16384 203778304 203811072 12 1719 14275 28 _ _ (1913253 / 100000) (239157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203811072 :
    ThetaLowerSegment 203811072 203843840 (20379074908561 / 100000) (815293557819 / 4000) := by
  exact
    packedTile16384 203811072 203843840 12 1706 14276 28 _ _ (1913269 / 100000) (239159 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203843840 :
    ThetaLowerSegment 203843840 203876608 (815293557819 / 4000) (163084579177 / 800) := by
  exact
    packedTile16384 203843840 203876608 12 1690 14277 28 _ _ (382657 / 20000) (239161 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203876608 :
    ThetaLowerSegment 203876608 203909376 (163084579177 / 800) (10194470860093 / 50000) := by
  exact
    packedTile16384 203876608 203909376 12 1761 14278 28 _ _ (1913301 / 100000) (239163 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203909376 :
    ThetaLowerSegment 203909376 203942144 (10194470860093 / 50000) (20392272805083 / 100000) := by
  exact
    packedTile16384 203909376 203942144 12 1741 14279 28 _ _ (1913317 / 100000) (47833 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203942144 :
    ThetaLowerSegment 203942144 203974912 (20392272805083 / 100000) (20395567564509 / 100000) := by
  exact
    packedTile16384 203942144 203974912 12 1722 14280 28 _ _ (1913333 / 100000) (239167 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell203974912 :
    ThetaLowerSegment 203974912 204007680 (20395567564509 / 100000) (1274924711517 / 6250) := by
  exact
    packedTile16384 203974912 204007680 12 1687 14281 28 _ _ (1913349 / 100000) (239169 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204007680 :
    ThetaLowerSegment 204007680 204040448 (1274924711517 / 6250) (20402092112167 / 100000) := by
  exact
    packedTile16384 204007680 204040448 12 1723 14283 28 _ _ (382673 / 20000) (239171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204040448 :
    ThetaLowerSegment 204040448 204073216 (20402092112167 / 100000) (20405402261297 / 100000) := by
  exact
    packedTile16384 204040448 204073216 12 1730 14284 28 _ _ (1913381 / 100000) (239173 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204073216 :
    ThetaLowerSegment 204073216 204105984 (20405402261297 / 100000) (10204347608767 / 50000) := by
  exact
    packedTile16384 204073216 204105984 12 1721 14285 28 _ _ (1913397 / 100000) (9567 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204105984 :
    ThetaLowerSegment 204105984 204138752 (10204347608767 / 50000) (20411892530657 / 100000) := by
  exact
    packedTile16384 204105984 204138752 12 1671 14286 28 _ _ (1913413 / 100000) (239177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204138752 :
    ThetaLowerSegment 204138752 204171520 (20411892530657 / 100000) (20415177889967 / 100000) := by
  exact
    packedTile16384 204138752 204171520 12 1717 14287 28 _ _ (191343 / 10000) (1913433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204171520 :
    ThetaLowerSegment 204171520 204204288 (20415177889967 / 100000) (20418472843979 / 100000) := by
  exact
    packedTile16384 204171520 204204288 12 1722 14288 28 _ _ (956723 / 50000) (1913449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204204288 :
    ThetaLowerSegment 204204288 204237056 (20418472843979 / 100000) (20421605181273 / 100000) := by
  exact
    packedTile16384 204204288 204237056 12 1637 14290 28 _ _ (956731 / 50000) (382693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204237056 :
    ThetaLowerSegment 204237056 204269824 (20421605181273 / 100000) (20424925065603 / 100000) := by
  exact
    packedTile16384 204237056 204269824 12 1735 14291 28 _ _ (956739 / 50000) (1913481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204269824 :
    ThetaLowerSegment 204269824 204302592 (20424925065603 / 100000) (20428199053837 / 100000) := by
  exact
    packedTile16384 204269824 204302592 12 1711 14292 28 _ _ (956747 / 50000) (1913497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204302592 :
    ThetaLowerSegment 204302592 204335360 (20428199053837 / 100000) (20431476896467 / 100000) := by
  exact
    packedTile16384 204302592 204335360 12 1713 14293 28 _ _ (191351 / 10000) (1913513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204335360 :
    ThetaLowerSegment 204335360 204368128 (20431476896467 / 100000) (20434705014829 / 100000) := by
  exact
    packedTile16384 204335360 204368128 12 1687 14294 28 _ _ (956763 / 50000) (1913529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204368128 :
    ThetaLowerSegment 204368128 204400896 (20434705014829 / 100000) (20438013528947 / 100000) := by
  exact
    packedTile16384 204368128 204400896 12 1729 14295 28 _ _ (956771 / 50000) (382709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204400896 :
    ThetaLowerSegment 204400896 204433664 (20438013528947 / 100000) (4088265179569 / 20000) := by
  exact
    packedTile16384 204400896 204433664 12 1731 14296 28 _ _ (956779 / 50000) (1913561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204433664 :
    ThetaLowerSegment 204433664 204466432 (4088265179569 / 20000) (20444649775883 / 100000) := by
  exact
    packedTile16384 204433664 204466432 12 1737 14298 28 _ _ (956787 / 50000) (1913577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204466432 :
    ThetaLowerSegment 204466432 204499200 (20444649775883 / 100000) (20447946891453 / 100000) := by
  exact
    packedTile16384 204466432 204499200 12 1723 14299 28 _ _ (191359 / 10000) (1913593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204499200 :
    ThetaLowerSegment 204499200 204531968 (20447946891453 / 100000) (20451221071319 / 100000) := by
  exact
    packedTile16384 204499200 204531968 12 1711 14300 28 _ _ (956803 / 50000) (1913609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204531968 :
    ThetaLowerSegment 204531968 204564736 (20451221071319 / 100000) (20454581391551 / 100000) := by
  exact
    packedTile16384 204531968 204564736 12 1756 14301 28 _ _ (956811 / 50000) (15309 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204564736 :
    ThetaLowerSegment 204564736 204597504 (20454581391551 / 100000) (4091548927033 / 20000) := by
  exact
    packedTile16384 204564736 204597504 12 1653 14302 28 _ _ (956819 / 50000) (1913641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204597504 :
    ThetaLowerSegment 204597504 204630272 (4091548927033 / 20000) (4092207224009 / 20000) := by
  exact
    packedTile16384 204597504 204630272 12 1720 14303 28 _ _ (956827 / 50000) (1913657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204630272 :
    ThetaLowerSegment 204630272 204663040 (4092207224009 / 20000) (4092857106341 / 20000) := by
  exact
    packedTile16384 204630272 204663040 12 1698 14304 28 _ _ (191367 / 10000) (1913673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204663040 :
    ThetaLowerSegment 204663040 204695808 (4092857106341 / 20000) (20467578985311 / 100000) := by
  exact
    packedTile16384 204663040 204695808 12 1721 14306 28 _ _ (956843 / 50000) (1913689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204695808 :
    ThetaLowerSegment 204695808 204712192 (20467578985311 / 100000) (20469224769031 / 100000) := by
  exact
    packedTile16384 204695808 204712192 11 860 14307 28 _ _ (956851 / 50000) (382741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_177432832_204712192 :
    ThetaLowerSegment 177432832 204712192 (17742096478069 / 100000) (20469224769031 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell177432832 cell177465600)
                      (ThetaLowerSegment.join cell177498368 cell177531136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell177563904 cell177596672)
                      (ThetaLowerSegment.join cell177629440 cell177662208)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell177694976 cell177727744)
                      (ThetaLowerSegment.join cell177760512 cell177793280))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell177826048 cell177858816)
                      (ThetaLowerSegment.join cell177891584 cell177924352))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell177957120 cell177989888)
                      (ThetaLowerSegment.join cell178022656 cell178055424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell178088192 cell178120960)
                      (ThetaLowerSegment.join cell178153728 cell178186496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell178219264 cell178252032)
                      (ThetaLowerSegment.join cell178284800 cell178317568))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell178350336 cell178383104)
                      (ThetaLowerSegment.join cell178415872 cell178448640)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell178481408 cell178514176)
                      (ThetaLowerSegment.join cell178546944 cell178579712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell178612480 cell178645248)
                      (ThetaLowerSegment.join cell178678016 cell178710784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell178743552 cell178776320)
                      (ThetaLowerSegment.join cell178809088 cell178841856))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell178874624 cell178907392)
                      (ThetaLowerSegment.join cell178940160 cell178972928))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell179005696 cell179038464)
                      (ThetaLowerSegment.join cell179071232 cell179104000))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell179136768 cell179169536)
                      (ThetaLowerSegment.join cell179202304 cell179235072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell179267840 cell179300608)
                      (ThetaLowerSegment.join cell179333376 cell179366144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell179398912 cell179431680)
                      (ThetaLowerSegment.join cell179464448 cell179497216))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell179529984 cell179562752)
                      (ThetaLowerSegment.join cell179595520 cell179628288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell179661056 cell179693824)
                      (ThetaLowerSegment.join cell179726592 cell179759360)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell179792128 cell179824896)
                      (ThetaLowerSegment.join cell179857664 cell179890432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell179923200 cell179955968)
                      (ThetaLowerSegment.join cell179988736 cell180021504))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell180054272 cell180087040)
                      (ThetaLowerSegment.join cell180119808 cell180152576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell180185344 cell180218112)
                      (ThetaLowerSegment.join cell180250880 cell180283648)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell180316416 cell180349184)
                      (ThetaLowerSegment.join cell180381952 cell180414720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell180447488 cell180480256)
                      (ThetaLowerSegment.join cell180513024 cell180545792)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell180578560 cell180611328)
                      (ThetaLowerSegment.join cell180644096 cell180676864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell180709632 cell180742400)
                      (ThetaLowerSegment.join cell180775168 cell180807936)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell180840704 cell180873472)
                      (ThetaLowerSegment.join cell180906240 cell180939008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell180971776 cell181004544)
                      (ThetaLowerSegment.join cell181037312 cell181070080))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell181102848 cell181135616)
                      (ThetaLowerSegment.join cell181168384 cell181201152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell181233920 cell181266688)
                      (ThetaLowerSegment.join cell181299456 cell181332224)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell181364992 cell181397760)
                      (ThetaLowerSegment.join cell181430528 cell181463296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell181496064 cell181528832)
                      (ThetaLowerSegment.join cell181561600 cell181594368)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell181627136 cell181659904)
                      (ThetaLowerSegment.join cell181692672 cell181725440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell181758208 cell181790976)
                      (ThetaLowerSegment.join cell181823744 cell181856512)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell181889280 cell181922048)
                      (ThetaLowerSegment.join cell181954816 cell181987584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell182020352 cell182053120)
                      (ThetaLowerSegment.join cell182085888 cell182118656))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell182151424 cell182184192)
                      (ThetaLowerSegment.join cell182216960 cell182249728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell182282496 cell182315264)
                      (ThetaLowerSegment.join cell182348032 cell182380800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell182413568 cell182446336)
                      (ThetaLowerSegment.join cell182479104 cell182511872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell182544640 cell182577408)
                      (ThetaLowerSegment.join cell182610176 cell182642944)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell182675712 cell182708480)
                      (ThetaLowerSegment.join cell182741248 cell182774016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell182806784 cell182839552)
                      (ThetaLowerSegment.join cell182872320 cell182905088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell182937856 cell182970624)
                      (ThetaLowerSegment.join cell183003392 cell183036160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell183068928 cell183101696)
                      (ThetaLowerSegment.join cell183134464 cell183167232))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell183200000 cell183232768)
                      (ThetaLowerSegment.join cell183265536 cell183298304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell183331072 cell183363840)
                      (ThetaLowerSegment.join cell183396608 cell183429376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell183462144 cell183494912)
                      (ThetaLowerSegment.join cell183527680 cell183560448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell183593216 cell183625984)
                      (ThetaLowerSegment.join cell183658752 cell183691520))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell183724288 cell183757056)
                      (ThetaLowerSegment.join cell183789824 cell183822592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell183855360 cell183888128)
                      (ThetaLowerSegment.join cell183920896 cell183953664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell183986432 cell184019200)
                      (ThetaLowerSegment.join cell184051968 cell184084736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell184117504 cell184150272)
                      (ThetaLowerSegment.join cell184183040 cell184215808))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell184248576 cell184281344)
                      (ThetaLowerSegment.join cell184314112 cell184346880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell184379648 cell184412416)
                      (ThetaLowerSegment.join cell184445184 cell184477952)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell184510720 cell184543488)
                      (ThetaLowerSegment.join cell184576256 cell184609024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell184641792 cell184674560)
                      (ThetaLowerSegment.join cell184707328 cell184740096)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell184772864 cell184805632)
                      (ThetaLowerSegment.join cell184838400 cell184871168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell184903936 cell184936704)
                      (ThetaLowerSegment.join cell184969472 cell185002240)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell185035008 cell185067776)
                      (ThetaLowerSegment.join cell185100544 cell185133312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell185166080 cell185198848)
                      (ThetaLowerSegment.join cell185231616 cell185264384))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell185297152 cell185329920)
                      (ThetaLowerSegment.join cell185362688 cell185395456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell185428224 cell185460992)
                      (ThetaLowerSegment.join cell185493760 cell185526528)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell185559296 cell185592064)
                      (ThetaLowerSegment.join cell185624832 cell185657600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell185690368 cell185723136)
                      (ThetaLowerSegment.join cell185755904 cell185788672))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell185821440 cell185854208)
                      (ThetaLowerSegment.join cell185886976 cell185919744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell185952512 cell185985280)
                      (ThetaLowerSegment.join cell186018048 cell186050816)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell186083584 cell186116352)
                      (ThetaLowerSegment.join cell186149120 cell186181888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell186214656 cell186247424)
                      (ThetaLowerSegment.join cell186280192 cell186312960))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell186345728 cell186378496)
                      (ThetaLowerSegment.join cell186411264 cell186444032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell186476800 cell186509568)
                      (ThetaLowerSegment.join cell186542336 cell186575104)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell186607872 cell186640640)
                      (ThetaLowerSegment.join cell186673408 cell186706176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell186738944 cell186771712)
                      (ThetaLowerSegment.join cell186804480 cell186837248)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell186870016 cell186902784)
                      (ThetaLowerSegment.join cell186935552 cell186968320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell187001088 cell187033856)
                      (ThetaLowerSegment.join cell187066624 cell187099392)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell187132160 cell187164928)
                      (ThetaLowerSegment.join cell187197696 cell187230464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell187263232 cell187296000)
                      (ThetaLowerSegment.join cell187328768 cell187361536))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell187394304 cell187427072)
                      (ThetaLowerSegment.join cell187459840 cell187492608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell187525376 cell187558144)
                      (ThetaLowerSegment.join cell187590912 cell187623680)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell187656448 cell187689216)
                      (ThetaLowerSegment.join cell187721984 cell187754752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell187787520 cell187820288)
                      (ThetaLowerSegment.join cell187853056 cell187885824))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell187918592 cell187951360)
                      (ThetaLowerSegment.join cell187984128 cell188016896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell188049664 cell188082432)
                      (ThetaLowerSegment.join cell188115200 cell188147968)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell188180736 cell188213504)
                      (ThetaLowerSegment.join cell188246272 cell188279040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell188311808 cell188344576)
                      (ThetaLowerSegment.join cell188377344 cell188410112))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell188442880 cell188475648)
                      (ThetaLowerSegment.join cell188508416 cell188541184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell188573952 cell188606720)
                      (ThetaLowerSegment.join cell188639488 cell188672256)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell188705024 cell188737792)
                      (ThetaLowerSegment.join cell188770560 cell188803328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell188836096 cell188868864)
                      (ThetaLowerSegment.join cell188901632 cell188934400)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell188967168 cell188999936)
                      (ThetaLowerSegment.join cell189032704 cell189065472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell189098240 cell189131008)
                      (ThetaLowerSegment.join cell189163776 cell189196544)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell189229312 cell189262080)
                      (ThetaLowerSegment.join cell189294848 cell189327616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell189360384 cell189393152)
                      (ThetaLowerSegment.join cell189425920 cell189458688))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell189491456 cell189524224)
                      (ThetaLowerSegment.join cell189556992 cell189589760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell189622528 cell189655296)
                      (ThetaLowerSegment.join cell189688064 cell189720832)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell189753600 cell189786368)
                      (ThetaLowerSegment.join cell189819136 cell189851904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell189884672 cell189917440)
                      (ThetaLowerSegment.join cell189950208 cell189982976)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell190015744 cell190048512)
                      (ThetaLowerSegment.join cell190081280 cell190114048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell190146816 cell190179584)
                      (ThetaLowerSegment.join cell190212352 cell190245120)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell190277888 cell190310656)
                      (ThetaLowerSegment.join cell190343424 cell190376192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell190408960 cell190441728)
                      (ThetaLowerSegment.join cell190474496 cell190507264))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell190540032 cell190572800)
                      (ThetaLowerSegment.join cell190605568 cell190638336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell190671104 cell190703872)
                      (ThetaLowerSegment.join cell190736640 cell190769408)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell190802176 cell190834944)
                      (ThetaLowerSegment.join cell190867712 cell190900480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell190933248 cell190966016)
                      (ThetaLowerSegment.join cell190998784 cell191031552)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell191064320 cell191097088)
                      (ThetaLowerSegment.join cell191129856 cell191162624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell191195392 cell191228160)
                      (ThetaLowerSegment.join cell191260928 cell191293696)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell191326464 cell191359232)
                      (ThetaLowerSegment.join cell191392000 cell191424768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell191457536 cell191490304)
                      (ThetaLowerSegment.join cell191523072 cell191555840))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell191588608 cell191621376)
                      (ThetaLowerSegment.join cell191654144 cell191686912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell191719680 cell191752448)
                      (ThetaLowerSegment.join cell191785216 cell191817984)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell191850752 cell191883520)
                      (ThetaLowerSegment.join cell191916288 cell191949056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell191981824 cell192014592)
                      (ThetaLowerSegment.join cell192047360 cell192080128))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell192112896 cell192145664)
                      (ThetaLowerSegment.join cell192178432 cell192211200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell192243968 cell192276736)
                      (ThetaLowerSegment.join cell192309504 cell192342272)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell192375040 cell192407808)
                      (ThetaLowerSegment.join cell192440576 cell192473344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell192506112 cell192538880)
                      (ThetaLowerSegment.join cell192571648 cell192604416))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell192637184 cell192669952)
                      (ThetaLowerSegment.join cell192702720 cell192735488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell192768256 cell192801024)
                      (ThetaLowerSegment.join cell192833792 cell192866560)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell192899328 cell192932096)
                      (ThetaLowerSegment.join cell192964864 cell192997632))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell193030400 cell193063168)
                      (ThetaLowerSegment.join cell193095936 cell193128704)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell193161472 cell193194240)
                      (ThetaLowerSegment.join cell193227008 cell193259776))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell193292544 cell193325312)
                      (ThetaLowerSegment.join cell193358080 cell193390848)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell193423616 cell193456384)
                      (ThetaLowerSegment.join cell193489152 cell193521920))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell193554688 cell193587456)
                      (ThetaLowerSegment.join cell193620224 cell193652992))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell193685760 cell193718528)
                      (ThetaLowerSegment.join cell193751296 cell193784064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell193816832 cell193849600)
                      (ThetaLowerSegment.join cell193882368 cell193915136)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell193947904 cell193980672)
                      (ThetaLowerSegment.join cell194013440 cell194046208))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell194078976 cell194111744)
                      (ThetaLowerSegment.join cell194144512 cell194177280)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell194210048 cell194242816)
                      (ThetaLowerSegment.join cell194275584 cell194308352))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell194341120 cell194373888)
                      (ThetaLowerSegment.join cell194406656 cell194439424)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell194472192 cell194504960)
                      (ThetaLowerSegment.join cell194537728 cell194570496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell194603264 cell194636032)
                      (ThetaLowerSegment.join cell194668800 cell194701568))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell194734336 cell194767104)
                      (ThetaLowerSegment.join cell194799872 cell194832640))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell194865408 cell194898176)
                      (ThetaLowerSegment.join cell194930944 cell194963712)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell194996480 cell195029248)
                      (ThetaLowerSegment.join cell195062016 cell195094784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell195127552 cell195160320)
                      (ThetaLowerSegment.join cell195193088 cell195225856)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell195258624 cell195291392)
                      (ThetaLowerSegment.join cell195324160 cell195356928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell195389696 cell195422464)
                      (ThetaLowerSegment.join cell195455232 cell195488000)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell195520768 cell195553536)
                      (ThetaLowerSegment.join cell195586304 cell195619072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell195651840 cell195684608)
                      (ThetaLowerSegment.join cell195717376 cell195750144))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell195782912 cell195815680)
                      (ThetaLowerSegment.join cell195848448 cell195881216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell195913984 cell195946752)
                      (ThetaLowerSegment.join cell195979520 cell196012288)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell196045056 cell196077824)
                      (ThetaLowerSegment.join cell196110592 cell196143360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell196176128 cell196208896)
                      (ThetaLowerSegment.join cell196241664 cell196274432))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell196307200 cell196339968)
                      (ThetaLowerSegment.join cell196372736 cell196405504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell196438272 cell196471040)
                      (ThetaLowerSegment.join cell196503808 cell196536576)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell196569344 cell196602112)
                      (ThetaLowerSegment.join cell196634880 cell196667648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell196700416 cell196733184)
                      (ThetaLowerSegment.join cell196765952 cell196798720))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell196831488 cell196864256)
                      (ThetaLowerSegment.join cell196897024 cell196929792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell196962560 cell196995328)
                      (ThetaLowerSegment.join cell197028096 cell197060864)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell197093632 cell197126400)
                      (ThetaLowerSegment.join cell197159168 cell197191936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell197224704 cell197257472)
                      (ThetaLowerSegment.join cell197290240 cell197323008)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell197355776 cell197388544)
                      (ThetaLowerSegment.join cell197421312 cell197454080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell197486848 cell197519616)
                      (ThetaLowerSegment.join cell197552384 cell197585152)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell197617920 cell197650688)
                      (ThetaLowerSegment.join cell197683456 cell197716224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell197748992 cell197781760)
                      (ThetaLowerSegment.join cell197814528 cell197847296))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell197880064 cell197912832)
                      (ThetaLowerSegment.join cell197945600 cell197978368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell198011136 cell198043904)
                      (ThetaLowerSegment.join cell198076672 cell198109440)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell198142208 cell198174976)
                      (ThetaLowerSegment.join cell198207744 cell198240512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell198273280 cell198306048)
                      (ThetaLowerSegment.join cell198338816 cell198371584)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell198404352 cell198437120)
                      (ThetaLowerSegment.join cell198469888 cell198502656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell198535424 cell198568192)
                      (ThetaLowerSegment.join cell198600960 cell198633728)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell198666496 cell198699264)
                      (ThetaLowerSegment.join cell198732032 cell198764800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell198797568 cell198830336)
                      (ThetaLowerSegment.join cell198863104 cell198895872))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell198928640 cell198961408)
                      (ThetaLowerSegment.join cell198994176 cell199026944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell199059712 cell199092480)
                      (ThetaLowerSegment.join cell199125248 cell199158016)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell199190784 cell199223552)
                      (ThetaLowerSegment.join cell199256320 cell199289088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell199321856 cell199354624)
                      (ThetaLowerSegment.join cell199387392 cell199420160)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell199452928 cell199485696)
                      (ThetaLowerSegment.join cell199518464 cell199551232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell199584000 cell199616768)
                      (ThetaLowerSegment.join cell199649536 cell199682304)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell199715072 cell199747840)
                      (ThetaLowerSegment.join cell199780608 cell199813376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell199846144 cell199878912)
                      (ThetaLowerSegment.join cell199911680 cell199944448))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell199977216 cell200009984)
                      (ThetaLowerSegment.join cell200042752 cell200075520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell200108288 cell200141056)
                      (ThetaLowerSegment.join cell200173824 cell200206592)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell200239360 cell200272128)
                      (ThetaLowerSegment.join cell200304896 cell200337664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell200370432 cell200403200)
                      (ThetaLowerSegment.join cell200435968 cell200468736))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell200501504 cell200534272)
                      (ThetaLowerSegment.join cell200567040 cell200599808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell200632576 cell200665344)
                      (ThetaLowerSegment.join cell200698112 cell200730880)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell200763648 cell200796416)
                      (ThetaLowerSegment.join cell200829184 cell200861952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell200894720 cell200927488)
                      (ThetaLowerSegment.join cell200960256 cell200993024))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell201025792 cell201058560)
                      (ThetaLowerSegment.join cell201091328 cell201124096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell201156864 cell201189632)
                      (ThetaLowerSegment.join cell201222400 cell201255168)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell201287936 cell201320704)
                      (ThetaLowerSegment.join cell201353472 cell201386240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell201419008 cell201451776)
                      (ThetaLowerSegment.join cell201484544 cell201517312)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell201550080 cell201582848)
                      (ThetaLowerSegment.join cell201615616 cell201648384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell201681152 cell201713920)
                      (ThetaLowerSegment.join cell201746688 cell201779456)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell201812224 cell201844992)
                      (ThetaLowerSegment.join cell201877760 cell201910528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell201943296 cell201976064)
                      (ThetaLowerSegment.join cell202008832 cell202041600))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell202074368 cell202107136)
                      (ThetaLowerSegment.join cell202139904 cell202172672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell202205440 cell202238208)
                      (ThetaLowerSegment.join cell202270976 cell202303744)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell202336512 cell202369280)
                      (ThetaLowerSegment.join cell202402048 cell202434816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell202467584 cell202500352)
                      (ThetaLowerSegment.join cell202533120 cell202565888))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell202598656 cell202631424)
                    (ThetaLowerSegment.join cell202664192 cell202696960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell202729728 cell202762496)
                    (ThetaLowerSegment.join cell202795264 cell202828032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell202860800 cell202893568)
                    (ThetaLowerSegment.join cell202926336 cell202959104))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell202991872 cell203024640)
                    (ThetaLowerSegment.join cell203057408 cell203090176))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell203122944 cell203155712)
                    (ThetaLowerSegment.join cell203188480 cell203221248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell203254016 cell203286784)
                    (ThetaLowerSegment.join cell203319552 cell203352320)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell203385088 cell203417856)
                    (ThetaLowerSegment.join cell203450624 cell203483392))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell203516160 cell203548928)
                    (ThetaLowerSegment.join cell203581696 cell203614464)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell203647232 cell203680000)
                    (ThetaLowerSegment.join cell203712768 cell203745536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell203778304 cell203811072)
                    (ThetaLowerSegment.join cell203843840 cell203876608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell203909376 cell203942144)
                    (ThetaLowerSegment.join cell203974912 cell204007680))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell204040448 cell204073216)
                    (ThetaLowerSegment.join cell204105984 cell204138752))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell204171520 cell204204288)
                    (ThetaLowerSegment.join cell204237056 cell204269824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell204302592 cell204335360)
                    (ThetaLowerSegment.join cell204368128 cell204400896)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell204433664 cell204466432)
                    (ThetaLowerSegment.join cell204499200 cell204531968))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell204564736 cell204597504)
                    (ThetaLowerSegment.join cell204630272 cell204663040))))))
          cell204695808)))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
