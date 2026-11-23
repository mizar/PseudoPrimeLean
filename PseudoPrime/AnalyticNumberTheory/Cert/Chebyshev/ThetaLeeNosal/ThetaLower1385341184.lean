/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1385341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1353341184 :
    ThetaLowerSegment 1353341184 1353472256 (135329374024609 / 100000)
      (67671321712961 / 50000) := by
  exact
    packedTile65536 1353341184 1353472256 14 6311 36787 30 _ _ (2102583 / 100000) (1051293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353472256 :
    ThetaLowerSegment 1353472256 1353603328 (67671321712961 / 50000) (67677787183361 / 50000) := by
  exact
    packedTile65536 1353472256 1353603328 14 6150 36789 30 _ _ (65706 / 3125) (420519 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353603328 :
    ThetaLowerSegment 1353603328 1353734400 (67677787183361 / 50000) (4230271903469 / 3125) := by
  exact
    packedTile65536 1353603328 1353734400 14 6243 36791 30 _ _ (1051301 / 50000) (420521 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353734400 :
    ThetaLowerSegment 1353734400 1353865472 (4230271903469 / 3125) (8461374864331 / 6250) := by
  exact
    packedTile65536 1353734400 1353865472 14 6324 36793 30 _ _ (525653 / 25000) (420523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353865472 :
    ThetaLowerSegment 1353865472 1353996544 (8461374864331 / 6250) (135395212802281 / 100000) := by
  exact
    packedTile65536 1353865472 1353996544 14 6285 36794 30 _ _ (2102621 / 100000) (65707 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353996544 :
    ThetaLowerSegment 1353996544 1354127616 (135395212802281 / 100000)
      (33852115370053 / 25000) := by
  exact
    packedTile65536 1353996544 1354127616 14 6301 36796 30 _ _ (2102631 / 100000) (1051317 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1354127616 :
    ThetaLowerSegment 1354127616 1354258688 (33852115370053 / 25000)
      (135421579857411 / 100000) := by
  exact
    packedTile65536 1354127616 1354258688 14 6239 36798 30 _ _ (2102641 / 100000) (525661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1354258688 :
    ThetaLowerSegment 1354258688 1354389760 (135421579857411 / 100000)
      (33858668266297 / 25000) := by
  exact
    packedTile65536 1354258688 1354389760 14 6227 36800 30 _ _ (2102651 / 100000) (1051327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1354389760 :
    ThetaLowerSegment 1354389760 1354520832 (33858668266297 / 25000) (33861963134517 / 25000) := by
  exact
    packedTile65536 1354389760 1354520832 14 6268 36802 30 _ _ (105133 / 5000) (2102663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1354520832 :
    ThetaLowerSegment 1354520832 1354651904 (33861963134517 / 25000) (33865243299717 / 25000) := by
  exact
    packedTile65536 1354520832 1354651904 14 6240 36803 30 _ _ (210267 / 10000) (2102673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1354651904 :
    ThetaLowerSegment 1354651904 1354782976 (33865243299717 / 25000) (33868494042997 / 25000) := by
  exact
    packedTile65536 1354651904 1354782976 14 6184 36805 30 _ _ (52567 / 2500) (2102683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1354782976 :
    ThetaLowerSegment 1354782976 1354914048 (33868494042997 / 25000) (16935888170263 / 12500) := by
  exact
    packedTile65536 1354782976 1354914048 14 6244 36807 30 _ _ (2102689 / 100000) (525673 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1354914048 :
    ThetaLowerSegment 1354914048 1355045120 (16935888170263 / 12500) (67750110999233 / 50000) := by
  exact
    packedTile65536 1354914048 1355045120 14 6238 36809 30 _ _ (2102699 / 100000) (1051351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1355045120 :
    ThetaLowerSegment 1355045120 1355176192 (67750110999233 / 50000) (13551346065433 / 10000) := by
  exact
    packedTile65536 1355045120 1355176192 14 6296 36810 30 _ _ (2102709 / 100000) (262839 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1355176192 :
    ThetaLowerSegment 1355176192 1355307264 (13551346065433 / 10000) (8470414110733 / 6250) := by
  exact
    packedTile65536 1355176192 1355307264 14 6261 36812 30 _ _ (1051359 / 50000) (2102721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1355307264 :
    ThetaLowerSegment 1355307264 1355438336 (8470414110733 / 6250) (4235624315454 / 3125) := by
  exact
    packedTile65536 1355307264 1355438336 14 6350 36814 30 _ _ (262841 / 12500) (2102731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1355438336 :
    ThetaLowerSegment 1355438336 1355569408 (4235624315454 / 3125) (67776521202861 / 50000) := by
  exact
    packedTile65536 1355438336 1355569408 14 6213 36816 30 _ _ (1051369 / 50000) (2102741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1355569408 :
    ThetaLowerSegment 1355569408 1355700480 (67776521202861 / 50000) (67783123828441 / 50000) := by
  exact
    packedTile65536 1355569408 1355700480 14 6280 36818 30 _ _ (2102747 / 100000) (8411 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1355700480 :
    ThetaLowerSegment 1355700480 1355831552 (67783123828441 / 50000) (27115869146047 / 20000) := by
  exact
    packedTile65536 1355700480 1355831552 14 6229 36819 30 _ _ (2102757 / 100000) (52569 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1355831552 :
    ThetaLowerSegment 1355831552 1355962624 (27115869146047 / 20000) (67796276604881 / 50000) := by
  exact
    packedTile65536 1355831552 1355962624 14 6281 36821 30 _ _ (2102767 / 100000) (210277 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1355962624 :
    ThetaLowerSegment 1355962624 1356093696 (67796276604881 / 50000) (67802773131333 / 50000) := by
  exact
    packedTile65536 1355962624 1356093696 14 6179 36823 30 _ _ (262847 / 12500) (2102779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1356093696 :
    ThetaLowerSegment 1356093696 1356224768 (67802773131333 / 50000) (13561869708631 / 10000) := by
  exact
    packedTile65536 1356093696 1356224768 14 6254 36825 30 _ _ (1051393 / 50000) (2102789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1356224768 :
    ThetaLowerSegment 1356224768 1356355840 (13561869708631 / 10000) (67815902958287 / 50000) := by
  exact
    packedTile65536 1356224768 1356355840 14 6234 36826 30 _ _ (525699 / 25000) (2102799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1356355840 :
    ThetaLowerSegment 1356355840 1356486912 (67815902958287 / 50000) (16955620658783 / 12500) := by
  exact
    packedTile65536 1356355840 1356486912 14 6258 36828 30 _ _ (420561 / 20000) (262851 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1356486912 :
    ThetaLowerSegment 1356486912 1356617984 (16955620658783 / 12500) (67828948791257 / 50000) := by
  exact
    packedTile65536 1356486912 1356617984 14 6150 36830 30 _ _ (420563 / 20000) (1051409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1356617984 :
    ThetaLowerSegment 1356617984 1356749056 (67828948791257 / 50000) (67835513810907 / 50000) := by
  exact
    packedTile65536 1356617984 1356749056 14 6244 36832 30 _ _ (84113 / 4000) (525707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1356749056 :
    ThetaLowerSegment 1356749056 1356880128 (67835513810907 / 50000) (33921032595117 / 25000) := by
  exact
    packedTile65536 1356749056 1356880128 14 6231 36834 30 _ _ (1051417 / 50000) (2102837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1356880128 :
    ThetaLowerSegment 1356880128 1357011200 (33921032595117 / 25000) (33924318288867 / 25000) := by
  exact
    packedTile65536 1356880128 1357011200 14 6250 36835 30 _ _ (525711 / 25000) (2102847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1357011200 :
    ThetaLowerSegment 1357011200 1357142272 (33924318288867 / 25000) (33927619769647 / 25000) := by
  exact
    packedTile65536 1357011200 1357142272 14 6280 36837 30 _ _ (1051427 / 50000) (2102857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1357142272 :
    ThetaLowerSegment 1357142272 1357273344 (33927619769647 / 25000) (13572354626927 / 10000) := by
  exact
    packedTile65536 1357142272 1357273344 14 6214 36839 30 _ _ (2102863 / 100000) (1051433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1357273344 :
    ThetaLowerSegment 1357273344 1357404416 (13572354626927 / 10000)
      (135736607213473 / 100000) := by
  exact
    packedTile65536 1357273344 1357404416 14 6211 36841 30 _ _ (2102873 / 100000) (525719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1357404416 :
    ThetaLowerSegment 1357404416 1357535488 (135736607213473 / 100000)
      (67874876167553 / 50000) := by
  exact
    packedTile65536 1357404416 1357535488 14 6251 36842 30 _ _ (2102883 / 100000) (1051443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1357535488 :
    ThetaLowerSegment 1357535488 1357666560 (67874876167553 / 50000) (67881432984809 / 50000) := by
  exact
    packedTile65536 1357535488 1357666560 14 6236 36844 30 _ _ (525723 / 25000) (420579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1357666560 :
    ThetaLowerSegment 1357666560 1357797632 (67881432984809 / 50000) (33943994390897 / 25000) := by
  exact
    packedTile65536 1357666560 1357797632 14 6235 36846 30 _ _ (1051451 / 50000) (420581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1357797632 :
    ThetaLowerSegment 1357797632 1357928704 (33943994390897 / 25000)
      (135789164918469 / 100000) := by
  exact
    packedTile65536 1357797632 1357928704 14 6271 36848 30 _ _ (2102911 / 100000) (1051457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1357928704 :
    ThetaLowerSegment 1357928704 1358059776 (135789164918469 / 100000)
      (27160451540923 / 20000) := by
  exact
    packedTile65536 1357928704 1358059776 14 6226 36850 30 _ _ (2102921 / 100000) (525731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358059776 :
    ThetaLowerSegment 1358059776 1358190848 (27160451540923 / 20000) (33953827649333 / 25000) := by
  exact
    packedTile65536 1358059776 1358190848 14 6207 36851 30 _ _ (2102931 / 100000) (1051467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358190848 :
    ThetaLowerSegment 1358190848 1358321920 (33953827649333 / 25000) (33957105081323 / 25000) := by
  exact
    packedTile65536 1358190848 1358321920 14 6234 36853 30 _ _ (105147 / 5000) (2102943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358321920 :
    ThetaLowerSegment 1358321920 1358452992 (33957105081323 / 25000) (67920885977421 / 50000) := by
  exact
    packedTile65536 1358321920 1358452992 14 6349 36855 30 _ _ (42059 / 2000) (2102953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358452992 :
    ThetaLowerSegment 1358452992 1358584064 (67920885977421 / 50000) (67927372557541 / 50000) := by
  exact
    packedTile65536 1358452992 1358584064 14 6169 36857 30 _ _ (26287 / 1250) (2102963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358584064 :
    ThetaLowerSegment 1358584064 1358715136 (67927372557541 / 50000) (16983474517587 / 12500) := by
  exact
    packedTile65536 1358584064 1358715136 14 6206 36858 30 _ _ (2102969 / 100000) (525743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358715136 :
    ThetaLowerSegment 1358715136 1358846208 (16983474517587 / 12500) (67940448849933 / 50000) := by
  exact
    packedTile65536 1358715136 1358846208 14 6230 36860 30 _ _ (2102979 / 100000) (1051491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358846208 :
    ThetaLowerSegment 1358846208 1358977280 (67940448849933 / 50000) (33973493521367 / 25000) := by
  exact
    packedTile65536 1358846208 1358977280 14 6218 36862 30 _ _ (2102989 / 100000) (131437 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358977280 :
    ThetaLowerSegment 1358977280 1359108352 (33973493521367 / 25000) (6795361569243 / 5000) := by
  exact
    packedTile65536 1358977280 1359108352 14 6304 36864 30 _ _ (1051499 / 50000) (2103001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1359108352 :
    ThetaLowerSegment 1359108352 1359239424 (6795361569243 / 5000) (33980068560119 / 25000) := by
  exact
    packedTile65536 1359108352 1359239424 14 6202 36866 30 _ _ (65719 / 3125) (2103011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1359239424 :
    ThetaLowerSegment 1359239424 1359370496 (33980068560119 / 25000) (13593342441203 / 10000) := by
  exact
    packedTile65536 1359239424 1359370496 14 6253 36867 30 _ _ (1051509 / 50000) (2103021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1359370496 :
    ThetaLowerSegment 1359370496 1359501568 (13593342441203 / 10000)
      (135946419015863 / 100000) := by
  exact
    packedTile65536 1359370496 1359501568 14 6179 36869 30 _ _ (2103027 / 100000) (210303 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1359501568 :
    ThetaLowerSegment 1359501568 1359632640 (135946419015863 / 100000)
      (33989890223519 / 25000) := by
  exact
    packedTile65536 1359501568 1359632640 14 6249 36871 30 _ _ (2103037 / 100000) (13144 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1359632640 :
    ThetaLowerSegment 1359632640 1359763712 (33989890223519 / 25000) (67986314614067 / 50000) := by
  exact
    packedTile65536 1359632640 1359763712 14 6214 36873 30 _ _ (2103047 / 100000) (42061 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1359763712 :
    ThetaLowerSegment 1359763712 1359894784 (67986314614067 / 50000) (67992841448363 / 50000) := by
  exact
    packedTile65536 1359763712 1359894784 14 6207 36874 30 _ _ (131441 / 6250) (2103059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1359894784 :
    ThetaLowerSegment 1359894784 1360025856 (67992841448363 / 50000) (33999671538451 / 25000) := by
  exact
    packedTile65536 1359894784 1360025856 14 6183 36876 30 _ _ (1051533 / 50000) (2103069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360025856 :
    ThetaLowerSegment 1360025856 1360156928 (33999671538451 / 25000)
      (136011832475629 / 100000) := by
  exact
    packedTile65536 1360025856 1360156928 14 6251 36878 30 _ _ (84123 / 4000) (1051539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360156928 :
    ThetaLowerSegment 1360156928 1360288000 (136011832475629 / 100000)
      (136025086117299 / 100000) := by
  exact
    packedTile65536 1360156928 1360288000 14 6302 36880 30 _ _ (420617 / 20000) (131443 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360288000 :
    ThetaLowerSegment 1360288000 1360419072 (136025086117299 / 100000)
      (136038301966279 / 100000) := by
  exact
    packedTile65536 1360288000 1360419072 14 6284 36882 30 _ _ (420619 / 20000) (1051549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360419072 :
    ThetaLowerSegment 1360419072 1360550144 (136038301966279 / 100000)
      (136051467397319 / 100000) := by
  exact
    packedTile65536 1360419072 1360550144 14 6260 36883 30 _ _ (65722 / 3125) (2103107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360550144 :
    ThetaLowerSegment 1360550144 1360681216 (136051467397319 / 100000)
      (27212900920201 / 20000) := by
  exact
    packedTile65536 1360550144 1360681216 14 6199 36885 30 _ _ (1051557 / 50000) (2103117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360681216 :
    ThetaLowerSegment 1360681216 1360812288 (27212900920201 / 20000)
      (136077388338629 / 100000) := by
  exact
    packedTile65536 1360681216 1360812288 14 6126 36887 30 _ _ (525781 / 25000) (2103127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360812288 :
    ThetaLowerSegment 1360812288 1360943360 (136077388338629 / 100000)
      (17011309516911 / 12500) := by
  exact
    packedTile65536 1360812288 1360943360 14 6223 36889 30 _ _ (2103133 / 100000) (65723 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360943360 :
    ThetaLowerSegment 1360943360 1361074432 (17011309516911 / 12500)
      (136103728039331 / 100000) := by
  exact
    packedTile65536 1360943360 1361074432 14 6301 36890 30 _ _ (2103143 / 100000) (1051573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1361074432 :
    ThetaLowerSegment 1361074432 1361205504 (136103728039331 / 100000)
      (136116767587931 / 100000) := by
  exact
    packedTile65536 1361074432 1361205504 14 6200 36892 30 _ _ (2103153 / 100000) (525789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1361205504 :
    ThetaLowerSegment 1361205504 1361336576 (136116767587931 / 100000)
      (136129903937783 / 100000) := by
  exact
    packedTile65536 1361205504 1361336576 14 6246 36894 30 _ _ (1051581 / 50000) (420633 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1361336576 :
    ThetaLowerSegment 1361336576 1361467648 (136129903937783 / 100000)
      (27228597554159 / 20000) := by
  exact
    packedTile65536 1361336576 1361467648 14 6221 36896 30 _ _ (525793 / 25000) (84127 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1361467648 :
    ThetaLowerSegment 1361467648 1361598720 (27228597554159 / 20000)
      (136156115826597 / 100000) := by
  exact
    packedTile65536 1361467648 1361598720 14 6242 36898 30 _ _ (2103181 / 100000) (131449 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1361598720 :
    ThetaLowerSegment 1361598720 1361729792 (136156115826597 / 100000)
      (68084585166567 / 50000) := by
  exact
    packedTile65536 1361598720 1361729792 14 6207 36899 30 _ _ (2103191 / 100000) (1051597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1361729792 :
    ThetaLowerSegment 1361729792 1361860864 (68084585166567 / 50000)
      (136182431015439 / 100000) := by
  exact
    packedTile65536 1361729792 1361860864 14 6305 36901 30 _ _ (2103201 / 100000) (525801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1361860864 :
    ThetaLowerSegment 1361860864 1361991936 (136182431015439 / 100000)
      (136195548736209 / 100000) := by
  exact
    packedTile65536 1361860864 1361991936 14 6237 36903 30 _ _ (210321 / 10000) (2103213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1361991936 :
    ThetaLowerSegment 1361991936 1362123008 (136195548736209 / 100000)
      (136208729615949 / 100000) := by
  exact
    packedTile65536 1361991936 1362123008 14 6267 36905 30 _ _ (105161 / 5000) (2103223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1362123008 :
    ThetaLowerSegment 1362123008 1362254080 (136208729615949 / 100000)
      (136221799087169 / 100000) := by
  exact
    packedTile65536 1362123008 1362254080 14 6214 36906 30 _ _ (210323 / 10000) (2103233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1362254080 :
    ThetaLowerSegment 1362254080 1362385152 (136221799087169 / 100000)
      (34058716627769 / 25000) := by
  exact
    packedTile65536 1362254080 1362385152 14 6213 36908 30 _ _ (2103239 / 100000) (1051621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1362385152 :
    ThetaLowerSegment 1362385152 1362516224 (34058716627769 / 25000)
      (136247933997113 / 100000) := by
  exact
    packedTile65536 1362385152 1362516224 14 6213 36910 30 _ _ (2103249 / 100000) (525813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1362516224 :
    ThetaLowerSegment 1362516224 1362647296 (136247933997113 / 100000)
      (136261039397711 / 100000) := by
  exact
    packedTile65536 1362516224 1362647296 14 6231 36912 30 _ _ (1051629 / 50000) (2103261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1362647296 :
    ThetaLowerSegment 1362647296 1362778368 (136261039397711 / 100000)
      (136274125931207 / 100000) := by
  exact
    packedTile65536 1362647296 1362778368 14 6222 36914 30 _ _ (525817 / 25000) (2103271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1362778368 :
    ThetaLowerSegment 1362778368 1362909440 (136274125931207 / 100000)
      (136287313484267 / 100000) := by
  exact
    packedTile65536 1362778368 1362909440 14 6270 36915 30 _ _ (1051639 / 50000) (2103281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1362909440 :
    ThetaLowerSegment 1362909440 1363040512 (136287313484267 / 100000)
      (27260068248789 / 20000) := by
  exact
    packedTile65536 1362909440 1363040512 14 6194 36917 30 _ _ (2103287 / 100000) (210329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1363040512 :
    ThetaLowerSegment 1363040512 1363171584 (27260068248789 / 20000)
      (136313470023819 / 100000) := by
  exact
    packedTile65536 1363040512 1363171584 14 6242 36919 30 _ _ (2103297 / 100000) (21033 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1363171584 :
    ThetaLowerSegment 1363171584 1363302656 (136313470023819 / 100000)
      (136326739781373 / 100000) := by
  exact
    packedTile65536 1363171584 1363302656 14 6309 36921 30 _ _ (1051653 / 50000) (2103309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1363302656 :
    ThetaLowerSegment 1363302656 1363433728 (136326739781373 / 100000)
      (136339643625033 / 100000) := by
  exact
    packedTile65536 1363302656 1363433728 14 6135 36922 30 _ _ (525829 / 25000) (2103319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1363433728 :
    ThetaLowerSegment 1363433728 1363564800 (136339643625033 / 100000)
      (27270539793903 / 20000) := by
  exact
    packedTile65536 1363433728 1363564800 14 6207 36924 30 _ _ (1051663 / 50000) (2103329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1363564800 :
    ThetaLowerSegment 1363564800 1363695872 (27270539793903 / 20000) (3409149538251 / 2500) := by
  exact
    packedTile65536 1363564800 1363695872 14 6315 36926 30 _ _ (420667 / 20000) (1051669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1363695872 :
    ThetaLowerSegment 1363695872 1363826944 (3409149538251 / 2500) (13637911060953 / 10000) := by
  exact
    packedTile65536 1363695872 1363826944 14 6242 36928 30 _ _ (420669 / 20000) (525837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1363826944 :
    ThetaLowerSegment 1363826944 1363958016 (13637911060953 / 10000) (27278445846933 / 20000) := by
  exact
    packedTile65536 1363826944 1363958016 14 6237 36930 30 _ _ (420671 / 20000) (1051679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1363958016 :
    ThetaLowerSegment 1363958016 1364089088 (27278445846933 / 20000)
      (136405423637037 / 100000) := by
  exact
    packedTile65536 1363958016 1364089088 14 6273 36931 30 _ _ (525841 / 25000) (2103367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1364089088 :
    ThetaLowerSegment 1364089088 1364220160 (136405423637037 / 100000)
      (136418527657057 / 100000) := by
  exact
    packedTile65536 1364089088 1364220160 14 6230 36933 30 _ _ (1051687 / 50000) (2103377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1364220160 :
    ThetaLowerSegment 1364220160 1364351232 (136418527657057 / 100000)
      (68215791677669 / 50000) := by
  exact
    packedTile65536 1364220160 1364351232 14 6207 36935 30 _ _ (2103383 / 100000) (1051693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1364351232 :
    ThetaLowerSegment 1364351232 1364482304 (68215791677669 / 50000)
      (136444630702117 / 100000) := by
  exact
    packedTile65536 1364351232 1364482304 14 6203 36937 30 _ _ (2103393 / 100000) (525849 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1364482304 :
    ThetaLowerSegment 1364482304 1364613376 (136444630702117 / 100000)
      (136457739109613 / 100000) := by
  exact
    packedTile65536 1364482304 1364613376 14 6232 36938 30 _ _ (2103403 / 100000) (1051703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1364613376 :
    ThetaLowerSegment 1364613376 1364744448 (136457739109613 / 100000)
      (136470654059293 / 100000) := by
  exact
    packedTile65536 1364613376 1364744448 14 6140 36940 30 _ _ (525853 / 25000) (420683 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1364744448 :
    ThetaLowerSegment 1364744448 1364875520 (136470654059293 / 100000)
      (27296810992171 / 20000) := by
  exact
    packedTile65536 1364744448 1364875520 14 6371 36942 30 _ _ (1051711 / 50000) (84137 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1364875520 :
    ThetaLowerSegment 1364875520 1365006592 (27296810992171 / 20000) (68248578616277 / 50000) := by
  exact
    packedTile65536 1364875520 1365006592 14 6229 36944 30 _ _ (2103431 / 100000) (1051717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1365006592 :
    ThetaLowerSegment 1365006592 1365137664 (68248578616277 / 50000)
      (136510120739437 / 100000) := by
  exact
    packedTile65536 1365006592 1365137664 14 6163 36945 30 _ _ (2103441 / 100000) (525861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1365137664 :
    ThetaLowerSegment 1365137664 1365268736 (136510120739437 / 100000) (8532706178747 / 6250) := by
  exact
    packedTile65536 1365137664 1365268736 14 6265 36947 30 _ _ (2103451 / 100000) (1051727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1365268736 :
    ThetaLowerSegment 1365268736 1365399808 (8532706178747 / 6250) (17067059892539 / 12500) := by
  exact
    packedTile65536 1365268736 1365399808 14 6266 36949 30 _ _ (105173 / 5000) (2103463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1365399808 :
    ThetaLowerSegment 1365399808 1365530880 (17067059892539 / 12500) (68274820276051 / 50000) := by
  exact
    packedTile65536 1365399808 1365530880 14 6257 36951 30 _ _ (210347 / 10000) (2103473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1365530880 :
    ThetaLowerSegment 1365530880 1365661952 (68274820276051 / 50000) (8535169473163 / 6250) := by
  exact
    packedTile65536 1365530880 1365661952 14 6214 36953 30 _ _ (2103479 / 100000) (1051741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1365661952 :
    ThetaLowerSegment 1365661952 1365793024 (8535169473163 / 6250) (136575881515237 / 100000) := by
  exact
    packedTile65536 1365661952 1365793024 14 6261 36954 30 _ _ (2103489 / 100000) (525873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1365793024 :
    ThetaLowerSegment 1365793024 1365924096 (136575881515237 / 100000)
      (136589003141999 / 100000) := by
  exact
    packedTile65536 1365793024 1365924096 14 6238 36956 30 _ _ (2103499 / 100000) (1051751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1365924096 :
    ThetaLowerSegment 1365924096 1366055168 (136589003141999 / 100000)
      (27320441372343 / 20000) := by
  exact
    packedTile65536 1365924096 1366055168 14 6277 36958 30 _ _ (525877 / 25000) (2103511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366055168 :
    ThetaLowerSegment 1366055168 1366186240 (27320441372343 / 20000)
      (136615158222041 / 100000) := by
  exact
    packedTile65536 1366055168 1366186240 14 6157 36960 30 _ _ (1051759 / 50000) (2103521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366186240 :
    ThetaLowerSegment 1366186240 1366317312 (136615158222041 / 100000)
      (136628221124711 / 100000) := by
  exact
    packedTile65536 1366186240 1366317312 14 6210 36961 30 _ _ (2103527 / 100000) (210353 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366317312 :
    ThetaLowerSegment 1366317312 1366448384 (136628221124711 / 100000)
      (68320643096509 / 50000) := by
  exact
    packedTile65536 1366317312 1366448384 14 6211 36963 30 _ _ (2103537 / 100000) (105177 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366448384 :
    ThetaLowerSegment 1366448384 1366579456 (68320643096509 / 50000) (68327214577337 / 50000) := by
  exact
    packedTile65536 1366448384 1366579456 14 6248 36965 30 _ _ (2103547 / 100000) (42071 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366579456 :
    ThetaLowerSegment 1366579456 1366710528 (68327214577337 / 50000) (13666737864541 / 10000) := by
  exact
    packedTile65536 1366579456 1366710528 14 6156 36967 30 _ _ (525889 / 25000) (2103559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366710528 :
    ThetaLowerSegment 1366710528 1366841600 (13666737864541 / 10000) (13668052593291 / 10000) := by
  exact
    packedTile65536 1366710528 1366841600 14 6250 36969 30 _ _ (1051783 / 50000) (2103569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366841600 :
    ThetaLowerSegment 1366841600 1366972672 (13668052593291 / 10000) (27338695528837 / 20000) := by
  exact
    packedTile65536 1366841600 1366972672 14 6157 36970 30 _ _ (84143 / 4000) (1051789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366972672 :
    ThetaLowerSegment 1366972672 1367103744 (27338695528837 / 20000) (13670647990307 / 10000) := by
  exact
    packedTile65536 1366972672 1367103744 14 6181 36972 30 _ _ (420717 / 20000) (525897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1367103744 :
    ThetaLowerSegment 1367103744 1367234816 (13670647990307 / 10000) (5468781644977 / 4000) := by
  exact
    packedTile65536 1367103744 1367234816 14 6209 36974 30 _ _ (420719 / 20000) (1051799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1367234816 :
    ThetaLowerSegment 1367234816 1367365888 (5468781644977 / 4000) (136732892699013 / 100000) := by
  exact
    packedTile65536 1367234816 1367365888 14 6347 36976 30 _ _ (525901 / 25000) (2103607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1367365888 :
    ThetaLowerSegment 1367365888 1367496960 (136732892699013 / 100000)
      (136746073944337 / 100000) := by
  exact
    packedTile65536 1367365888 1367496960 14 6266 36977 30 _ _ (1051807 / 50000) (2103617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1367496960 :
    ThetaLowerSegment 1367496960 1367628032 (136746073944337 / 100000)
      (27351796355013 / 20000) := by
  exact
    packedTile65536 1367496960 1367628032 14 6136 36979 30 _ _ (2103623 / 100000) (1051813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1367628032 :
    ThetaLowerSegment 1367628032 1367759104 (27351796355013 / 20000) (27354442725327 / 20000) := by
  exact
    packedTile65536 1367628032 1367759104 14 6290 36981 30 _ _ (2103633 / 100000) (525909 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1367759104 :
    ThetaLowerSegment 1367759104 1367890176 (27354442725327 / 20000)
      (136785323523579 / 100000) := by
  exact
    packedTile65536 1367759104 1367890176 14 6232 36983 30 _ _ (1051821 / 50000) (420729 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1367890176 :
    ThetaLowerSegment 1367890176 1368021248 (136785323523579 / 100000)
      (27359685013647 / 20000) := by
  exact
    packedTile65536 1367890176 1368021248 14 6228 36984 30 _ _ (525913 / 25000) (420731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368021248 :
    ThetaLowerSegment 1368021248 1368152320 (27359685013647 / 20000)
      (136811495120241 / 100000) := by
  exact
    packedTile65536 1368021248 1368152320 14 6213 36986 30 _ _ (1051831 / 50000) (420733 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368152320 :
    ThetaLowerSegment 1368152320 1368283392 (136811495120241 / 100000)
      (17103082223711 / 12500) := by
  exact
    packedTile65536 1368152320 1368283392 14 6257 36988 30 _ _ (2103671 / 100000) (1051837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368283392 :
    ThetaLowerSegment 1368283392 1368414464 (17103082223711 / 12500)
      (136837791070171 / 100000) := by
  exact
    packedTile65536 1368283392 1368414464 14 6243 36990 30 _ _ (2103681 / 100000) (525921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368414464 :
    ThetaLowerSegment 1368414464 1368545536 (136837791070171 / 100000)
      (136850833948171 / 100000) := by
  exact
    packedTile65536 1368414464 1368545536 14 6200 36992 30 _ _ (210369 / 10000) (2103693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368545536 :
    ThetaLowerSegment 1368545536 1368676608 (136850833948171 / 100000)
      (136863971554671 / 100000) := by
  exact
    packedTile65536 1368545536 1368676608 14 6245 36993 30 _ _ (21037 / 1000) (2103703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368676608 :
    ThetaLowerSegment 1368676608 1368807680 (136863971554671 / 100000)
      (136876978793601 / 100000) := by
  exact
    packedTile65536 1368676608 1368807680 14 6183 36995 30 _ _ (210371 / 10000) (2103713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368807680 :
    ThetaLowerSegment 1368807680 1368938752 (136876978793601 / 100000) (5475596330023 / 4000) := by
  exact
    packedTile65536 1368807680 1368938752 14 6146 36997 30 _ _ (2103719 / 100000) (1051861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368938752 :
    ThetaLowerSegment 1368938752 1369069824 (5475596330023 / 4000) (342257509909 / 250) := by
  exact
    packedTile65536 1368938752 1369069824 14 6225 36999 30 _ _ (2103729 / 100000) (525933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1369069824 :
    ThetaLowerSegment 1369069824 1369200896 (342257509909 / 250) (68458108770989 / 50000) := by
  exact
    packedTile65536 1369069824 1369200896 14 6281 37000 30 _ _ (1051869 / 50000) (2103741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1369200896 :
    ThetaLowerSegment 1369200896 1369331968 (68458108770989 / 50000) (68464674568497 / 50000) := by
  exact
    packedTile65536 1369200896 1369331968 14 6242 37002 30 _ _ (525937 / 25000) (2103751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1369331968 :
    ThetaLowerSegment 1369331968 1369463040 (68464674568497 / 50000) (34235590744449 / 25000) := by
  exact
    packedTile65536 1369331968 1369463040 14 6186 37004 30 _ _ (2103757 / 100000) (26297 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1369463040 :
    ThetaLowerSegment 1369463040 1369594112 (34235590744449 / 25000)
      (136955412644497 / 100000) := by
  exact
    packedTile65536 1369463040 1369594112 14 6203 37006 30 _ _ (2103767 / 100000) (210377 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1369594112 :
    ThetaLowerSegment 1369594112 1369725184 (136955412644497 / 100000)
      (68484271158377 / 50000) := by
  exact
    packedTile65536 1369594112 1369725184 14 6241 37008 30 _ _ (2103777 / 100000) (105189 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1369725184 :
    ThetaLowerSegment 1369725184 1369856256 (68484271158377 / 50000) (856135581769 / 625) := by
  exact
    packedTile65536 1369725184 1369856256 14 6251 37009 30 _ _ (1051893 / 50000) (2103789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1369856256 :
    ThetaLowerSegment 1369856256 1369987328 (856135581769 / 625) (34248704666571 / 25000) := by
  exact
    packedTile65536 1369856256 1369987328 14 6239 37011 30 _ _ (525949 / 25000) (2103799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1369987328 :
    ThetaLowerSegment 1369987328 1370118400 (34248704666571 / 25000)
      (137007809662159 / 100000) := by
  exact
    packedTile65536 1369987328 1370118400 14 6175 37013 30 _ _ (420761 / 20000) (65744 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1370118400 :
    ThetaLowerSegment 1370118400 1370249472 (137007809662159 / 100000)
      (137020958505909 / 100000) := by
  exact
    packedTile65536 1370118400 1370249472 14 6250 37015 30 _ _ (420763 / 20000) (1051909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1370249472 :
    ThetaLowerSegment 1370249472 1370380544 (137020958505909 / 100000)
      (137034092679141 / 100000) := by
  exact
    packedTile65536 1370249472 1370380544 14 6243 37016 30 _ _ (131489 / 6250) (2103827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1370380544 :
    ThetaLowerSegment 1370380544 1370511616 (137034092679141 / 100000)
      (137047279510653 / 100000) := by
  exact
    packedTile65536 1370380544 1370511616 14 6268 37018 30 _ _ (1051917 / 50000) (2103837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1370511616 :
    ThetaLowerSegment 1370511616 1370642688 (137047279510653 / 100000)
      (68530185862821 / 50000) := by
  exact
    packedTile65536 1370511616 1370642688 14 6223 37020 30 _ _ (2103843 / 100000) (1051923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1370642688 :
    ThetaLowerSegment 1370642688 1370773760 (68530185862821 / 50000) (5482945965677 / 4000) := by
  exact
    packedTile65536 1370642688 1370773760 14 6311 37022 30 _ _ (2103853 / 100000) (131491 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1370773760 :
    ThetaLowerSegment 1370773760 1370904832 (5482945965677 / 4000) (34271694837727 / 25000) := by
  exact
    packedTile65536 1370773760 1370904832 14 6241 37023 30 _ _ (2103863 / 100000) (1051933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1370904832 :
    ThetaLowerSegment 1370904832 1371035904 (34271694837727 / 25000) (34274960047071 / 25000) := by
  exact
    packedTile65536 1370904832 1371035904 14 6208 37025 30 _ _ (65746 / 3125) (16831 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1371035904 :
    ThetaLowerSegment 1371035904 1371166976 (34274960047071 / 25000) (34278265245693 / 25000) := by
  exact
    packedTile65536 1371035904 1371166976 14 6284 37027 30 _ _ (1051941 / 50000) (420777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1371166976 :
    ThetaLowerSegment 1371166976 1371298048 (34278265245693 / 25000) (4285193677443 / 3125) := by
  exact
    packedTile65536 1371166976 1371298048 14 6244 37029 30 _ _ (2103891 / 100000) (1051947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1371298048 :
    ThetaLowerSegment 1371298048 1371429120 (4285193677443 / 3125) (137139248176079 / 100000) := by
  exact
    packedTile65536 1371298048 1371429120 14 6203 37031 30 _ _ (2103901 / 100000) (65747 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1371429120 :
    ThetaLowerSegment 1371429120 1371560192 (137139248176079 / 100000)
      (137152277690709 / 100000) := by
  exact
    packedTile65536 1371429120 1371560192 14 6193 37032 30 _ _ (210391 / 10000) (2103913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1371560192 :
    ThetaLowerSegment 1371560192 1371691264 (137152277690709 / 100000)
      (137165391424069 / 100000) := by
  exact
    packedTile65536 1371560192 1371691264 14 6233 37034 30 _ _ (26299 / 1250) (2103923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1371691264 :
    ThetaLowerSegment 1371691264 1371822336 (137165391424069 / 100000)
      (137178496804039 / 100000) := by
  exact
    packedTile65536 1371691264 1371822336 14 6229 37036 30 _ _ (210393 / 10000) (2103933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1371822336 :
    ThetaLowerSegment 1371822336 1371953408 (137178496804039 / 100000)
      (68595733793987 / 50000) := by
  exact
    packedTile65536 1371822336 1371953408 14 6165 37038 30 _ _ (2103939 / 100000) (1051971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1371953408 :
    ThetaLowerSegment 1371953408 1372084480 (68595733793987 / 50000)
      (137204648828459 / 100000) := by
  exact
    packedTile65536 1371953408 1372084480 14 6265 37039 30 _ _ (2103949 / 100000) (131497 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1372084480 :
    ThetaLowerSegment 1372084480 1372215552 (137204648828459 / 100000)
      (137217743863051 / 100000) := by
  exact
    packedTile65536 1372084480 1372215552 14 6224 37041 30 _ _ (1051979 / 50000) (2103961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1372215552 :
    ThetaLowerSegment 1372215552 1372346624 (137217743863051 / 100000)
      (137230864207499 / 100000) := by
  exact
    packedTile65536 1372215552 1372346624 14 6236 37043 30 _ _ (65749 / 3125) (2103971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1372346624 :
    ThetaLowerSegment 1372346624 1372477696 (137230864207499 / 100000)
      (137243866785359 / 100000) := by
  exact
    packedTile65536 1372346624 1372477696 14 6180 37045 30 _ _ (2103977 / 100000) (105199 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1372477696 :
    ThetaLowerSegment 1372477696 1372608768 (137243866785359 / 100000)
      (34314235766141 / 25000) := by
  exact
    packedTile65536 1372477696 1372608768 14 6215 37046 30 _ _ (2103987 / 100000) (210399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1372608768 :
    ThetaLowerSegment 1372608768 1372739840 (34314235766141 / 25000) (34317550611839 / 25000) := by
  exact
    packedTile65536 1372608768 1372739840 14 6302 37048 30 _ _ (525999 / 25000) (2103999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1372739840 :
    ThetaLowerSegment 1372739840 1372870912 (34317550611839 / 25000) (68641681502443 / 50000) := by
  exact
    packedTile65536 1372739840 1372870912 14 6255 37050 30 _ _ (1052003 / 50000) (2104009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1372870912 :
    ThetaLowerSegment 1372870912 1373001984 (68641681502443 / 50000) (68648220781063 / 50000) := by
  exact
    packedTile65536 1372870912 1373001984 14 6216 37052 30 _ _ (420803 / 20000) (1052009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1373001984 :
    ThetaLowerSegment 1373001984 1373133056 (68648220781063 / 50000)
      (137309534909701 / 100000) := by
  exact
    packedTile65536 1373001984 1373133056 14 6223 37054 30 _ _ (84161 / 4000) (526007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1373133056 :
    ThetaLowerSegment 1373133056 1373264128 (137309534909701 / 100000)
      (137322542054071 / 100000) := by
  exact
    packedTile65536 1373133056 1373264128 14 6182 37055 30 _ _ (420807 / 20000) (1052019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1373264128 :
    ThetaLowerSegment 1373264128 1373395200 (137322542054071 / 100000)
      (137335576606651 / 100000) := by
  exact
    packedTile65536 1373264128 1373395200 14 6195 37057 30 _ _ (526011 / 25000) (2104047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1373395200 :
    ThetaLowerSegment 1373395200 1373526272 (137335576606651 / 100000)
      (137348657510369 / 100000) := by
  exact
    packedTile65536 1373395200 1373526272 14 6217 37059 30 _ _ (1052027 / 50000) (2104057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1373526272 :
    ThetaLowerSegment 1373526272 1373657344 (137348657510369 / 100000)
      (137361744782229 / 100000) := by
  exact
    packedTile65536 1373526272 1373657344 14 6220 37061 30 _ _ (2104063 / 100000) (1052033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1373657344 :
    ThetaLowerSegment 1373657344 1373788416 (137361744782229 / 100000)
      (137374848948873 / 100000) := by
  exact
    packedTile65536 1373657344 1373788416 14 6228 37062 30 _ _ (2104073 / 100000) (526019 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1373788416 :
    ThetaLowerSegment 1373788416 1373919488 (137374848948873 / 100000)
      (137388024710357 / 100000) := by
  exact
    packedTile65536 1373788416 1373919488 14 6262 37064 30 _ _ (1052041 / 50000) (420817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1373919488 :
    ThetaLowerSegment 1373919488 1374050560 (137388024710357 / 100000)
      (137401255240853 / 100000) := by
  exact
    packedTile65536 1373919488 1374050560 14 6288 37066 30 _ _ (526023 / 25000) (420819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374050560 :
    ThetaLowerSegment 1374050560 1374181632 (137401255240853 / 100000)
      (137414233335821 / 100000) := by
  exact
    packedTile65536 1374050560 1374181632 14 6168 37068 30 _ _ (2104101 / 100000) (263013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374181632 :
    ThetaLowerSegment 1374181632 1374312704 (137414233335821 / 100000)
      (68713672025731 / 50000) := by
  exact
    packedTile65536 1374181632 1374312704 14 6231 37069 30 _ _ (2104111 / 100000) (1052057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374312704 :
    ThetaLowerSegment 1374312704 1374443776 (68713672025731 / 50000) (68720238984251 / 50000) := by
  exact
    packedTile65536 1374312704 1374443776 14 6242 37071 30 _ _ (52603 / 2500) (2104123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374443776 :
    ThetaLowerSegment 1374443776 1374574848 (68720238984251 / 50000) (34363336180863 / 25000) := by
  exact
    packedTile65536 1374443776 1374574848 14 6115 37073 30 _ _ (210413 / 10000) (2104133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374574848 :
    ThetaLowerSegment 1374574848 1374705920 (34363336180863 / 25000) (8591647163817 / 6250) := by
  exact
    packedTile65536 1374574848 1374705920 14 6183 37075 30 _ _ (105207 / 5000) (2104143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374705920 :
    ThetaLowerSegment 1374705920 1374836992 (8591647163817 / 6250) (137479389824127 / 100000) := by
  exact
    packedTile65536 1374705920 1374836992 14 6195 37077 30 _ _ (2104149 / 100000) (263019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374836992 :
    ThetaLowerSegment 1374836992 1374968064 (137479389824127 / 100000)
      (137492616567601 / 100000) := by
  exact
    packedTile65536 1374836992 1374968064 14 6286 37078 30 _ _ (2104159 / 100000) (1052081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374968064 :
    ThetaLowerSegment 1374968064 1375099136 (137492616567601 / 100000)
      (137505681346713 / 100000) := by
  exact
    packedTile65536 1374968064 1375099136 14 6209 37080 30 _ _ (263021 / 12500) (2104171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1375099136 :
    ThetaLowerSegment 1375099136 1375230208 (137505681346713 / 100000)
      (137518771438051 / 100000) := by
  exact
    packedTile65536 1375099136 1375230208 14 6221 37082 30 _ _ (1052089 / 50000) (2104181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1375230208 :
    ThetaLowerSegment 1375230208 1375361280 (137518771438051 / 100000)
      (68765846625209 / 50000) := by
  exact
    packedTile65536 1375230208 1375361280 14 6141 37084 30 _ _ (2104187 / 100000) (210419 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1375361280 :
    ThetaLowerSegment 1375361280 1375492352 (68765846625209 / 50000) (68772436970213 / 50000) := by
  exact
    packedTile65536 1375361280 1375492352 14 6264 37085 30 _ _ (2104197 / 100000) (10521 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1375492352 :
    ThetaLowerSegment 1375492352 1375623424 (68772436970213 / 50000) (8597375919181 / 6250) := by
  exact
    packedTile65536 1375492352 1375623424 14 6245 37087 30 _ _ (1052103 / 50000) (2104209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1375623424 :
    ThetaLowerSegment 1375623424 1375754496 (8597375919181 / 6250) (4299094730846 / 3125) := by
  exact
    packedTile65536 1375623424 1375754496 14 6186 37089 30 _ _ (263027 / 12500) (2104219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1375754496 :
    ThetaLowerSegment 1375754496 1375885568 (4299094730846 / 3125) (8599012213667 / 6250) := by
  exact
    packedTile65536 1375754496 1375885568 14 6256 37091 30 _ _ (84169 / 4000) (526057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1375885568 :
    ThetaLowerSegment 1375885568 1376016640 (8599012213667 / 6250) (137597226946027 / 100000) := by
  exact
    packedTile65536 1375885568 1376016640 14 6193 37092 30 _ _ (420847 / 20000) (1052119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376016640 :
    ThetaLowerSegment 1376016640 1376147712 (137597226946027 / 100000)
      (137610464745031 / 100000) := by
  exact
    packedTile65536 1376016640 1376147712 14 6291 37094 30 _ _ (526061 / 25000) (2104247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376147712 :
    ThetaLowerSegment 1376147712 1376278784 (137610464745031 / 100000)
      (27524772085199 / 20000) := by
  exact
    packedTile65536 1376147712 1376278784 14 6366 37096 30 _ _ (1052127 / 50000) (2104257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376278784 :
    ThetaLowerSegment 1376278784 1376409856 (27524772085199 / 20000) (68818420812221 / 50000) := by
  exact
    packedTile65536 1376278784 1376409856 14 6169 37098 30 _ _ (2104263 / 100000) (1052133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376409856 :
    ThetaLowerSegment 1376409856 1376540928 (68818420812221 / 50000)
      (137649928098229 / 100000) := by
  exact
    packedTile65536 1376409856 1376540928 14 6219 37099 30 _ _ (2104273 / 100000) (526069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376540928 :
    ThetaLowerSegment 1376540928 1376672000 (137649928098229 / 100000)
      (137663060922191 / 100000) := by
  exact
    packedTile65536 1376540928 1376672000 14 6241 37101 30 _ _ (1052141 / 50000) (420857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376672000 :
    ThetaLowerSegment 1376672000 1376803072 (137663060922191 / 100000)
      (27535216035359 / 20000) := by
  exact
    packedTile65536 1376672000 1376803072 14 6187 37103 30 _ _ (526073 / 25000) (420859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376803072 :
    ThetaLowerSegment 1376803072 1376934144 (27535216035359 / 20000) (27537835891349 / 20000) := by
  exact
    packedTile65536 1376803072 1376934144 14 6225 37105 30 _ _ (1052151 / 50000) (420861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376934144 :
    ThetaLowerSegment 1376934144 1377065216 (27537835891349 / 20000) (68851166752403 / 50000) := by
  exact
    packedTile65536 1376934144 1377065216 14 6251 37107 30 _ _ (2104311 / 100000) (1052157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1377065216 :
    ThetaLowerSegment 1377065216 1377196288 (68851166752403 / 50000) (34428797726529 / 25000) := by
  exact
    packedTile65536 1377065216 1377196288 14 6110 37108 30 _ _ (2104321 / 100000) (526081 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1377196288 :
    ThetaLowerSegment 1377196288 1377327360 (34428797726529 / 25000) (68864145180183 / 50000) := by
  exact
    packedTile65536 1377196288 1377327360 14 6225 37110 30 _ _ (210433 / 10000) (2104333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1377327360 :
    ThetaLowerSegment 1377327360 1377458432 (68864145180183 / 50000) (68870770694673 / 50000) := by
  exact
    packedTile65536 1377327360 1377458432 14 6297 37112 30 _ _ (105217 / 5000) (2104343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1377458432 :
    ThetaLowerSegment 1377458432 1377589504 (68870770694673 / 50000)
      (137754565205307 / 100000) := by
  exact
    packedTile65536 1377458432 1377589504 14 6189 37114 30 _ _ (2104349 / 100000) (65761 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1377589504 :
    ThetaLowerSegment 1377589504 1377720576 (137754565205307 / 100000) (2755351276617 / 2000) := by
  exact
    packedTile65536 1377589504 1377720576 14 6177 37115 30 _ _ (2104359 / 100000) (1052181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1377720576 :
    ThetaLowerSegment 1377720576 1377851648 (2755351276617 / 2000) (68890341230481 / 50000) := by
  exact
    packedTile65536 1377720576 1377851648 14 6234 37117 30 _ _ (131523 / 6250) (2104371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1377851648 :
    ThetaLowerSegment 1377851648 1377982720 (68890341230481 / 50000) (4306053195239 / 3125) := by
  exact
    packedTile65536 1377851648 1377982720 14 6187 37119 30 _ _ (1052189 / 50000) (2104381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1377982720 :
    ThetaLowerSegment 1377982720 1378113792 (4306053195239 / 3125) (68903246355917 / 50000) := by
  exact
    packedTile65536 1377982720 1378113792 14 6078 37121 30 _ _ (2104387 / 100000) (210439 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1378113792 :
    ThetaLowerSegment 1378113792 1378244864 (68903246355917 / 50000)
      (137819706220597 / 100000) := by
  exact
    packedTile65536 1378113792 1378244864 14 6279 37122 30 _ _ (2104397 / 100000) (5261 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1378244864 :
    ThetaLowerSegment 1378244864 1378375936 (137819706220597 / 100000)
      (27566554074609 / 20000) := by
  exact
    packedTile65536 1378244864 1378375936 14 6208 37124 30 _ _ (1052203 / 50000) (2104409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1378375936 :
    ThetaLowerSegment 1378375936 1378507008 (27566554074609 / 20000) (5513833130973 / 4000) := by
  exact
    packedTile65536 1378375936 1378507008 14 6205 37126 30 _ _ (65763 / 3125) (2104419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1378507008 :
    ThetaLowerSegment 1378507008 1378638080 (5513833130973 / 4000) (5514360415701 / 4000) := by
  exact
    packedTile65536 1378507008 1378638080 14 6264 37128 30 _ _ (84177 / 4000) (526107 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1378638080 :
    ThetaLowerSegment 1378638080 1378769152 (5514360415701 / 4000) (27574425046289 / 20000) := by
  exact
    packedTile65536 1378638080 1378769152 14 6232 37130 30 _ _ (420887 / 20000) (1052219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1378769152 :
    ThetaLowerSegment 1378769152 1378900224 (27574425046289 / 20000)
      (137885366393093 / 100000) := by
  exact
    packedTile65536 1378769152 1378900224 14 6292 37131 30 _ _ (526111 / 25000) (2104447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1378900224 :
    ThetaLowerSegment 1378900224 1379031296 (137885366393093 / 100000)
      (27579660915257 / 20000) := by
  exact
    packedTile65536 1378900224 1379031296 14 6148 37133 30 _ _ (1052227 / 50000) (2104457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1379031296 :
    ThetaLowerSegment 1379031296 1379162368 (27579660915257 / 20000) (27582274658303 / 20000) := by
  exact
    packedTile65536 1379031296 1379162368 14 6210 37135 30 _ _ (2104463 / 100000) (1052233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1379162368 :
    ThetaLowerSegment 1379162368 1379293440 (27582274658303 / 20000)
      (137924551501441 / 100000) := by
  exact
    packedTile65536 1379162368 1379293440 14 6262 37137 30 _ _ (2104473 / 100000) (526119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1379293440 :
    ThetaLowerSegment 1379293440 1379424512 (137924551501441 / 100000)
      (137937805529077 / 100000) := by
  exact
    packedTile65536 1379293440 1379424512 14 6298 37138 30 _ _ (1052241 / 50000) (420897 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1379424512 :
    ThetaLowerSegment 1379424512 1379555584 (137937805529077 / 100000)
      (137950804976161 / 100000) := by
  exact
    packedTile65536 1379424512 1379555584 14 6177 37140 30 _ _ (526123 / 25000) (420899 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1379555584 :
    ThetaLowerSegment 1379555584 1379686656 (137950804976161 / 100000)
      (137963928644397 / 100000) := by
  exact
    packedTile65536 1379555584 1379686656 14 6236 37142 30 _ _ (2104501 / 100000) (263063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1379686656 :
    ThetaLowerSegment 1379686656 1379817728 (137963928644397 / 100000)
      (137977022911839 / 100000) := by
  exact
    packedTile65536 1379686656 1379817728 14 6222 37144 30 _ _ (2104511 / 100000) (1052257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1379817728 :
    ThetaLowerSegment 1379817728 1379948800 (137977022911839 / 100000)
      (137990176161839 / 100000) := by
  exact
    packedTile65536 1379817728 1379948800 14 6250 37145 30 _ _ (52613 / 2500) (2104523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1379948800 :
    ThetaLowerSegment 1379948800 1380079872 (137990176161839 / 100000)
      (138003453641609 / 100000) := by
  exact
    packedTile65536 1379948800 1380079872 14 6309 37147 30 _ _ (210453 / 10000) (2104533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380079872 :
    ThetaLowerSegment 1380079872 1380210944 (138003453641609 / 100000)
      (138016619637593 / 100000) := by
  exact
    packedTile65536 1380079872 1380210944 14 6256 37149 30 _ _ (2104539 / 100000) (1052271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380210944 :
    ThetaLowerSegment 1380210944 1380342016 (138016619637593 / 100000)
      (27605924308263 / 20000) := by
  exact
    packedTile65536 1380210944 1380342016 14 6178 37151 30 _ _ (2104549 / 100000) (263069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380342016 :
    ThetaLowerSegment 1380342016 1380473088 (27605924308263 / 20000)
      (138042518272739 / 100000) := by
  exact
    packedTile65536 1380342016 1380473088 14 6128 37152 30 _ _ (1052279 / 50000) (2104561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380473088 :
    ThetaLowerSegment 1380473088 1380604160 (138042518272739 / 100000)
      (138055568698907 / 100000) := by
  exact
    packedTile65536 1380473088 1380604160 14 6201 37154 30 _ _ (263071 / 12500) (2104571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380604160 :
    ThetaLowerSegment 1380604160 1380735232 (138055568698907 / 100000) (5522747545277 / 4000) := by
  exact
    packedTile65536 1380604160 1380735232 14 6234 37156 30 _ _ (2104577 / 100000) (105229 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380735232 :
    ThetaLowerSegment 1380735232 1380866304 (5522747545277 / 4000) (138081808627283 / 100000) := by
  exact
    packedTile65536 1380735232 1380866304 14 6234 37158 30 _ _ (2104587 / 100000) (210459 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380866304 :
    ThetaLowerSegment 1380866304 1380997376 (138081808627283 / 100000) (1104760153411 / 800) := by
  exact
    packedTile65536 1380866304 1380997376 14 6277 37160 30 _ _ (526149 / 25000) (2104599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380997376 :
    ThetaLowerSegment 1380997376 1381128448 (1104760153411 / 800) (138108196114541 / 100000) := by
  exact
    packedTile65536 1380997376 1381128448 14 6261 37161 30 _ _ (1052303 / 50000) (2104609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1381128448 :
    ThetaLowerSegment 1381128448 1381259520 (138108196114541 / 100000)
      (17265161115557 / 12500) := by
  exact
    packedTile65536 1381128448 1381259520 14 6221 37163 30 _ _ (420923 / 20000) (1052309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1381259520 :
    ThetaLowerSegment 1381259520 1381390592 (17265161115557 / 12500)
      (138134306030081 / 100000) := by
  exact
    packedTile65536 1381259520 1381390592 14 6185 37165 30 _ _ (16837 / 800) (526157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1381390592 :
    ThetaLowerSegment 1381390592 1381521664 (138134306030081 / 100000)
      (138147426318437 / 100000) := by
  exact
    packedTile65536 1381390592 1381521664 14 6234 37167 30 _ _ (1052317 / 50000) (2104637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1381521664 :
    ThetaLowerSegment 1381521664 1381652736 (138147426318437 / 100000)
      (138160534041269 / 100000) := by
  exact
    packedTile65536 1381521664 1381652736 14 6228 37168 30 _ _ (526161 / 25000) (2104647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1381652736 :
    ThetaLowerSegment 1381652736 1381783808 (138160534041269 / 100000)
      (138173620773623 / 100000) := by
  exact
    packedTile65536 1381652736 1381783808 14 6218 37170 30 _ _ (2104653 / 100000) (131541 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1381783808 :
    ThetaLowerSegment 1381783808 1381914880 (138173620773623 / 100000)
      (138186766498721 / 100000) := by
  exact
    packedTile65536 1381783808 1381914880 14 6246 37172 30 _ _ (2104663 / 100000) (1052333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1381914880 :
    ThetaLowerSegment 1381914880 1382045952 (138186766498721 / 100000)
      (138199969106177 / 100000) := by
  exact
    packedTile65536 1381914880 1382045952 14 6273 37174 30 _ _ (65771 / 3125) (84187 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1382045952 :
    ThetaLowerSegment 1382045952 1382177024 (138199969106177 / 100000)
      (138213001297121 / 100000) := by
  exact
    packedTile65536 1382045952 1382177024 14 6192 37175 30 _ _ (1052341 / 50000) (420937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1382177024 :
    ThetaLowerSegment 1382177024 1382308096 (138213001297121 / 100000)
      (138226159825253 / 100000) := by
  exact
    packedTile65536 1382177024 1382308096 14 6252 37177 30 _ _ (2104691 / 100000) (1052347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1382308096 :
    ThetaLowerSegment 1382308096 1382439168 (138226159825253 / 100000)
      (27647901567799 / 20000) := by
  exact
    packedTile65536 1382308096 1382439168 14 6342 37179 30 _ _ (2104701 / 100000) (65772 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1382439168 :
    ThetaLowerSegment 1382439168 1382570240 (27647901567799 / 20000) (1106021769667 / 800) := by
  exact
    packedTile65536 1382439168 1382570240 14 6278 37181 30 _ _ (210471 / 10000) (2104713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1382570240 :
    ThetaLowerSegment 1382570240 1382701312 (1106021769667 / 800) (27653155778251 / 20000) := by
  exact
    packedTile65536 1382570240 1382701312 14 6204 37182 30 _ _ (26309 / 1250) (2104723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1382701312 :
    ThetaLowerSegment 1382701312 1382832384 (27653155778251 / 20000)
      (138278794535391 / 100000) := by
  exact
    packedTile65536 1382701312 1382832384 14 6184 37184 30 _ _ (2104729 / 100000) (526183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1382832384 :
    ThetaLowerSegment 1382832384 1382963456 (138278794535391 / 100000)
      (138291928100511 / 100000) := by
  exact
    packedTile65536 1382832384 1382963456 14 6240 37186 30 _ _ (1052369 / 50000) (2104741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1382963456 :
    ThetaLowerSegment 1382963456 1383094528 (138291928100511 / 100000)
      (138305065937527 / 100000) := by
  exact
    packedTile65536 1382963456 1383094528 14 6242 37188 30 _ _ (526187 / 25000) (2104751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1383094528 :
    ThetaLowerSegment 1383094528 1383225600 (138305065937527 / 100000)
      (138318115430927 / 100000) := by
  exact
    packedTile65536 1383094528 1383225600 14 6200 37189 30 _ _ (2104757 / 100000) (52619 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1383225600 :
    ThetaLowerSegment 1383225600 1383356672 (138318115430927 / 100000)
      (69165629850421 / 50000) := by
  exact
    packedTile65536 1383225600 1383356672 14 6245 37191 30 _ _ (2104767 / 100000) (210477 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1383356672 :
    ThetaLowerSegment 1383356672 1383487744 (69165629850421 / 50000) (69172149394081 / 50000) := by
  exact
    packedTile65536 1383356672 1383487744 14 6195 37193 30 _ _ (263097 / 12500) (2104779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1383487744 :
    ThetaLowerSegment 1383487744 1383618816 (69172149394081 / 50000) (6917866686393 / 5000) := by
  exact
    packedTile65536 1383487744 1383618816 14 6193 37195 30 _ _ (1052393 / 50000) (2104789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1383618816 :
    ThetaLowerSegment 1383618816 1383749888 (6917866686393 / 5000) (13837037082809 / 10000) := by
  exact
    packedTile65536 1383618816 1383749888 14 6194 37197 30 _ _ (420959 / 20000) (1052399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1383749888 :
    ThetaLowerSegment 1383749888 1383880960 (13837037082809 / 10000) (27676671915949 / 20000) := by
  exact
    packedTile65536 1383749888 1383880960 14 6171 37198 30 _ _ (420961 / 20000) (263101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1383880960 :
    ThetaLowerSegment 1383880960 1384012032 (27676671915949 / 20000)
      (138396422055429 / 100000) := by
  exact
    packedTile65536 1383880960 1384012032 14 6206 37200 30 _ _ (1052407 / 50000) (2104817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384012032 :
    ThetaLowerSegment 1384012032 1384143104 (138396422055429 / 100000)
      (138409570890957 / 100000) := by
  exact
    packedTile65536 1384012032 1384143104 14 6247 37202 30 _ _ (263103 / 12500) (2104827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384143104 :
    ThetaLowerSegment 1384143104 1384274176 (138409570890957 / 100000)
      (27684518277579 / 20000) := by
  exact
    packedTile65536 1384143104 1384274176 14 6186 37204 30 _ _ (2104833 / 100000) (526209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384274176 :
    ThetaLowerSegment 1384274176 1384405248 (27684518277579 / 20000) (34608943504901 / 25000) := by
  exact
    packedTile65536 1384274176 1384405248 14 6263 37205 30 _ _ (2104843 / 100000) (1052423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384405248 :
    ThetaLowerSegment 1384405248 1384536320 (34608943504901 / 25000) (1384488198923 / 1000) := by
  exact
    packedTile65536 1384405248 1384536320 14 6198 37207 30 _ _ (526213 / 25000) (420971 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384536320 :
    ThetaLowerSegment 1384536320 1384667392 (1384488198923 / 1000) (6923097711559 / 5000) := by
  exact
    packedTile65536 1384536320 1384667392 14 6240 37209 30 _ _ (1052431 / 50000) (420973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384667392 :
    ThetaLowerSegment 1384667392 1384798464 (6923097711559 / 5000) (138475044423929 / 100000) := by
  exact
    packedTile65536 1384667392 1384798464 14 6219 37211 30 _ _ (2104871 / 100000) (1052437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384798464 :
    ThetaLowerSegment 1384798464 1384929536 (138475044423929 / 100000)
      (13848805469339 / 10000) := by
  exact
    packedTile65536 1384798464 1384929536 14 6181 37212 30 _ _ (2104881 / 100000) (526221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384929536 :
    ThetaLowerSegment 1384929536 1385060608 (13848805469339 / 10000) (2770023531553 / 2000) := by
  exact
    packedTile65536 1384929536 1385060608 14 6234 37214 30 _ _ (210489 / 10000) (2104893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385060608 :
    ThetaLowerSegment 1385060608 1385191680 (2770023531553 / 2000) (17314306258843 / 12500) := by
  exact
    packedTile65536 1385060608 1385191680 14 6306 37216 30 _ _ (2104899 / 100000) (1052451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385191680 :
    ThetaLowerSegment 1385191680 1385322752 (17314306258843 / 12500) (13852761417163 / 10000) := by
  exact
    packedTile65536 1385191680 1385322752 14 6254 37218 30 _ _ (2104909 / 100000) (131557 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385322752 :
    ThetaLowerSegment 1385322752 1385339136 (13852761417163 / 10000) (34632308213393 / 25000) := by
  exact
    packedTile65536 1385322752 1385339136 11 769 37219 30 _ _ (1052459 / 50000) (2104921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1385339136 :
    ThetaLowerSegment 1385339136 1385341184 (34632308213393 / 25000) (34632366098693 / 25000) := by
  exact
    packedTile65536 1385339136 1385341184 8 110 37220 30 _ _ (52623 / 2500) (2104923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1353341184_1385341184 :
    ThetaLowerSegment 1353341184 1385341184 (135329374024609 / 100000)
      (34632366098693 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1353341184 cell1353472256)
                  (ThetaLowerSegment.join cell1353603328 cell1353734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1353865472 cell1353996544)
                  (ThetaLowerSegment.join cell1354127616 cell1354258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1354389760 cell1354520832)
                  (ThetaLowerSegment.join cell1354651904 cell1354782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1354914048 cell1355045120)
                  (ThetaLowerSegment.join cell1355176192 cell1355307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1355438336 cell1355569408)
                  (ThetaLowerSegment.join cell1355700480 cell1355831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1355962624 cell1356093696)
                  (ThetaLowerSegment.join cell1356224768 cell1356355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1356486912 cell1356617984)
                  (ThetaLowerSegment.join cell1356749056 cell1356880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1357011200 cell1357142272)
                  (ThetaLowerSegment.join cell1357273344 cell1357404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1357535488 cell1357666560)
                  (ThetaLowerSegment.join cell1357797632 cell1357928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1358059776 cell1358190848)
                  (ThetaLowerSegment.join cell1358321920 cell1358452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1358584064 cell1358715136)
                  (ThetaLowerSegment.join cell1358846208 cell1358977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1359108352 cell1359239424)
                  (ThetaLowerSegment.join cell1359370496 cell1359501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1359632640 cell1359763712)
                  (ThetaLowerSegment.join cell1359894784 cell1360025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1360156928 cell1360288000)
                  (ThetaLowerSegment.join cell1360419072 cell1360550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1360681216 cell1360812288)
                  (ThetaLowerSegment.join cell1360943360 cell1361074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1361205504 cell1361336576)
                  (ThetaLowerSegment.join cell1361467648 cell1361598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1361729792 cell1361860864)
                  (ThetaLowerSegment.join cell1361991936 cell1362123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1362254080 cell1362385152)
                  (ThetaLowerSegment.join cell1362516224 cell1362647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1362778368 cell1362909440)
                  (ThetaLowerSegment.join cell1363040512 cell1363171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1363302656 cell1363433728)
                  (ThetaLowerSegment.join cell1363564800 cell1363695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1363826944 cell1363958016)
                  (ThetaLowerSegment.join cell1364089088 cell1364220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1364351232 cell1364482304)
                  (ThetaLowerSegment.join cell1364613376 cell1364744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1364875520 cell1365006592)
                  (ThetaLowerSegment.join cell1365137664 cell1365268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1365399808 cell1365530880)
                  (ThetaLowerSegment.join cell1365661952 cell1365793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1365924096 cell1366055168)
                  (ThetaLowerSegment.join cell1366186240 cell1366317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1366448384 cell1366579456)
                  (ThetaLowerSegment.join cell1366710528 cell1366841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1366972672 cell1367103744)
                  (ThetaLowerSegment.join cell1367234816 cell1367365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1367496960 cell1367628032)
                  (ThetaLowerSegment.join cell1367759104 cell1367890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1368021248 cell1368152320)
                  (ThetaLowerSegment.join cell1368283392 cell1368414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1368545536 cell1368676608)
                  (ThetaLowerSegment.join cell1368807680 cell1368938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1369069824 cell1369200896)
                  (ThetaLowerSegment.join cell1369331968 cell1369463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1369594112 cell1369725184)
                  (ThetaLowerSegment.join cell1369856256 cell1369987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1370118400 cell1370249472)
                  (ThetaLowerSegment.join cell1370380544 cell1370511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1370642688 cell1370773760)
                  (ThetaLowerSegment.join cell1370904832 cell1371035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1371166976 cell1371298048)
                  (ThetaLowerSegment.join cell1371429120 cell1371560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1371691264 cell1371822336)
                  (ThetaLowerSegment.join cell1371953408 cell1372084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1372215552 cell1372346624)
                  (ThetaLowerSegment.join cell1372477696 cell1372608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1372739840 cell1372870912)
                  (ThetaLowerSegment.join cell1373001984 cell1373133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1373264128 cell1373395200)
                  (ThetaLowerSegment.join cell1373526272 cell1373657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1373788416 cell1373919488)
                  (ThetaLowerSegment.join cell1374050560 cell1374181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1374312704 cell1374443776)
                  (ThetaLowerSegment.join cell1374574848 cell1374705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1374836992 cell1374968064)
                  (ThetaLowerSegment.join cell1375099136 cell1375230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1375361280 cell1375492352)
                  (ThetaLowerSegment.join cell1375623424 cell1375754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1375885568 cell1376016640)
                  (ThetaLowerSegment.join cell1376147712 cell1376278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1376409856 cell1376540928)
                  (ThetaLowerSegment.join cell1376672000 cell1376803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1376934144 cell1377065216)
                  (ThetaLowerSegment.join cell1377196288 cell1377327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1377458432 cell1377589504)
                  (ThetaLowerSegment.join cell1377720576 cell1377851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1377982720 cell1378113792)
                  (ThetaLowerSegment.join cell1378244864 cell1378375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1378507008 cell1378638080)
                  (ThetaLowerSegment.join cell1378769152 cell1378900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1379031296 cell1379162368)
                  (ThetaLowerSegment.join cell1379293440 cell1379424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1379555584 cell1379686656)
                  (ThetaLowerSegment.join cell1379817728 cell1379948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1380079872 cell1380210944)
                  (ThetaLowerSegment.join cell1380342016 cell1380473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1380604160 cell1380735232)
                  (ThetaLowerSegment.join cell1380866304 cell1380997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1381128448 cell1381259520)
                  (ThetaLowerSegment.join cell1381390592 cell1381521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1381652736 cell1381783808)
                  (ThetaLowerSegment.join cell1381914880 cell1382045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1382177024 cell1382308096)
                  (ThetaLowerSegment.join cell1382439168 cell1382570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1382701312 cell1382832384)
                  (ThetaLowerSegment.join cell1382963456 cell1383094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1383225600 cell1383356672)
                  (ThetaLowerSegment.join cell1383487744 cell1383618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1383749888 cell1383880960)
                  (ThetaLowerSegment.join cell1384012032 cell1384143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1384274176 cell1384405248)
                  (ThetaLowerSegment.join cell1384536320 cell1384667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1384798464 cell1384929536)
                (ThetaLowerSegment.join cell1385060608 cell1385191680))
              (ThetaLowerSegment.join cell1385322752 cell1385339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
