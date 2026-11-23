/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2025341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1993341184 :
    ThetaLowerSegment 1993341184 1993472256 (99663955798939 / 50000) (99670506053993 / 50000) := by
  exact
    packedTile65536 1993341184 1993472256 14 6118 44646 31 _ _ (1070653 / 50000) (2141309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993472256 :
    ThetaLowerSegment 1993472256 1993603328 (99670506053993 / 50000)
      (199354196172127 / 100000) := by
  exact
    packedTile65536 1993472256 1993603328 14 6157 44648 31 _ _ (2141313 / 100000) (535329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993603328 :
    ThetaLowerSegment 1993603328 1993734400 (199354196172127 / 100000)
      (19936746592597 / 10000) := by
  exact
    packedTile65536 1993603328 1993734400 14 6197 44649 31 _ _ (2141319 / 100000) (1070661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993734400 :
    ThetaLowerSegment 1993734400 1993865472 (19936746592597 / 10000) (99690255441981 / 50000) := by
  exact
    packedTile65536 1993734400 1993865472 14 6092 44651 31 _ _ (1070663 / 50000) (2141329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993865472 :
    ThetaLowerSegment 1993865472 1993996544 (99690255441981 / 50000)
      (199393528047269 / 100000) := by
  exact
    packedTile65536 1993865472 1993996544 14 6079 44652 31 _ _ (2141333 / 100000) (267667 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993996544 :
    ThetaLowerSegment 1993996544 1994127616 (199393528047269 / 100000)
      (199406645889983 / 100000) := by
  exact
    packedTile65536 1993996544 1994127616 14 6126 44654 31 _ _ (2141339 / 100000) (1070671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1994127616 :
    ThetaLowerSegment 1994127616 1994258688 (199406645889983 / 100000)
      (199419832298651 / 100000) := by
  exact
    packedTile65536 1994127616 1994258688 14 6158 44655 31 _ _ (1070673 / 50000) (2141349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1994258688 :
    ThetaLowerSegment 1994258688 1994389760 (199419832298651 / 100000)
      (199432928807483 / 100000) := by
  exact
    packedTile65536 1994258688 1994389760 14 6116 44657 31 _ _ (267669 / 12500) (428271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1994389760 :
    ThetaLowerSegment 1994389760 1994520832 (199432928807483 / 100000) (199446126003 / 100) := by
  exact
    packedTile65536 1994389760 1994520832 14 6163 44658 31 _ _ (2141359 / 100000) (1070681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1994520832 :
    ThetaLowerSegment 1994520832 1994651904 (199446126003 / 100) (4986483776831 / 2500) := by
  exact
    packedTile65536 1994520832 1994651904 14 6176 44660 31 _ _ (428273 / 20000) (267671 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1994651904 :
    ThetaLowerSegment 1994651904 1994782976 (4986483776831 / 2500) (49868107108011 / 25000) := by
  exact
    packedTile65536 1994651904 1994782976 14 6107 44661 31 _ _ (535343 / 25000) (17131 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1994782976 :
    ThetaLowerSegment 1994782976 1994914048 (49868107108011 / 25000) (6233924265597 / 3125) := by
  exact
    packedTile65536 1994782976 1994914048 14 6140 44662 31 _ _ (2141379 / 100000) (1070691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1994914048 :
    ThetaLowerSegment 1994914048 1995045120 (6233924265597 / 3125) (199498589695749 / 100000) := by
  exact
    packedTile65536 1994914048 1995045120 14 6077 44664 31 _ _ (428277 / 20000) (535347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1995045120 :
    ThetaLowerSegment 1995045120 1995176192 (199498589695749 / 100000)
      (199511748549589 / 100000) := by
  exact
    packedTile65536 1995045120 1995176192 14 6145 44665 31 _ _ (133837 / 6250) (428279 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1995176192 :
    ThetaLowerSegment 1995176192 1995307264 (199511748549589 / 100000)
      (199524798229001 / 100000) := by
  exact
    packedTile65536 1995176192 1995307264 14 6094 44667 31 _ _ (1070699 / 50000) (2141401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1995307264 :
    ThetaLowerSegment 1995307264 1995438336 (199524798229001 / 100000)
      (199537882213551 / 100000) := by
  exact
    packedTile65536 1995307264 1995438336 14 6110 44668 31 _ _ (428281 / 20000) (66919 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1995438336 :
    ThetaLowerSegment 1995438336 1995569408 (199537882213551 / 100000)
      (199550979083227 / 100000) := by
  exact
    packedTile65536 1995438336 1995569408 14 6116 44670 31 _ _ (2141411 / 100000) (1070707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1995569408 :
    ThetaLowerSegment 1995569408 1995700480 (199550979083227 / 100000)
      (199563855429661 / 100000) := by
  exact
    packedTile65536 1995569408 1995700480 14 6013 44671 31 _ _ (1070709 / 50000) (2141421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1995700480 :
    ThetaLowerSegment 1995700480 1995831552 (199563855429661 / 100000)
      (199577025193411 / 100000) := by
  exact
    packedTile65536 1995700480 1995831552 14 6150 44673 31 _ _ (85657 / 4000) (535357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1995831552 :
    ThetaLowerSegment 1995831552 1995962624 (199577025193411 / 100000)
      (39918044994819 / 20000) := by
  exact
    packedTile65536 1995831552 1995962624 14 6164 44674 31 _ _ (2141431 / 100000) (1070717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1995962624 :
    ThetaLowerSegment 1995962624 1996093696 (39918044994819 / 20000)
      (199603232068507 / 100000) := by
  exact
    packedTile65536 1995962624 1996093696 14 6074 44676 31 _ _ (1070719 / 50000) (2141441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1996093696 :
    ThetaLowerSegment 1996093696 1996224768 (199603232068507 / 100000)
      (199616404090551 / 100000) := by
  exact
    packedTile65536 1996093696 1996224768 14 6151 44677 31 _ _ (535361 / 25000) (2141447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1996224768 :
    ThetaLowerSegment 1996224768 1996355840 (199616404090551 / 100000)
      (99814863028611 / 50000) := by
  exact
    packedTile65536 1996224768 1996355840 14 6221 44679 31 _ _ (2141451 / 100000) (1070727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1996355840 :
    ThetaLowerSegment 1996355840 1996486912 (99814863028611 / 50000)
      (199642654033131 / 100000) := by
  exact
    packedTile65536 1996355840 1996486912 14 6037 44680 31 _ _ (2141457 / 100000) (107073 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1996486912 :
    ThetaLowerSegment 1996486912 1996617984 (199642654033131 / 100000)
      (199655575626907 / 100000) := by
  exact
    packedTile65536 1996486912 1996617984 14 6034 44682 31 _ _ (267683 / 12500) (2141467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1996617984 :
    ThetaLowerSegment 1996617984 1996749056 (199655575626907 / 100000)
      (49917148407279 / 25000) := by
  exact
    packedTile65536 1996617984 1996749056 14 6079 44683 31 _ _ (2141471 / 100000) (1070737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1996749056 :
    ThetaLowerSegment 1996749056 1996880128 (49917148407279 / 25000) (39936334325831 / 20000) := by
  exact
    packedTile65536 1996749056 1996880128 14 6107 44684 31 _ _ (2141477 / 100000) (53537 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1996880128 :
    ThetaLowerSegment 1996880128 1997011200 (39936334325831 / 20000)
      (199694666154067 / 100000) := by
  exact
    packedTile65536 1996880128 1997011200 14 6068 44686 31 _ _ (535371 / 25000) (2141487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997011200 :
    ThetaLowerSegment 1997011200 1997142272 (199694666154067 / 100000)
      (199707677847307 / 100000) := by
  exact
    packedTile65536 1997011200 1997142272 14 6076 44687 31 _ _ (214149 / 10000) (2141493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997142272 :
    ThetaLowerSegment 1997142272 1997273344 (199707677847307 / 100000)
      (99860506474563 / 50000) := by
  exact
    packedTile65536 1997142272 1997273344 14 6227 44689 31 _ _ (2141497 / 100000) (4283 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997273344 :
    ThetaLowerSegment 1997273344 1997404416 (99860506474563 / 50000)
      (199734236730151 / 100000) := by
  exact
    packedTile65536 1997273344 1997404416 14 6175 44690 31 _ _ (2141503 / 100000) (1070753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997404416 :
    ThetaLowerSegment 1997404416 1997535488 (199734236730151 / 100000)
      (199747319214741 / 100000) := by
  exact
    packedTile65536 1997404416 1997535488 14 6109 44692 31 _ _ (214151 / 10000) (2141513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997535488 :
    ThetaLowerSegment 1997535488 1997666560 (199747319214741 / 100000)
      (19976063302593 / 10000) := by
  exact
    packedTile65536 1997535488 1997666560 14 6217 44693 31 _ _ (2141517 / 100000) (26769 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997666560 :
    ThetaLowerSegment 1997666560 1997797632 (19976063302593 / 10000) (24971700796533 / 12500) := by
  exact
    packedTile65536 1997666560 1997797632 14 6058 44695 31 _ _ (2141523 / 100000) (1070763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997797632 :
    ThetaLowerSegment 1997797632 1997928704 (24971700796533 / 12500) (99893383037057 / 50000) := by
  exact
    packedTile65536 1997797632 1997928704 14 6145 44696 31 _ _ (214153 / 10000) (2141533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997928704 :
    ThetaLowerSegment 1997928704 1998059776 (99893383037057 / 50000) (99899959694113 / 50000) := by
  exact
    packedTile65536 1997928704 1998059776 14 6142 44698 31 _ _ (66923 / 3125) (2141539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1998059776 :
    ThetaLowerSegment 1998059776 1998190848 (99899959694113 / 50000) (12488309015797 / 6250) := by
  exact
    packedTile65536 1998059776 1998190848 14 6082 44699 31 _ _ (2141543 / 100000) (1070773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1998190848 :
    ThetaLowerSegment 1998190848 1998321920 (12488309015797 / 6250) (199826039824887 / 100000) := by
  exact
    packedTile65536 1998190848 1998321920 14 6115 44701 31 _ _ (2141549 / 100000) (133847 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1998321920 :
    ThetaLowerSegment 1998321920 1998452992 (199826039824887 / 100000)
      (199839156855387 / 100000) := by
  exact
    packedTile65536 1998321920 1998452992 14 6125 44702 31 _ _ (535389 / 25000) (2141559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1998452992 :
    ThetaLowerSegment 1998452992 1998584064 (199839156855387 / 100000)
      (199852072615809 / 100000) := by
  exact
    packedTile65536 1998452992 1998584064 14 6031 44704 31 _ _ (1070781 / 50000) (428313 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1998584064 :
    ThetaLowerSegment 1998584064 1998715136 (199852072615809 / 100000)
      (199865179018089 / 100000) := by
  exact
    packedTile65536 1998584064 1998715136 14 6120 44705 31 _ _ (2141569 / 100000) (535393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1998715136 :
    ThetaLowerSegment 1998715136 1998846208 (199865179018089 / 100000)
      (199878339002609 / 100000) := by
  exact
    packedTile65536 1998715136 1998846208 14 6145 44706 31 _ _ (267697 / 12500) (2141579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1998846208 :
    ThetaLowerSegment 1998846208 1998977280 (199878339002609 / 100000)
      (199891338405349 / 100000) := by
  exact
    packedTile65536 1998846208 1998977280 14 6070 44708 31 _ _ (1070791 / 50000) (428317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1998977280 :
    ThetaLowerSegment 1998977280 1999108352 (199891338405349 / 100000)
      (49976087139631 / 25000) := by
  exact
    packedTile65536 1998977280 1999108352 14 6075 44709 31 _ _ (2141589 / 100000) (267699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999108352 :
    ThetaLowerSegment 1999108352 1999239424 (49976087139631 / 25000) (24989672252813 / 12500) := by
  exact
    packedTile65536 1999108352 1999239424 14 6084 44711 31 _ _ (428319 / 20000) (1070799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999239424 :
    ThetaLowerSegment 1999239424 1999370496 (24989672252813 / 12500) (4998264685591 / 2500) := by
  exact
    packedTile65536 1999239424 1999370496 14 6168 44712 31 _ _ (1070801 / 50000) (428321 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999370496 :
    ThetaLowerSegment 1999370496 1999501568 (4998264685591 / 2500) (24992962293477 / 12500) := by
  exact
    packedTile65536 1999370496 1999501568 14 6122 44714 31 _ _ (267701 / 12500) (2141611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999501568 :
    ThetaLowerSegment 1999501568 1999632640 (24992962293477 / 12500) (24994594204107 / 12500) := by
  exact
    packedTile65536 1999501568 1999632640 14 6096 44715 31 _ _ (428323 / 20000) (1070809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999632640 :
    ThetaLowerSegment 1999632640 1999763712 (24994594204107 / 12500) (99984872352921 / 50000) := by
  exact
    packedTile65536 1999632640 1999763712 14 6066 44717 31 _ _ (2141621 / 100000) (267703 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999763712 :
    ThetaLowerSegment 1999763712 1999894784 (99984872352921 / 50000) (99991461071463 / 50000) := by
  exact
    packedTile65536 1999763712 1999894784 14 6153 44718 31 _ _ (535407 / 25000) (2141631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999894784 :
    ThetaLowerSegment 1999894784 2000025856 (99991461071463 / 50000)
      (199995881176311 / 100000) := by
  exact
    packedTile65536 1999894784 2000025856 14 6051 44720 31 _ _ (428327 / 20000) (1070819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2000025856 :
    ThetaLowerSegment 2000025856 2000156928 (199995881176311 / 100000)
      (25001145186519 / 12500) := by
  exact
    packedTile65536 2000025856 2000156928 14 6201 44721 31 _ _ (2141641 / 100000) (535411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2000156928 :
    ThetaLowerSegment 2000156928 2000288000 (25001145186519 / 12500) (25002780067061 / 12500) := by
  exact
    packedTile65536 2000156928 2000288000 14 6107 44723 31 _ _ (133853 / 6250) (2141651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2000288000 :
    ThetaLowerSegment 2000288000 2000419072 (25002780067061 / 12500) (100017736908277 / 50000) := by
  exact
    packedTile65536 2000288000 2000419072 14 6179 44724 31 _ _ (1070827 / 50000) (2141657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2000419072 :
    ThetaLowerSegment 2000419072 2000550144 (100017736908277 / 50000)
      (100024247557717 / 50000) := by
  exact
    packedTile65536 2000419072 2000550144 14 6080 44726 31 _ _ (2141661 / 100000) (66927 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2000550144 :
    ThetaLowerSegment 2000550144 2000681216 (100024247557717 / 50000) (50015408025203 / 25000) := by
  exact
    packedTile65536 2000550144 2000681216 14 6134 44727 31 _ _ (2141667 / 100000) (214167 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2000681216 :
    ThetaLowerSegment 2000681216 2000812288 (50015408025203 / 25000) (100037383493727 / 50000) := by
  exact
    packedTile65536 2000681216 2000812288 14 6133 44728 31 _ _ (1070837 / 50000) (2141677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2000812288 :
    ThetaLowerSegment 2000812288 2000943360 (100037383493727 / 50000)
      (100043992718207 / 50000) := by
  exact
    packedTile65536 2000812288 2000943360 14 6172 44730 31 _ _ (26771 / 1250) (2141683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2000943360 :
    ThetaLowerSegment 2000943360 2001074432 (100043992718207 / 50000)
      (200101193220143 / 100000) := by
  exact
    packedTile65536 2000943360 2001074432 14 6167 44731 31 _ _ (2141687 / 100000) (214169 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2001074432 :
    ThetaLowerSegment 2001074432 2001205504 (200101193220143 / 100000)
      (200114362496549 / 100000) := by
  exact
    packedTile65536 2001074432 2001205504 14 6149 44733 31 _ _ (1070847 / 50000) (2141697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2001205504 :
    ThetaLowerSegment 2001205504 2001336576 (200114362496549 / 100000)
      (200127529668149 / 100000) := by
  exact
    packedTile65536 2001205504 2001336576 14 6148 44734 31 _ _ (21417 / 1000) (2141703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2001336576 :
    ThetaLowerSegment 2001336576 2001467648 (200127529668149 / 100000)
      (200140551246709 / 100000) := by
  exact
    packedTile65536 2001336576 2001467648 14 6080 44736 31 _ _ (2141707 / 100000) (214171 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2001467648 :
    ThetaLowerSegment 2001467648 2001598720 (200140551246709 / 100000)
      (40030741129591 / 20000) := by
  exact
    packedTile65536 2001467648 2001598720 14 6142 44737 31 _ _ (2141713 / 100000) (535429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2001598720 :
    ThetaLowerSegment 2001598720 2001729792 (40030741129591 / 20000) (40033377586911 / 20000) := by
  exact
    packedTile65536 2001598720 2001729792 14 6155 44739 31 _ _ (53543 / 2500) (2141723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2001729792 :
    ThetaLowerSegment 2001729792 2001860864 (40033377586911 / 20000)
      (200180173060933 / 100000) := by
  exact
    packedTile65536 2001729792 2001860864 14 6203 44740 31 _ _ (1070863 / 50000) (2141729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2001860864 :
    ThetaLowerSegment 2001860864 2001991936 (200180173060933 / 100000)
      (200193370419679 / 100000) := by
  exact
    packedTile65536 2001860864 2001991936 14 6162 44742 31 _ _ (2141733 / 100000) (267717 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2001991936 :
    ThetaLowerSegment 2001991936 2002123008 (200193370419679 / 100000)
      (200206554964963 / 100000) := by
  exact
    packedTile65536 2001991936 2002123008 14 6156 44743 31 _ _ (2141739 / 100000) (1070871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2002123008 :
    ThetaLowerSegment 2002123008 2002254080 (200206554964963 / 100000)
      (200219619615563 / 100000) := by
  exact
    packedTile65536 2002123008 2002254080 14 6100 44745 31 _ _ (1070873 / 50000) (2141749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2002254080 :
    ThetaLowerSegment 2002254080 2002385152 (200219619615563 / 100000)
      (200232690728019 / 100000) := by
  exact
    packedTile65536 2002254080 2002385152 14 6103 44746 31 _ _ (267719 / 12500) (428351 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2002385152 :
    ThetaLowerSegment 2002385152 2002516224 (200232690728019 / 100000)
      (100122964470199 / 50000) := by
  exact
    packedTile65536 2002385152 2002516224 14 6181 44748 31 _ _ (2141759 / 100000) (1070881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2002516224 :
    ThetaLowerSegment 2002516224 2002647296 (100122964470199 / 50000)
      (100129479722371 / 50000) := by
  exact
    packedTile65536 2002516224 2002647296 14 6084 44749 31 _ _ (1070883 / 50000) (2141769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2002647296 :
    ThetaLowerSegment 2002647296 2002778368 (100129479722371 / 50000)
      (100136042111779 / 50000) := by
  exact
    packedTile65536 2002647296 2002778368 14 6128 44750 31 _ _ (535443 / 25000) (85671 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2002778368 :
    ThetaLowerSegment 2002778368 2002909440 (100136042111779 / 50000)
      (200285172635027 / 100000) := by
  exact
    packedTile65536 2002778368 2002909440 14 6111 44752 31 _ _ (2141779 / 100000) (1070891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2002909440 :
    ThetaLowerSegment 2002909440 2003040512 (200285172635027 / 100000)
      (25037282099949 / 12500) := by
  exact
    packedTile65536 2002909440 2003040512 14 6109 44753 31 _ _ (428357 / 20000) (535447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2003040512 :
    ThetaLowerSegment 2003040512 2003171584 (25037282099949 / 12500) (25038927799377 / 12500) := by
  exact
    packedTile65536 2003040512 2003171584 14 6147 44755 31 _ _ (66931 / 3125) (428359 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2003171584 :
    ThetaLowerSegment 2003171584 2003302656 (25038927799377 / 12500) (20032442953427 / 10000) := by
  exact
    packedTile65536 2003171584 2003302656 14 6073 44756 31 _ _ (1070899 / 50000) (2141801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2003302656 :
    ThetaLowerSegment 2003302656 2003433728 (20032442953427 / 10000) (10016874941419 / 5000) := by
  exact
    packedTile65536 2003302656 2003433728 14 6102 44758 31 _ _ (428361 / 20000) (133863 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2003433728 :
    ThetaLowerSegment 2003433728 2003564800 (10016874941419 / 5000) (200350784482013 / 100000) := by
  exact
    packedTile65536 2003433728 2003564800 14 6203 44759 31 _ _ (2141811 / 100000) (1070907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2003564800 :
    ThetaLowerSegment 2003564800 2003695872 (200350784482013 / 100000)
      (40072812322359 / 20000) := by
  exact
    packedTile65536 2003564800 2003695872 14 6199 44761 31 _ _ (1070909 / 50000) (2141821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2003695872 :
    ThetaLowerSegment 2003695872 2003826944 (40072812322359 / 20000)
      (200377278807699 / 100000) := by
  exact
    packedTile65536 2003695872 2003826944 14 6171 44762 31 _ _ (66932 / 3125) (2141827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2003826944 :
    ThetaLowerSegment 2003826944 2003958016 (200377278807699 / 100000)
      (50097596167897 / 25000) := by
  exact
    packedTile65536 2003826944 2003958016 14 6119 44764 31 _ _ (2141831 / 100000) (1070917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2003958016 :
    ThetaLowerSegment 2003958016 2004089088 (50097596167897 / 25000) (100201747430993 / 50000) := by
  exact
    packedTile65536 2003958016 2004089088 14 6121 44765 31 _ _ (1070919 / 50000) (2141841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2004089088 :
    ThetaLowerSegment 2004089088 2004220160 (100201747430993 / 50000)
      (100208330388527 / 50000) := by
  exact
    packedTile65536 2004089088 2004220160 14 6147 44767 31 _ _ (535461 / 25000) (2141847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2004220160 :
    ThetaLowerSegment 2004220160 2004351232 (100208330388527 / 50000)
      (200429603982647 / 100000) := by
  exact
    packedTile65536 2004220160 2004351232 14 6043 44768 31 _ _ (2141851 / 100000) (1070927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2004351232 :
    ThetaLowerSegment 2004351232 2004482304 (200429603982647 / 100000) (6263839105256 / 3125) := by
  exact
    packedTile65536 2004351232 2004482304 14 6185 44769 31 _ _ (2141857 / 100000) (107093 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2004482304 :
    ThetaLowerSegment 2004482304 2004613376 (6263839105256 / 3125) (25056997356581 / 12500) := by
  exact
    packedTile65536 2004482304 2004613376 14 6129 44771 31 _ _ (267733 / 12500) (2141867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2004613376 :
    ThetaLowerSegment 2004613376 2004744448 (25056997356581 / 12500) (25058614468431 / 12500) := by
  exact
    packedTile65536 2004613376 2004744448 14 6040 44772 31 _ _ (214187 / 10000) (2141873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2004744448 :
    ThetaLowerSegment 2004744448 2004875520 (25058614468431 / 12500) (100240958470419 / 50000) := by
  exact
    packedTile65536 2004744448 2004875520 14 6070 44774 31 _ _ (2141877 / 100000) (53547 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2004875520 :
    ThetaLowerSegment 2004875520 2005006592 (100240958470419 / 50000)
      (200495155919661 / 100000) := by
  exact
    packedTile65536 2004875520 2005006592 14 6181 44775 31 _ _ (2141883 / 100000) (1070943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2005006592 :
    ThetaLowerSegment 2005006592 2005137664 (200495155919661 / 100000)
      (200508122921721 / 100000) := by
  exact
    packedTile65536 2005006592 2005137664 14 6054 44777 31 _ _ (214189 / 10000) (2141893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2005137664 :
    ThetaLowerSegment 2005137664 2005268736 (200508122921721 / 100000)
      (200521479785177 / 100000) := by
  exact
    packedTile65536 2005137664 2005268736 14 6236 44778 31 _ _ (267737 / 12500) (2141899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2005268736 :
    ThetaLowerSegment 2005268736 2005399808 (200521479785177 / 100000)
      (40106933068009 / 20000) := by
  exact
    packedTile65536 2005268736 2005399808 14 6156 44780 31 _ _ (2141903 / 100000) (1070953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2005399808 :
    ThetaLowerSegment 2005399808 2005530880 (40106933068009 / 20000) (50136945062213 / 25000) := by
  exact
    packedTile65536 2005399808 2005530880 14 6123 44781 31 _ _ (2141909 / 100000) (267739 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2005530880 :
    ThetaLowerSegment 2005530880 2005661952 (50136945062213 / 25000) (12535064249957 / 6250) := by
  exact
    packedTile65536 2005530880 2005661952 14 6185 44783 31 _ _ (535479 / 25000) (2141919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2005661952 :
    ThetaLowerSegment 2005661952 2005793024 (12535064249957 / 6250) (12535880322239 / 6250) := by
  exact
    packedTile65536 2005661952 2005793024 14 6096 44784 31 _ _ (1070961 / 50000) (85677 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2005793024 :
    ThetaLowerSegment 2005793024 2005924096 (12535880322239 / 6250) (50146792014539 / 25000) := by
  exact
    packedTile65536 2005793024 2005924096 14 6108 44786 31 _ _ (2141929 / 100000) (535483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2005924096 :
    ThetaLowerSegment 2005924096 2006055168 (50146792014539 / 25000) (50150082563719 / 25000) := by
  exact
    packedTile65536 2005924096 2006055168 14 6145 44787 31 _ _ (133871 / 6250) (2141939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2006055168 :
    ThetaLowerSegment 2006055168 2006186240 (50150082563719 / 25000) (25076678261033 / 12500) := by
  exact
    packedTile65536 2006055168 2006186240 14 6114 44789 31 _ _ (1070971 / 50000) (428389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2006186240 :
    ThetaLowerSegment 2006186240 2006317312 (25076678261033 / 12500) (20062669332037 / 10000) := by
  exact
    packedTile65536 2006186240 2006317312 14 6194 44790 31 _ _ (2141949 / 100000) (66936 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2006317312 :
    ThetaLowerSegment 2006317312 2006448384 (20062669332037 / 10000) (32102373817 / 16) := by
  exact
    packedTile65536 2006317312 2006448384 14 6136 44791 31 _ _ (428391 / 20000) (1070979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2006448384 :
    ThetaLowerSegment 2006448384 2006579456 (32102373817 / 16) (100326479007731 / 50000) := by
  exact
    packedTile65536 2006448384 2006579456 14 6126 44793 31 _ _ (1070981 / 50000) (428393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2006579456 :
    ThetaLowerSegment 2006579456 2006710528 (100326479007731 / 50000)
      (100333014152099 / 50000) := by
  exact
    packedTile65536 2006579456 2006710528 14 6102 44794 31 _ _ (133873 / 6250) (2141971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2006710528 :
    ThetaLowerSegment 2006710528 2006841600 (100333014152099 / 50000)
      (200679105061573 / 100000) := by
  exact
    packedTile65536 2006710528 2006841600 14 6105 44796 31 _ _ (85679 / 4000) (1070989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2006841600 :
    ThetaLowerSegment 2006841600 2006972672 (200679105061573 / 100000)
      (100346095211751 / 50000) := by
  exact
    packedTile65536 2006841600 2006972672 14 6109 44797 31 _ _ (2141981 / 100000) (66937 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2006972672 :
    ThetaLowerSegment 2006972672 2007103744 (100346095211751 / 50000)
      (100352743942503 / 50000) := by
  exact
    packedTile65536 2006972672 2007103744 14 6208 44799 31 _ _ (535497 / 25000) (2141991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2007103744 :
    ThetaLowerSegment 2007103744 2007234816 (100352743942503 / 50000) (802874438961 / 400) := by
  exact
    packedTile65536 2007103744 2007234816 14 6126 44800 31 _ _ (1070997 / 50000) (2141997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2007234816 :
    ThetaLowerSegment 2007234816 2007365888 (802874438961 / 400) (200731699508361 / 100000) := by
  exact
    packedTile65536 2007234816 2007365888 14 6111 44802 31 _ _ (2142001 / 100000) (535501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2007365888 :
    ThetaLowerSegment 2007365888 2007496960 (200731699508361 / 100000)
      (100372287556219 / 50000) := by
  exact
    packedTile65536 2007365888 2007496960 14 6011 44803 31 _ _ (2142007 / 100000) (214201 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2007496960 :
    ThetaLowerSegment 2007496960 2007628032 (100372287556219 / 50000)
      (100378852829129 / 50000) := by
  exact
    packedTile65536 2007496960 2007628032 14 6130 44805 31 _ _ (1071007 / 50000) (2142017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2007628032 :
    ThetaLowerSegment 2007628032 2007759104 (100378852829129 / 50000)
      (100385452392749 / 50000) := by
  exact
    packedTile65536 2007628032 2007759104 14 6162 44806 31 _ _ (107101 / 5000) (2142023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2007759104 :
    ThetaLowerSegment 2007759104 2007890176 (100385452392749 / 50000) (25097993716241 / 12500) := by
  exact
    packedTile65536 2007759104 2007890176 14 6090 44808 31 _ _ (2142027 / 100000) (214203 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2007890176 :
    ThetaLowerSegment 2007890176 2008021248 (25097993716241 / 12500) (100398459872899 / 50000) := by
  exact
    packedTile65536 2007890176 2008021248 14 6055 44809 31 _ _ (1071017 / 50000) (2142037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008021248 :
    ThetaLowerSegment 2008021248 2008152320 (100398459872899 / 50000)
      (100405058427119 / 50000) := by
  exact
    packedTile65536 2008021248 2008152320 14 6161 44810 31 _ _ (53551 / 2500) (2142043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008152320 :
    ThetaLowerSegment 2008152320 2008283392 (100405058427119 / 50000)
      (100411548829529 / 50000) := by
  exact
    packedTile65536 2008152320 2008283392 14 6060 44812 31 _ _ (2142047 / 100000) (42841 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008283392 :
    ThetaLowerSegment 2008283392 2008414464 (100411548829529 / 50000)
      (200836320552227 / 100000) := by
  exact
    packedTile65536 2008283392 2008414464 14 6173 44813 31 _ _ (2142053 / 100000) (267757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008414464 :
    ThetaLowerSegment 2008414464 2008545536 (200836320552227 / 100000)
      (200849282157287 / 100000) := by
  exact
    packedTile65536 2008414464 2008545536 14 6051 44815 31 _ _ (107103 / 5000) (2142063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008545536 :
    ThetaLowerSegment 2008545536 2008676608 (200849282157287 / 100000)
      (200862331623359 / 100000) := by
  exact
    packedTile65536 2008545536 2008676608 14 6092 44816 31 _ _ (1071033 / 50000) (2142069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008676608 :
    ThetaLowerSegment 2008676608 2008807680 (200862331623359 / 100000)
      (200875668169857 / 100000) := by
  exact
    packedTile65536 2008676608 2008807680 14 6226 44818 31 _ _ (2142073 / 100000) (535519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008807680 :
    ThetaLowerSegment 2008807680 2008938752 (200875668169857 / 100000)
      (100444297808311 / 50000) := by
  exact
    packedTile65536 2008807680 2008938752 14 6035 44819 31 _ _ (2142079 / 100000) (1071041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008938752 :
    ThetaLowerSegment 2008938752 2009069824 (100444297808311 / 50000)
      (100450794755149 / 50000) := by
  exact
    packedTile65536 2008938752 2009069824 14 6066 44821 31 _ _ (1071043 / 50000) (2142089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2009069824 :
    ThetaLowerSegment 2009069824 2009200896 (100450794755149 / 50000)
      (100457383830141 / 50000) := by
  exact
    packedTile65536 2009069824 2009200896 14 6152 44822 31 _ _ (535523 / 25000) (428419 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2009200896 :
    ThetaLowerSegment 2009200896 2009331968 (100457383830141 / 50000)
      (100463998631853 / 50000) := by
  exact
    packedTile65536 2009200896 2009331968 14 6176 44824 31 _ _ (2142099 / 100000) (1071051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2009331968 :
    ThetaLowerSegment 2009331968 2009463040 (100463998631853 / 50000) (50235273523419 / 25000) := by
  exact
    packedTile65536 2009331968 2009463040 14 6114 44825 31 _ _ (428421 / 20000) (535527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2009463040 :
    ThetaLowerSegment 2009463040 2009594112 (50235273523419 / 25000) (50238540779747 / 25000) := by
  exact
    packedTile65536 2009463040 2009594112 14 6101 44827 31 _ _ (66941 / 3125) (428423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2009594112 :
    ThetaLowerSegment 2009594112 2009725184 (50238540779747 / 25000) (5024181500711 / 2500) := by
  exact
    packedTile65536 2009594112 2009725184 14 6114 44828 31 _ _ (1071059 / 50000) (2142121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2009725184 :
    ThetaLowerSegment 2009725184 2009856256 (5024181500711 / 2500) (20098037411769 / 10000) := by
  exact
    packedTile65536 2009725184 2009856256 14 6122 44829 31 _ _ (17137 / 800) (133883 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2009856256 :
    ThetaLowerSegment 2009856256 2009987328 (20098037411769 / 10000) (25124203167507 / 12500) := by
  exact
    packedTile65536 2009856256 2009987328 14 6186 44831 31 _ _ (2142131 / 100000) (1071067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2009987328 :
    ThetaLowerSegment 2009987328 2010118400 (25124203167507 / 12500) (12562906492107 / 6250) := by
  exact
    packedTile65536 2009987328 2010118400 14 6012 44832 31 _ _ (1071069 / 50000) (2142141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2010118400 :
    ThetaLowerSegment 2010118400 2010249472 (12562906492107 / 6250) (12563713812627 / 6250) := by
  exact
    packedTile65536 2010118400 2010249472 14 6030 44834 31 _ _ (66942 / 3125) (2142147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2010249472 :
    ThetaLowerSegment 2010249472 2010380544 (12563713812627 / 6250) (201032670205967 / 100000) := by
  exact
    packedTile65536 2010249472 2010380544 14 6185 44835 31 _ _ (2142151 / 100000) (1071077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2010380544 :
    ThetaLowerSegment 2010380544 2010511616 (201032670205967 / 100000)
      (201045668814643 / 100000) := by
  exact
    packedTile65536 2010380544 2010511616 14 6068 44837 31 _ _ (2142157 / 100000) (26777 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2010511616 :
    ThetaLowerSegment 2010511616 2010642688 (201045668814643 / 100000)
      (201058830270259 / 100000) := by
  exact
    packedTile65536 2010511616 2010642688 14 6144 44838 31 _ _ (535541 / 25000) (2142167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2010642688 :
    ThetaLowerSegment 2010642688 2010773760 (201058830270259 / 100000)
      (20107168543843 / 10000) := by
  exact
    packedTile65536 2010642688 2010773760 14 6001 44840 31 _ _ (2142171 / 100000) (1071087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2010773760 :
    ThetaLowerSegment 2010773760 2010904832 (20107168543843 / 10000)
      (201085011921547 / 100000) := by
  exact
    packedTile65536 2010773760 2010904832 14 6221 44841 31 _ _ (2142177 / 100000) (107109 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2010904832 :
    ThetaLowerSegment 2010904832 2011035904 (201085011921547 / 100000)
      (201098006409691 / 100000) := by
  exact
    packedTile65536 2010904832 2011035904 14 6066 44843 31 _ _ (267773 / 12500) (2142187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2011035904 :
    ThetaLowerSegment 2011035904 2011166976 (201098006409691 / 100000)
      (201111067342121 / 100000) := by
  exact
    packedTile65536 2011035904 2011166976 14 6097 44844 31 _ _ (214219 / 10000) (2142193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2011166976 :
    ThetaLowerSegment 2011166976 2011298048 (201111067342121 / 100000)
      (50281039576997 / 25000) := by
  exact
    packedTile65536 2011166976 2011298048 14 6111 44846 31 _ _ (2142197 / 100000) (10711 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2011298048 :
    ThetaLowerSegment 2011298048 2011429120 (50281039576997 / 25000) (50284355707241 / 25000) := by
  exact
    packedTile65536 2011298048 2011429120 14 6192 44847 31 _ _ (2142203 / 100000) (1071103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2011429120 :
    ThetaLowerSegment 2011429120 2011560192 (50284355707241 / 25000) (25143806468773 / 12500) := by
  exact
    packedTile65536 2011429120 2011560192 14 6082 44848 31 _ _ (214221 / 10000) (2142213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2011560192 :
    ThetaLowerSegment 2011560192 2011691264 (25143806468773 / 12500) (6286360981282 / 3125) := by
  exact
    packedTile65536 2011560192 2011691264 14 6115 44850 31 _ _ (267777 / 12500) (2142219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2011691264 :
    ThetaLowerSegment 2011691264 2011822336 (6286360981282 / 3125) (12573546718419 / 6250) := by
  exact
    packedTile65536 2011691264 2011822336 14 6160 44851 31 _ _ (2142223 / 100000) (1071113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2011822336 :
    ThetaLowerSegment 2011822336 2011953408 (12573546718419 / 6250) (25148723673107 / 12500) := by
  exact
    packedTile65536 2011822336 2011953408 14 6088 44853 31 _ _ (2142229 / 100000) (267779 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2011953408 :
    ThetaLowerSegment 2011953408 2012084480 (25148723673107 / 12500) (50300790841051 / 25000) := by
  exact
    packedTile65536 2011953408 2012084480 14 6243 44854 31 _ _ (535559 / 25000) (2142239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2012084480 :
    ThetaLowerSegment 2012084480 2012215552 (50300790841051 / 25000) (20121628031197 / 10000) := by
  exact
    packedTile65536 2012084480 2012215552 14 6123 44856 31 _ _ (1071121 / 50000) (428449 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2012215552 :
    ThetaLowerSegment 2012215552 2012346624 (20121628031197 / 10000) (50307318798601 / 25000) := by
  exact
    packedTile65536 2012215552 2012346624 14 6066 44857 31 _ _ (2142249 / 100000) (535563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2012346624 :
    ThetaLowerSegment 2012346624 2012477696 (50307318798601 / 25000) (100621169332697 / 50000) := by
  exact
    packedTile65536 2012346624 2012477696 14 6098 44859 31 _ _ (428451 / 20000) (1071129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2012477696 :
    ThetaLowerSegment 2012477696 2012608768 (100621169332697 / 50000)
      (100627619683579 / 50000) := by
  exact
    packedTile65536 2012477696 2012608768 14 6022 44860 31 _ _ (1071131 / 50000) (428453 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2012608768 :
    ThetaLowerSegment 2012608768 2012739840 (100627619683579 / 50000)
      (100634328195821 / 50000) := by
  exact
    packedTile65536 2012608768 2012739840 14 6263 44862 31 _ _ (535567 / 25000) (2142271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2012739840 :
    ThetaLowerSegment 2012739840 2012870912 (100634328195821 / 50000)
      (100640870703671 / 50000) := by
  exact
    packedTile65536 2012739840 2012870912 14 6108 44863 31 _ _ (85691 / 4000) (1071139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2012870912 :
    ThetaLowerSegment 2012870912 2013001984 (100640870703671 / 50000) (12580933883929 / 6250) := by
  exact
    packedTile65536 2012870912 2013001984 14 6162 44865 31 _ _ (2142281 / 100000) (535571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2013001984 :
    ThetaLowerSegment 2013001984 2013133056 (12580933883929 / 6250) (12581748756727 / 6250) := by
  exact
    packedTile65536 2013001984 2013133056 14 6086 44866 31 _ _ (133893 / 6250) (2142291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2013133056 :
    ThetaLowerSegment 2013133056 2013264128 (12581748756727 / 6250) (100660634378657 / 50000) := by
  exact
    packedTile65536 2013133056 2013264128 14 6203 44867 31 _ _ (1071147 / 50000) (2142297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2013264128 :
    ThetaLowerSegment 2013264128 2013395200 (100660634378657 / 50000)
      (201334411773949 / 100000) := by
  exact
    packedTile65536 2013264128 2013395200 14 6135 44869 31 _ _ (2142301 / 100000) (66947 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2013395200 :
    ThetaLowerSegment 2013395200 2013526272 (201334411773949 / 100000)
      (100673820259837 / 50000) := by
  exact
    packedTile65536 2013395200 2013526272 14 6175 44870 31 _ _ (2142307 / 100000) (214231 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2013526272 :
    ThetaLowerSegment 2013526272 2013657344 (100673820259837 / 50000)
      (100680420729271 / 50000) := by
  exact
    packedTile65536 2013526272 2013657344 14 6162 44872 31 _ _ (1071157 / 50000) (2142317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2013657344 :
    ThetaLowerSegment 2013657344 2013788416 (100680420729271 / 50000)
      (100687055494311 / 50000) := by
  exact
    packedTile65536 2013657344 2013788416 14 6194 44873 31 _ _ (26779 / 1250) (2142323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2013788416 :
    ThetaLowerSegment 2013788416 2013919488 (100687055494311 / 50000)
      (201387245595459 / 100000) := by
  exact
    packedTile65536 2013788416 2013919488 14 6131 44875 31 _ _ (2142327 / 100000) (214233 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2013919488 :
    ThetaLowerSegment 2013919488 2014050560 (201387245595459 / 100000)
      (201400395235413 / 100000) := by
  exact
    packedTile65536 2013919488 2014050560 14 6138 44876 31 _ _ (2142333 / 100000) (66948 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2014050560 :
    ThetaLowerSegment 2014050560 2014181632 (201400395235413 / 100000)
      (201413568484073 / 100000) := by
  exact
    packedTile65536 2014050560 2014181632 14 6149 44878 31 _ _ (107117 / 5000) (2142343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2014181632 :
    ThetaLowerSegment 2014181632 2014312704 (201413568484073 / 100000)
      (201426671072209 / 100000) := by
  exact
    packedTile65536 2014181632 2014312704 14 6116 44879 31 _ _ (1071173 / 50000) (2142349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2014312704 :
    ThetaLowerSegment 2014312704 2014443776 (201426671072209 / 100000)
      (201439683724331 / 100000) := by
  exact
    packedTile65536 2014312704 2014443776 14 6074 44881 31 _ _ (2142353 / 100000) (535589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2014443776 :
    ThetaLowerSegment 2014443776 2014574848 (201439683724331 / 100000)
      (201452902079361 / 100000) := by
  exact
    packedTile65536 2014443776 2014574848 14 6170 44882 31 _ _ (2142359 / 100000) (1071181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2014574848 :
    ThetaLowerSegment 2014574848 2014705920 (201452902079361 / 100000)
      (201465816261609 / 100000) := by
  exact
    packedTile65536 2014574848 2014705920 14 6028 44884 31 _ _ (1071183 / 50000) (2142369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2014705920 :
    ThetaLowerSegment 2014705920 2014836992 (201465816261609 / 100000)
      (201479064690057 / 100000) := by
  exact
    packedTile65536 2014705920 2014836992 14 6184 44885 31 _ _ (535593 / 25000) (17139 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2014836992 :
    ThetaLowerSegment 2014836992 2014968064 (201479064690057 / 100000)
      (201492163195263 / 100000) := by
  exact
    packedTile65536 2014836992 2014968064 14 6114 44886 31 _ _ (2142379 / 100000) (1071191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2014968064 :
    ThetaLowerSegment 2014968064 2015099136 (201492163195263 / 100000)
      (100752704780859 / 50000) := by
  exact
    packedTile65536 2014968064 2015099136 14 6183 44888 31 _ _ (428477 / 20000) (535597 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2015099136 :
    ThetaLowerSegment 2015099136 2015230208 (100752704780859 / 50000)
      (100759230506891 / 50000) := by
  exact
    packedTile65536 2015099136 2015230208 14 6092 44889 31 _ _ (267799 / 12500) (428479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2015230208 :
    ThetaLowerSegment 2015230208 2015361280 (100759230506891 / 50000)
      (100765796956761 / 50000) := by
  exact
    packedTile65536 2015230208 2015361280 14 6130 44891 31 _ _ (1071199 / 50000) (2142401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2015361280 :
    ThetaLowerSegment 2015361280 2015492352 (100765796956761 / 50000) (50386134581133 / 25000) := by
  exact
    packedTile65536 2015361280 2015492352 14 6042 44892 31 _ _ (428481 / 20000) (267801 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2015492352 :
    ThetaLowerSegment 2015492352 2015623424 (50386134581133 / 25000) (50389433894073 / 25000) := by
  exact
    packedTile65536 2015492352 2015623424 14 6160 44894 31 _ _ (2142411 / 100000) (1071207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2015623424 :
    ThetaLowerSegment 2015623424 2015754496 (50389433894073 / 25000) (10078554784747 / 5000) := by
  exact
    packedTile65536 2015623424 2015754496 14 6236 44895 31 _ _ (1071209 / 50000) (2142421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2015754496 :
    ThetaLowerSegment 2015754496 2015885568 (10078554784747 / 5000) (10079206081643 / 5000) := by
  exact
    packedTile65536 2015754496 2015885568 14 6080 44897 31 _ _ (267803 / 12500) (2142427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2015885568 :
    ThetaLowerSegment 2015885568 2016016640 (10079206081643 / 5000) (20159725473489 / 10000) := by
  exact
    packedTile65536 2015885568 2016016640 14 6130 44898 31 _ _ (2142431 / 100000) (1071217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016016640 :
    ThetaLowerSegment 2016016640 2016147712 (20159725473489 / 10000) (100805213218783 / 50000) := by
  exact
    packedTile65536 2016016640 2016147712 14 6148 44900 31 _ _ (2142437 / 100000) (53561 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016147712 :
    ThetaLowerSegment 2016147712 2016278784 (100805213218783 / 50000)
      (100811776595977 / 50000) := by
  exact
    packedTile65536 2016147712 2016278784 14 6127 44901 31 _ _ (535611 / 25000) (2142447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016278784 :
    ThetaLowerSegment 2016278784 2016409856 (100811776595977 / 50000)
      (100818334635427 / 50000) := by
  exact
    packedTile65536 2016278784 2016409856 14 6122 44902 31 _ _ (42849 / 2000) (2142453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016409856 :
    ThetaLowerSegment 2016409856 2016540928 (100818334635427 / 50000) (10082497410967 / 5000) := by
  exact
    packedTile65536 2016409856 2016540928 14 6198 44904 31 _ _ (2142457 / 100000) (107123 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016540928 :
    ThetaLowerSegment 2016540928 2016672000 (10082497410967 / 5000) (100831493624579 / 50000) := by
  exact
    packedTile65536 2016540928 2016672000 14 6086 44905 31 _ _ (2142463 / 100000) (1071233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016672000 :
    ThetaLowerSegment 2016672000 2016803072 (100831493624579 / 50000) (12604756063943 / 6250) := by
  exact
    packedTile65536 2016672000 2016803072 14 6119 44907 31 _ _ (214247 / 10000) (2142473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016803072 :
    ThetaLowerSegment 2016803072 2016934144 (12604756063943 / 6250) (10084455842487 / 5000) := by
  exact
    packedTile65536 2016803072 2016934144 14 6077 44908 31 _ _ (535619 / 25000) (2142479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016934144 :
    ThetaLowerSegment 2016934144 2017065216 (10084455842487 / 5000) (201702226703217 / 100000) := by
  exact
    packedTile65536 2016934144 2017065216 14 6119 44910 31 _ _ (2142483 / 100000) (1071243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2017065216 :
    ThetaLowerSegment 2017065216 2017196288 (201702226703217 / 100000)
      (201715308741051 / 100000) := by
  exact
    packedTile65536 2017065216 2017196288 14 6106 44911 31 _ _ (2142489 / 100000) (535623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2017196288 :
    ThetaLowerSegment 2017196288 2017327360 (201715308741051 / 100000)
      (40345703017279 / 20000) := by
  exact
    packedTile65536 2017196288 2017327360 14 6164 44913 31 _ _ (66953 / 3125) (2142499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2017327360 :
    ThetaLowerSegment 2017327360 2017458432 (40345703017279 / 20000)
      (201741453655973 / 100000) := by
  exact
    packedTile65536 2017327360 2017458432 14 6039 44914 31 _ _ (1071251 / 50000) (428501 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2017458432 :
    ThetaLowerSegment 2017458432 2017589504 (201741453655973 / 100000)
      (100877348252051 / 50000) := by
  exact
    packedTile65536 2017458432 2017589504 14 6181 44916 31 _ _ (2142509 / 100000) (133907 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2017589504 :
    ThetaLowerSegment 2017589504 2017720576 (100877348252051 / 50000)
      (201767703712667 / 100000) := by
  exact
    packedTile65536 2017589504 2017720576 14 6071 44917 31 _ _ (428503 / 20000) (1071259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2017720576 :
    ThetaLowerSegment 2017720576 2017851648 (201767703712667 / 100000)
      (201780743101559 / 100000) := by
  exact
    packedTile65536 2017720576 2017851648 14 6086 44919 31 _ _ (1071261 / 50000) (85701 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2017851648 :
    ThetaLowerSegment 2017851648 2017982720 (201780743101559 / 100000)
      (201793823234999 / 100000) := by
  exact
    packedTile65536 2017851648 2017982720 14 6105 44920 31 _ _ (66954 / 3125) (2142531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2017982720 :
    ThetaLowerSegment 2017982720 2018113792 (201793823234999 / 100000)
      (100903404569817 / 50000) := by
  exact
    packedTile65536 2017982720 2018113792 14 6061 44921 31 _ _ (428507 / 20000) (1071269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2018113792 :
    ThetaLowerSegment 2018113792 2018244864 (100903404569817 / 50000)
      (201819872212111 / 100000) := by
  exact
    packedTile65536 2018113792 2018244864 14 6097 44923 31 _ _ (2142541 / 100000) (133909 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2018244864 :
    ThetaLowerSegment 2018244864 2018375936 (201819872212111 / 100000)
      (40366566068483 / 20000) := by
  exact
    packedTile65536 2018244864 2018375936 14 6048 44924 31 _ _ (535637 / 25000) (2142551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2018375936 :
    ThetaLowerSegment 2018375936 2018507008 (40366566068483 / 20000)
      (201845977053759 / 100000) := by
  exact
    packedTile65536 2018375936 2018507008 14 6136 44926 31 _ _ (1071277 / 50000) (2142557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2018507008 :
    ThetaLowerSegment 2018507008 2018638080 (201845977053759 / 100000)
      (20185902739281 / 10000) := by
  exact
    packedTile65536 2018507008 2018638080 14 6091 44927 31 _ _ (2142561 / 100000) (535641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2018638080 :
    ThetaLowerSegment 2018638080 2018769152 (20185902739281 / 10000)
      (201872133475149 / 100000) := by
  exact
    packedTile65536 2018638080 2018769152 14 6117 44929 31 _ _ (2142567 / 100000) (214257 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2018769152 :
    ThetaLowerSegment 2018769152 2018900224 (201872133475149 / 100000)
      (201885520277501 / 100000) := by
  exact
    packedTile65536 2018769152 2018900224 14 6248 44930 31 _ _ (1071287 / 50000) (2142577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2018900224 :
    ThetaLowerSegment 2018900224 2019031296 (201885520277501 / 100000)
      (201898585730341 / 100000) := by
  exact
    packedTile65536 2018900224 2019031296 14 6098 44932 31 _ _ (107129 / 5000) (2142583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2019031296 :
    ThetaLowerSegment 2019031296 2019162368 (201898585730341 / 100000) (8076473248127 / 4000) := by
  exact
    packedTile65536 2019031296 2019162368 14 6182 44933 31 _ _ (2142587 / 100000) (214259 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2019162368 :
    ThetaLowerSegment 2019162368 2019293440 (8076473248127 / 4000) (25240620394459 / 12500) := by
  exact
    packedTile65536 2019162368 2019293440 14 6129 44935 31 _ _ (2142593 / 100000) (535649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2019293440 :
    ThetaLowerSegment 2019293440 2019424512 (25240620394459 / 12500) (25242244485259 / 12500) := by
  exact
    packedTile65536 2019293440 2019424512 14 6064 44936 31 _ _ (10713 / 500) (2142603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2019424512 :
    ThetaLowerSegment 2019424512 2019555584 (25242244485259 / 12500) (100975543957123 / 50000) := by
  exact
    packedTile65536 2019424512 2019555584 14 6129 44938 31 _ _ (1071303 / 50000) (2142609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2019555584 :
    ThetaLowerSegment 2019555584 2019686656 (100975543957123 / 50000) (6311381941623 / 3125) := by
  exact
    packedTile65536 2019555584 2019686656 14 6130 44939 31 _ _ (2142613 / 100000) (267827 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2019686656 :
    ThetaLowerSegment 2019686656 2019817728 (6311381941623 / 3125) (8079094341161 / 4000) := by
  exact
    packedTile65536 2019686656 2019817728 14 6131 44940 31 _ _ (2142619 / 100000) (1071311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2019817728 :
    ThetaLowerSegment 2019817728 2019948800 (8079094341161 / 4000) (40398083566899 / 20000) := by
  exact
    packedTile65536 2019817728 2019948800 14 6095 44942 31 _ _ (1071313 / 50000) (2142629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2019948800 :
    ThetaLowerSegment 2019948800 2020079872 (40398083566899 / 20000)
      (202003539312863 / 100000) := by
  exact
    packedTile65536 2019948800 2020079872 14 6124 44943 31 _ _ (267829 / 12500) (428527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2020079872 :
    ThetaLowerSegment 2020079872 2020210944 (202003539312863 / 100000)
      (202016677975211 / 100000) := by
  exact
    packedTile65536 2020079872 2020210944 14 6132 44945 31 _ _ (2142639 / 100000) (1071321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2020210944 :
    ThetaLowerSegment 2020210944 2020342016 (202016677975211 / 100000)
      (101014821560053 / 50000) := by
  exact
    packedTile65536 2020210944 2020342016 14 6051 44946 31 _ _ (428529 / 20000) (267831 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2020342016 :
    ThetaLowerSegment 2020342016 2020473088 (101014821560053 / 50000) (20204288899477 / 10000) := by
  exact
    packedTile65536 2020342016 2020473088 14 6182 44948 31 _ _ (535663 / 25000) (428531 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2020473088 :
    ThetaLowerSegment 2020473088 2020604160 (20204288899477 / 10000) (101027966748337 / 50000) := by
  exact
    packedTile65536 2020473088 2020604160 14 6088 44949 31 _ _ (1071329 / 50000) (2142661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2020604160 :
    ThetaLowerSegment 2020604160 2020735232 (101027966748337 / 50000)
      (202068993039849 / 100000) := by
  exact
    packedTile65536 2020604160 2020735232 14 6095 44951 31 _ _ (428533 / 20000) (535667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2020735232 :
    ThetaLowerSegment 2020735232 2020866304 (202068993039849 / 100000)
      (202082153325131 / 100000) := by
  exact
    packedTile65536 2020735232 2020866304 14 6142 44952 31 _ _ (2142671 / 100000) (1071337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2020866304 :
    ThetaLowerSegment 2020866304 2020997376 (202082153325131 / 100000)
      (40419031019047 / 20000) := by
  exact
    packedTile65536 2020866304 2020997376 14 6068 44954 31 _ _ (1071339 / 50000) (2142681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2020997376 :
    ThetaLowerSegment 2020997376 2021128448 (40419031019047 / 20000) (40421653664263 / 20000) := by
  exact
    packedTile65536 2020997376 2021128448 14 6120 44955 31 _ _ (535671 / 25000) (2142687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2021128448 :
    ThetaLowerSegment 2021128448 2021259520 (40421653664263 / 20000)
      (202121304453359 / 100000) := by
  exact
    packedTile65536 2021128448 2021259520 14 6084 44956 31 _ _ (2142691 / 100000) (1071347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2021259520 :
    ThetaLowerSegment 2021259520 2021390592 (202121304453359 / 100000)
      (20213433847921 / 10000) := by
  exact
    packedTile65536 2021259520 2021390592 14 6083 44958 31 _ _ (2142697 / 100000) (21427 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2021390592 :
    ThetaLowerSegment 2021390592 2021521664 (20213433847921 / 10000) (101073746269533 / 50000) := by
  exact
    packedTile65536 2021390592 2021521664 14 6139 44959 31 _ _ (133919 / 6250) (2142707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2021521664 :
    ThetaLowerSegment 2021521664 2021652736 (101073746269533 / 50000)
      (101080341530913 / 50000) := by
  exact
    packedTile65536 2021521664 2021652736 14 6156 44961 31 _ _ (214271 / 10000) (2142713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2021652736 :
    ThetaLowerSegment 2021652736 2021783808 (101080341530913 / 50000)
      (101086898244933 / 50000) := by
  exact
    packedTile65536 2021652736 2021783808 14 6120 44962 31 _ _ (2142717 / 100000) (13392 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2021783808 :
    ThetaLowerSegment 2021783808 2021914880 (101086898244933 / 50000)
      (202186727823171 / 100000) := by
  exact
    packedTile65536 2021783808 2021914880 14 6035 44964 31 _ _ (2142723 / 100000) (1071363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2021914880 :
    ThetaLowerSegment 2021914880 2022045952 (202186727823171 / 100000)
      (202199807047091 / 100000) := by
  exact
    packedTile65536 2021914880 2022045952 14 6104 44965 31 _ _ (214273 / 10000) (2142733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2022045952 :
    ThetaLowerSegment 2022045952 2022177024 (202199807047091 / 100000)
      (202212717031491 / 100000) := by
  exact
    packedTile65536 2022045952 2022177024 14 6025 44967 31 _ _ (133921 / 6250) (2142739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2022177024 :
    ThetaLowerSegment 2022177024 2022308096 (202212717031491 / 100000) (12639121243659 / 6250) := by
  exact
    packedTile65536 2022177024 2022308096 14 6171 44968 31 _ _ (2142743 / 100000) (1071373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2022308096 :
    ThetaLowerSegment 2022308096 2022439168 (12639121243659 / 6250) (202239068521667 / 100000) := by
  exact
    packedTile65536 2022308096 2022439168 14 6127 44970 31 _ _ (2142749 / 100000) (66961 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2022439168 :
    ThetaLowerSegment 2022439168 2022570240 (202239068521667 / 100000) (8090091401627 / 4000) := by
  exact
    packedTile65536 2022439168 2022570240 14 6168 44971 31 _ _ (535689 / 25000) (2142759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2022570240 :
    ThetaLowerSegment 2022570240 2022701312 (8090091401627 / 4000) (202265467312499 / 100000) := by
  exact
    packedTile65536 2022570240 2022701312 14 6152 44972 31 _ _ (1071381 / 50000) (428553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2022701312 :
    ThetaLowerSegment 2022701312 2022832384 (202265467312499 / 100000)
      (202278593909267 / 100000) := by
  exact
    packedTile65536 2022701312 2022832384 14 6126 44974 31 _ _ (133923 / 6250) (2142771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2022832384 :
    ThetaLowerSegment 2022832384 2022963456 (202278593909267 / 100000)
      (202291737691117 / 100000) := by
  exact
    packedTile65536 2022832384 2022963456 14 6134 44975 31 _ _ (85711 / 4000) (1071389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2022963456 :
    ThetaLowerSegment 2022963456 2023094528 (202291737691117 / 100000)
      (202304770085159 / 100000) := by
  exact
    packedTile65536 2022963456 2023094528 14 6082 44977 31 _ _ (2142781 / 100000) (66962 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2023094528 :
    ThetaLowerSegment 2023094528 2023225600 (202304770085159 / 100000) (8092716386447 / 4000) := by
  exact
    packedTile65536 2023094528 2023225600 14 6132 44978 31 _ _ (535697 / 25000) (2142791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2023225600 :
    ThetaLowerSegment 2023225600 2023356672 (8092716386447 / 4000) (8093232799801 / 4000) := by
  exact
    packedTile65536 2023225600 2023356672 14 6025 44980 31 _ _ (1071397 / 50000) (2142797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2023356672 :
    ThetaLowerSegment 2023356672 2023487744 (8093232799801 / 4000) (101171938040759 / 50000) := by
  exact
    packedTile65536 2023356672 2023487744 14 6093 44981 31 _ _ (2142801 / 100000) (535701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2023487744 :
    ThetaLowerSegment 2023487744 2023618816 (101171938040759 / 50000)
      (202356867920359 / 100000) := by
  exact
    packedTile65536 2023487744 2023618816 14 6063 44983 31 _ _ (2142807 / 100000) (214281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2023618816 :
    ThetaLowerSegment 2023618816 2023749888 (202356867920359 / 100000)
      (202369934800131 / 100000) := by
  exact
    packedTile65536 2023618816 2023749888 14 6098 44984 31 _ _ (1071407 / 50000) (2142817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2023749888 :
    ThetaLowerSegment 2023749888 2023880960 (202369934800131 / 100000)
      (202382995288031 / 100000) := by
  exact
    packedTile65536 2023749888 2023880960 14 6095 44986 31 _ _ (107141 / 5000) (2142823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2023880960 :
    ThetaLowerSegment 2023880960 2024012032 (202382995288031 / 100000)
      (101198000052547 / 50000) := by
  exact
    packedTile65536 2023880960 2024012032 14 6069 44987 31 _ _ (2142827 / 100000) (214283 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024012032 :
    ThetaLowerSegment 2024012032 2024143104 (101198000052547 / 50000) (40481842991241 / 20000) := by
  exact
    packedTile65536 2024012032 2024143104 14 6167 44989 31 _ _ (2142833 / 100000) (535709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024143104 :
    ThetaLowerSegment 2024143104 2024274176 (40481842991241 / 20000) (40484498827137 / 20000) := by
  exact
    packedTile65536 2024143104 2024274176 14 6197 44990 31 _ _ (53571 / 2500) (2142843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024274176 :
    ThetaLowerSegment 2024274176 2024405248 (40484498827137 / 20000) (40487102385027 / 20000) := by
  exact
    packedTile65536 2024274176 2024405248 14 6075 44991 31 _ _ (1071423 / 50000) (2142849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024405248 :
    ThetaLowerSegment 2024405248 2024536320 (40487102385027 / 20000)
      (202448514757139 / 100000) := by
  exact
    packedTile65536 2024405248 2024536320 14 6068 44993 31 _ _ (2142853 / 100000) (267857 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024536320 :
    ThetaLowerSegment 2024536320 2024667392 (202448514757139 / 100000) (8098463790739 / 4000) := by
  exact
    packedTile65536 2024536320 2024667392 14 6104 44994 31 _ _ (2142859 / 100000) (1071431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024667392 :
    ThetaLowerSegment 2024667392 2024798464 (8098463790739 / 4000) (202474721965591 / 100000) := by
  exact
    packedTile65536 2024667392 2024798464 14 6126 44996 31 _ _ (1071433 / 50000) (2142869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024798464 :
    ThetaLowerSegment 2024798464 2024929536 (202474721965591 / 100000)
      (202487952057319 / 100000) := by
  exact
    packedTile65536 2024798464 2024929536 14 6174 44997 31 _ _ (267859 / 12500) (17143 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024929536 :
    ThetaLowerSegment 2024929536 2025060608 (202487952057319 / 100000)
      (202501087905589 / 100000) := by
  exact
    packedTile65536 2024929536 2025060608 14 6130 44999 31 _ _ (2142879 / 100000) (1071441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025060608 :
    ThetaLowerSegment 2025060608 2025191680 (202501087905589 / 100000)
      (101257145110037 / 50000) := by
  exact
    packedTile65536 2025060608 2025191680 14 6161 45000 31 _ _ (428577 / 20000) (267861 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025191680 :
    ThetaLowerSegment 2025191680 2025322752 (101257145110037 / 50000)
      (101263695930881 / 50000) := by
  exact
    packedTile65536 2025191680 2025322752 14 6114 45002 31 _ _ (535723 / 25000) (428579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025322752 :
    ThetaLowerSegment 2025322752 2025339136 (101263695930881 / 50000) (50632242794397 / 25000) := by
  exact
    packedTile65536 2025322752 2025339136 11 737 45003 31 _ _ (1071449 / 50000) (2142901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025339136 :
    ThetaLowerSegment 2025339136 2025341184 (50632242794397 / 25000) (50632294223973 / 25000) := by
  exact
    packedTile65536 2025339136 2025341184 8 96 45003 31 _ _ (2142899 / 100000) (1071451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1993341184_2025341184 :
    ThetaLowerSegment 1993341184 2025341184 (99663955798939 / 50000) (50632294223973 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1993341184 cell1993472256)
                  (ThetaLowerSegment.join cell1993603328 cell1993734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1993865472 cell1993996544)
                  (ThetaLowerSegment.join cell1994127616 cell1994258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1994389760 cell1994520832)
                  (ThetaLowerSegment.join cell1994651904 cell1994782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1994914048 cell1995045120)
                  (ThetaLowerSegment.join cell1995176192 cell1995307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1995438336 cell1995569408)
                  (ThetaLowerSegment.join cell1995700480 cell1995831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1995962624 cell1996093696)
                  (ThetaLowerSegment.join cell1996224768 cell1996355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1996486912 cell1996617984)
                  (ThetaLowerSegment.join cell1996749056 cell1996880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1997011200 cell1997142272)
                  (ThetaLowerSegment.join cell1997273344 cell1997404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1997535488 cell1997666560)
                  (ThetaLowerSegment.join cell1997797632 cell1997928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1998059776 cell1998190848)
                  (ThetaLowerSegment.join cell1998321920 cell1998452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1998584064 cell1998715136)
                  (ThetaLowerSegment.join cell1998846208 cell1998977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1999108352 cell1999239424)
                  (ThetaLowerSegment.join cell1999370496 cell1999501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1999632640 cell1999763712)
                  (ThetaLowerSegment.join cell1999894784 cell2000025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2000156928 cell2000288000)
                  (ThetaLowerSegment.join cell2000419072 cell2000550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2000681216 cell2000812288)
                  (ThetaLowerSegment.join cell2000943360 cell2001074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2001205504 cell2001336576)
                  (ThetaLowerSegment.join cell2001467648 cell2001598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2001729792 cell2001860864)
                  (ThetaLowerSegment.join cell2001991936 cell2002123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2002254080 cell2002385152)
                  (ThetaLowerSegment.join cell2002516224 cell2002647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2002778368 cell2002909440)
                  (ThetaLowerSegment.join cell2003040512 cell2003171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2003302656 cell2003433728)
                  (ThetaLowerSegment.join cell2003564800 cell2003695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2003826944 cell2003958016)
                  (ThetaLowerSegment.join cell2004089088 cell2004220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2004351232 cell2004482304)
                  (ThetaLowerSegment.join cell2004613376 cell2004744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2004875520 cell2005006592)
                  (ThetaLowerSegment.join cell2005137664 cell2005268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2005399808 cell2005530880)
                  (ThetaLowerSegment.join cell2005661952 cell2005793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2005924096 cell2006055168)
                  (ThetaLowerSegment.join cell2006186240 cell2006317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2006448384 cell2006579456)
                  (ThetaLowerSegment.join cell2006710528 cell2006841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2006972672 cell2007103744)
                  (ThetaLowerSegment.join cell2007234816 cell2007365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2007496960 cell2007628032)
                  (ThetaLowerSegment.join cell2007759104 cell2007890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2008021248 cell2008152320)
                  (ThetaLowerSegment.join cell2008283392 cell2008414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2008545536 cell2008676608)
                  (ThetaLowerSegment.join cell2008807680 cell2008938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2009069824 cell2009200896)
                  (ThetaLowerSegment.join cell2009331968 cell2009463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2009594112 cell2009725184)
                  (ThetaLowerSegment.join cell2009856256 cell2009987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2010118400 cell2010249472)
                  (ThetaLowerSegment.join cell2010380544 cell2010511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2010642688 cell2010773760)
                  (ThetaLowerSegment.join cell2010904832 cell2011035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2011166976 cell2011298048)
                  (ThetaLowerSegment.join cell2011429120 cell2011560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2011691264 cell2011822336)
                  (ThetaLowerSegment.join cell2011953408 cell2012084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2012215552 cell2012346624)
                  (ThetaLowerSegment.join cell2012477696 cell2012608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2012739840 cell2012870912)
                  (ThetaLowerSegment.join cell2013001984 cell2013133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2013264128 cell2013395200)
                  (ThetaLowerSegment.join cell2013526272 cell2013657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2013788416 cell2013919488)
                  (ThetaLowerSegment.join cell2014050560 cell2014181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2014312704 cell2014443776)
                  (ThetaLowerSegment.join cell2014574848 cell2014705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2014836992 cell2014968064)
                  (ThetaLowerSegment.join cell2015099136 cell2015230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2015361280 cell2015492352)
                  (ThetaLowerSegment.join cell2015623424 cell2015754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2015885568 cell2016016640)
                  (ThetaLowerSegment.join cell2016147712 cell2016278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2016409856 cell2016540928)
                  (ThetaLowerSegment.join cell2016672000 cell2016803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2016934144 cell2017065216)
                  (ThetaLowerSegment.join cell2017196288 cell2017327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2017458432 cell2017589504)
                  (ThetaLowerSegment.join cell2017720576 cell2017851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2017982720 cell2018113792)
                  (ThetaLowerSegment.join cell2018244864 cell2018375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2018507008 cell2018638080)
                  (ThetaLowerSegment.join cell2018769152 cell2018900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2019031296 cell2019162368)
                  (ThetaLowerSegment.join cell2019293440 cell2019424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2019555584 cell2019686656)
                  (ThetaLowerSegment.join cell2019817728 cell2019948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2020079872 cell2020210944)
                  (ThetaLowerSegment.join cell2020342016 cell2020473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2020604160 cell2020735232)
                  (ThetaLowerSegment.join cell2020866304 cell2020997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2021128448 cell2021259520)
                  (ThetaLowerSegment.join cell2021390592 cell2021521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2021652736 cell2021783808)
                  (ThetaLowerSegment.join cell2021914880 cell2022045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2022177024 cell2022308096)
                  (ThetaLowerSegment.join cell2022439168 cell2022570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2022701312 cell2022832384)
                  (ThetaLowerSegment.join cell2022963456 cell2023094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2023225600 cell2023356672)
                  (ThetaLowerSegment.join cell2023487744 cell2023618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2023749888 cell2023880960)
                  (ThetaLowerSegment.join cell2024012032 cell2024143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2024274176 cell2024405248)
                  (ThetaLowerSegment.join cell2024536320 cell2024667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2024798464 cell2024929536)
                (ThetaLowerSegment.join cell2025060608 cell2025191680))
              (ThetaLowerSegment.join cell2025322752 cell2025339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
