/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 107667712 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell88412416 :
    ThetaLowerSegment 88412416 88445184 (1768014080011 / 20000) (8843389568369 / 100000) := by
  exact
    packedTile16384 88412416 88445184 12 1814 9402 26 _ _ (1829751 / 100000) (914877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88445184 :
    ThetaLowerSegment 88445184 88477952 (8843389568369 / 100000) (8846597186733 / 100000) := by
  exact
    packedTile16384 88445184 88477952 12 1753 9404 26 _ _ (457447 / 25000) (1829791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88477952 :
    ThetaLowerSegment 88477952 88510720 (8846597186733 / 100000) (8849806699783 / 100000) := by
  exact
    packedTile16384 88477952 88510720 12 1754 9406 26 _ _ (73193 / 4000) (457457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88510720 :
    ThetaLowerSegment 88510720 88543488 (8849806699783 / 100000) (8853005298559 / 100000) := by
  exact
    packedTile16384 88510720 88543488 12 1748 9408 26 _ _ (914931 / 50000) (365973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88543488 :
    ThetaLowerSegment 88543488 88576256 (8853005298559 / 100000) (1771242988281 / 20000) := by
  exact
    packedTile16384 88543488 88576256 12 1754 9409 26 _ _ (1829899 / 100000) (914951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88576256 :
    ThetaLowerSegment 88576256 88609024 (1771242988281 / 20000) (8859530785437 / 100000) := by
  exact
    packedTile16384 88576256 88609024 12 1812 9411 26 _ _ (114371 / 6250) (1829939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88609024 :
    ThetaLowerSegment 88609024 88641792 (8859530785437 / 100000) (8862868656189 / 100000) := by
  exact
    packedTile16384 88609024 88641792 12 1824 9413 26 _ _ (1829973 / 100000) (228747 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88641792 :
    ThetaLowerSegment 88641792 88674560 (8862868656189 / 100000) (8866104113869 / 100000) := by
  exact
    packedTile16384 88641792 88674560 12 1768 9414 26 _ _ (183001 / 10000) (1830013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88674560 :
    ThetaLowerSegment 88674560 88707328 (8866104113869 / 100000) (1773867927393 / 20000) := by
  exact
    packedTile16384 88674560 88707328 12 1768 9416 26 _ _ (1830047 / 100000) (36601 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88707328 :
    ThetaLowerSegment 88707328 88740096 (1773867927393 / 20000) (8872653919089 / 100000) := by
  exact
    packedTile16384 88707328 88740096 12 1811 9418 26 _ _ (457521 / 25000) (1830087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88740096 :
    ThetaLowerSegment 88740096 88772864 (8872653919089 / 100000) (4437953022053 / 50000) := by
  exact
    packedTile16384 88740096 88772864 12 1777 9420 26 _ _ (1830121 / 100000) (457531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88772864 :
    ThetaLowerSegment 88772864 88805632 (4437953022053 / 50000) (277475296228 / 3125) := by
  exact
    packedTile16384 88772864 88805632 12 1805 9421 26 _ _ (915079 / 50000) (1830161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88805632 :
    ThetaLowerSegment 88805632 88838400 (277475296228 / 3125) (4441264726513 / 50000) := by
  exact
    packedTile16384 88805632 88838400 12 1814 9423 26 _ _ (366039 / 20000) (915099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88838400 :
    ThetaLowerSegment 88838400 88871168 (4441264726513 / 50000) (444292474603 / 5000) := by
  exact
    packedTile16384 88838400 88871168 12 1814 9425 26 _ _ (1830231 / 100000) (915117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88871168 :
    ThetaLowerSegment 88871168 88903936 (444292474603 / 5000) (44445765629 / 500) := by
  exact
    packedTile16384 88871168 88903936 12 1805 9427 26 _ _ (457567 / 25000) (1830271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88903936 :
    ThetaLowerSegment 88903936 88936704 (44445765629 / 500) (1778494293753 / 20000) := by
  exact
    packedTile16384 88903936 88936704 12 1813 9428 26 _ _ (366061 / 20000) (457577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88936704 :
    ThetaLowerSegment 88936704 88969472 (1778494293753 / 20000) (8895755102313 / 100000) := by
  exact
    packedTile16384 88936704 88969472 12 1794 9430 26 _ _ (915171 / 50000) (366069 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88969472 :
    ThetaLowerSegment 88969472 89002240 (8895755102313 / 100000) (8899005855417 / 100000) := by
  exact
    packedTile16384 88969472 89002240 12 1776 9432 26 _ _ (1830379 / 100000) (915191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89002240 :
    ThetaLowerSegment 89002240 89035008 (8899005855417 / 100000) (8902225557161 / 100000) := by
  exact
    packedTile16384 89002240 89035008 12 1759 9434 26 _ _ (114401 / 6250) (1830419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89035008 :
    ThetaLowerSegment 89035008 89067776 (8902225557161 / 100000) (1781096020519 / 20000) := by
  exact
    packedTile16384 89035008 89067776 12 1778 9435 26 _ _ (1830453 / 100000) (228807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89067776 :
    ThetaLowerSegment 89067776 89100544 (1781096020519 / 20000) (1781758657537 / 20000) := by
  exact
    packedTile16384 89067776 89100544 12 1810 9437 26 _ _ (1830489 / 100000) (457623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89100544 :
    ThetaLowerSegment 89100544 89133312 (1781758657537 / 20000) (8912062607121 / 100000) := by
  exact
    packedTile16384 89100544 89133312 12 1786 9439 26 _ _ (915263 / 50000) (1830529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89133312 :
    ThetaLowerSegment 89133312 89166080 (8912062607121 / 100000) (8915412537411 / 100000) := by
  exact
    packedTile16384 89133312 89166080 12 1830 9441 26 _ _ (1830563 / 100000) (915283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89166080 :
    ThetaLowerSegment 89166080 89198848 (8915412537411 / 100000) (8918696633811 / 100000) := by
  exact
    packedTile16384 89166080 89198848 12 1794 9442 26 _ _ (9153 / 500) (1830603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89198848 :
    ThetaLowerSegment 89198848 89231616 (8918696633811 / 100000) (1784396158959 / 20000) := by
  exact
    packedTile16384 89198848 89231616 12 1794 9444 26 _ _ (457659 / 25000) (1830639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89231616 :
    ThetaLowerSegment 89231616 89264384 (1784396158959 / 20000) (8925297974271 / 100000) := by
  exact
    packedTile16384 89231616 89264384 12 1812 9446 26 _ _ (1830673 / 100000) (457669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89264384 :
    ThetaLowerSegment 89264384 89297152 (8925297974271 / 100000) (8928584098721 / 100000) := by
  exact
    packedTile16384 89264384 89297152 12 1795 9447 26 _ _ (183071 / 10000) (1830713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89297152 :
    ThetaLowerSegment 89297152 89329920 (8928584098721 / 100000) (8931835505393 / 100000) := by
  exact
    packedTile16384 89297152 89329920 12 1776 9449 26 _ _ (1830747 / 100000) (7323 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89329920 :
    ThetaLowerSegment 89329920 89362688 (8931835505393 / 100000) (2233770370913 / 25000) := by
  exact
    packedTile16384 89329920 89362688 12 1773 9451 26 _ _ (1830783 / 100000) (915393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89362688 :
    ThetaLowerSegment 89362688 89395456 (2233770370913 / 25000) (279321476546 / 3125) := by
  exact
    packedTile16384 89362688 89395456 12 1751 9453 26 _ _ (91541 / 5000) (1830823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89395456 :
    ThetaLowerSegment 89395456 89428224 (279321476546 / 3125) (2235393867161 / 25000) := by
  exact
    packedTile16384 89395456 89428224 12 1796 9454 26 _ _ (1830857 / 100000) (91543 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89428224 :
    ThetaLowerSegment 89428224 89460992 (2235393867161 / 25000) (4472433707129 / 50000) := by
  exact
    packedTile16384 89428224 89460992 12 1798 9456 26 _ _ (1830893 / 100000) (114431 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89460992 :
    ThetaLowerSegment 89460992 89493760 (4472433707129 / 50000) (2237022920497 / 25000) := by
  exact
    packedTile16384 89460992 89493760 12 1761 9458 26 _ _ (183093 / 10000) (1830933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89493760 :
    ThetaLowerSegment 89493760 89526528 (2237022920497 / 25000) (4475685471047 / 50000) := by
  exact
    packedTile16384 89493760 89526528 12 1791 9460 26 _ _ (915483 / 50000) (1830969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89526528 :
    ThetaLowerSegment 89526528 89559296 (4475685471047 / 50000) (8954591676371 / 100000) := by
  exact
    packedTile16384 89526528 89559296 12 1759 9461 26 _ _ (1831003 / 100000) (915503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89559296 :
    ThetaLowerSegment 89559296 89592064 (8954591676371 / 100000) (8957852758611 / 100000) := by
  exact
    packedTile16384 89559296 89592064 12 1781 9463 26 _ _ (11444 / 625) (1831043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89592064 :
    ThetaLowerSegment 89592064 89624832 (8957852758611 / 100000) (8961143202183 / 100000) := by
  exact
    packedTile16384 89592064 89624832 12 1797 9465 26 _ _ (457769 / 25000) (1831079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89624832 :
    ThetaLowerSegment 89624832 89657600 (8961143202183 / 100000) (4482171078297 / 50000) := by
  exact
    packedTile16384 89624832 89657600 12 1747 9467 26 _ _ (1831113 / 100000) (457779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89657600 :
    ThetaLowerSegment 89657600 89690368 (4482171078297 / 50000) (4483793476311 / 50000) := by
  exact
    packedTile16384 89657600 89690368 12 1772 9468 26 _ _ (1831149 / 100000) (114447 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89690368 :
    ThetaLowerSegment 89690368 89723136 (4483793476311 / 50000) (44854168227 / 500) := by
  exact
    packedTile16384 89690368 89723136 12 1773 9470 26 _ _ (915593 / 50000) (1831189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89723136 :
    ThetaLowerSegment 89723136 89739520 (44854168227 / 500) (4486214319881 / 50000) := by
  exact
    packedTile16384 89723136 89739520 11 871 9472 26 _ _ (915611 / 50000) (73249 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89739520 :
    ThetaLowerSegment 89739520 89755904 (4486214319881 / 50000) (8974067600457 / 100000) := by
  exact
    packedTile16384 89739520 89755904 11 895 9473 26 _ _ (1831241 / 100000) (457811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89755904 :
    ThetaLowerSegment 89755904 89772288 (8974067600457 / 100000) (8975668120823 / 100000) := by
  exact
    packedTile16384 89755904 89772288 11 874 9473 26 _ _ (1831259 / 100000) (915631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89772288 :
    ThetaLowerSegment 89772288 89788672 (8975668120823 / 100000) (8977264994367 / 100000) := by
  exact
    packedTile16384 89772288 89788672 11 872 9474 26 _ _ (1831277 / 100000) (22891 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89788672 :
    ThetaLowerSegment 89788672 89805056 (8977264994367 / 100000) (4489450170401 / 50000) := by
  exact
    packedTile16384 89788672 89805056 11 893 9475 26 _ _ (366259 / 20000) (915649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89805056 :
    ThetaLowerSegment 89805056 89821440 (4489450170401 / 50000) (4490244960677 / 50000) := by
  exact
    packedTile16384 89805056 89821440 11 868 9476 26 _ _ (915657 / 50000) (1831317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89821440 :
    ThetaLowerSegment 89821440 89837824 (4490244960677 / 50000) (4491087373397 / 50000) := by
  exact
    packedTile16384 89821440 89837824 11 920 9477 26 _ _ (457833 / 25000) (366267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89837824 :
    ThetaLowerSegment 89837824 89854208 (4491087373397 / 50000) (1122983593193 / 12500) := by
  exact
    packedTile16384 89837824 89854208 11 925 9478 26 _ _ (36627 / 2000) (1831353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89854208 :
    ThetaLowerSegment 89854208 89870592 (1122983593193 / 12500) (561593094139 / 6250) := by
  exact
    packedTile16384 89854208 89870592 11 885 9479 26 _ _ (228921 / 12500) (1831371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89870592 :
    ThetaLowerSegment 89870592 89886976 (561593094139 / 6250) (8987091969849 / 100000) := by
  exact
    packedTile16384 89870592 89886976 11 875 9480 26 _ _ (1831387 / 100000) (183139 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89886976 :
    ThetaLowerSegment 89886976 89903360 (8987091969849 / 100000) (4494385684117 / 50000) := by
  exact
    packedTile16384 89886976 89903360 11 917 9480 26 _ _ (366281 / 20000) (114463 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89903360 :
    ThetaLowerSegment 89903360 89919744 (4494385684117 / 50000) (2247609490791 / 25000) := by
  exact
    packedTile16384 89903360 89919744 11 910 9481 26 _ _ (1831423 / 100000) (915713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89919744 :
    ThetaLowerSegment 89919744 89936128 (2247609490791 / 25000) (4496001006889 / 50000) := by
  exact
    packedTile16384 89919744 89936128 11 854 9482 26 _ _ (1831441 / 100000) (457861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89936128 :
    ThetaLowerSegment 89936128 89952512 (4496001006889 / 50000) (4496825163889 / 50000) := by
  exact
    packedTile16384 89936128 89952512 11 900 9483 26 _ _ (91573 / 5000) (1831463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89952512 :
    ThetaLowerSegment 89952512 89968896 (4496825163889 / 50000) (1124404319531 / 12500) := by
  exact
    packedTile16384 89952512 89968896 11 865 9484 26 _ _ (915739 / 50000) (1831481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89968896 :
    ThetaLowerSegment 89968896 89985280 (1124404319531 / 12500) (281153105816 / 3125) := by
  exact
    packedTile16384 89968896 89985280 11 909 9485 26 _ _ (228937 / 12500) (1831499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell89985280 :
    ThetaLowerSegment 89985280 90001664 (281153105816 / 3125) (4499272958599 / 50000) := by
  exact
    packedTile16384 89985280 90001664 11 899 9486 26 _ _ (915757 / 50000) (1831517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90001664 :
    ThetaLowerSegment 90001664 90018048 (4499272958599 / 50000) (4500114547553 / 50000) := by
  exact
    packedTile16384 90001664 90018048 11 919 9486 26 _ _ (457883 / 25000) (366307 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90018048 :
    ThetaLowerSegment 90018048 90034432 (4500114547553 / 50000) (9001890311863 / 100000) := by
  exact
    packedTile16384 90018048 90034432 11 907 9487 26 _ _ (1831551 / 100000) (915777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90034432 :
    ThetaLowerSegment 90034432 90050816 (9001890311863 / 100000) (4501739141093 / 50000) := by
  exact
    packedTile16384 90034432 90050816 11 867 9488 26 _ _ (1831569 / 100000) (457893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90050816 :
    ThetaLowerSegment 90050816 90067200 (4501739141093 / 50000) (2251289919763 / 25000) := by
  exact
    packedTile16384 90050816 90067200 11 918 9489 26 _ _ (1831587 / 100000) (183159 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90067200 :
    ThetaLowerSegment 90067200 90083584 (2251289919763 / 25000) (9006787975897 / 100000) := by
  exact
    packedTile16384 90067200 90083584 11 889 9490 26 _ _ (366321 / 20000) (228951 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90083584 :
    ThetaLowerSegment 90083584 90099968 (9006787975897 / 100000) (4504239281963 / 50000) := by
  exact
    packedTile16384 90083584 90099968 11 923 9491 26 _ _ (1831623 / 100000) (915813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90099968 :
    ThetaLowerSegment 90099968 90116352 (4504239281963 / 50000) (1126266109171 / 12500) := by
  exact
    packedTile16384 90099968 90116352 11 901 9492 26 _ _ (915821 / 50000) (366329 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90116352 :
    ThetaLowerSegment 90116352 90132736 (1126266109171 / 12500) (1126471255091 / 12500) := by
  exact
    packedTile16384 90116352 90132736 11 896 9492 26 _ _ (91583 / 5000) (1831663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90132736 :
    ThetaLowerSegment 90132736 90149120 (1126471255091 / 12500) (450670378043 / 5000) := by
  exact
    packedTile16384 90132736 90149120 11 894 9493 26 _ _ (915839 / 50000) (1831681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90149120 :
    ThetaLowerSegment 90149120 90165504 (450670378043 / 5000) (2253770432751 / 25000) := by
  exact
    packedTile16384 90149120 90165504 11 914 9494 26 _ _ (114481 / 6250) (1831699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90165504 :
    ThetaLowerSegment 90165504 90198272 (2253770432751 / 25000) (4509204977671 / 50000) := by
  exact
    packedTile16384 90165504 90198272 12 1817 9495 26 _ _ (915857 / 50000) (1831717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90198272 :
    ThetaLowerSegment 90198272 90231040 (4509204977671 / 50000) (2255402048147 / 25000) := by
  exact
    packedTile16384 90198272 90231040 12 1746 9497 26 _ _ (1831751 / 100000) (915877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90231040 :
    ThetaLowerSegment 90231040 90247424 (2255402048147 / 25000) (4511655877249 / 50000) := by
  exact
    packedTile16384 90231040 90247424 11 930 9499 26 _ _ (1831787 / 100000) (183179 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90247424 :
    ThetaLowerSegment 90247424 90280192 (4511655877249 / 50000) (9026552217543 / 100000) := by
  exact
    packedTile16384 90247424 90280192 12 1769 9499 26 _ _ (366361 / 20000) (57244 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90280192 :
    ThetaLowerSegment 90280192 90312960 (9026552217543 / 100000) (56436754204 / 625) := by
  exact
    packedTile16384 90280192 90312960 12 1817 9501 26 _ _ (1831841 / 100000) (457961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90312960 :
    ThetaLowerSegment 90312960 90345728 (56436754204 / 625) (2258304588589 / 25000) := by
  exact
    packedTile16384 90312960 90345728 12 1822 9503 26 _ _ (915939 / 50000) (1831881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90345728 :
    ThetaLowerSegment 90345728 90378496 (2258304588589 / 25000) (2259119790319 / 25000) := by
  exact
    packedTile16384 90345728 90378496 12 1780 9505 26 _ _ (915957 / 50000) (1831917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90378496 :
    ThetaLowerSegment 90378496 90411264 (2259119790319 / 25000) (4519876427963 / 50000) := by
  exact
    packedTile16384 90378496 90411264 12 1787 9506 26 _ _ (36639 / 2000) (1831953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90411264 :
    ThetaLowerSegment 90411264 90444032 (4519876427963 / 50000) (90429753193 / 1000) := by
  exact
    packedTile16384 90411264 90444032 12 1759 9508 26 _ _ (915993 / 50000) (1831989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90444032 :
    ThetaLowerSegment 90444032 90476800 (90429753193 / 1000) (2261590224451 / 25000) := by
  exact
    packedTile16384 90444032 90476800 12 1848 9510 26 _ _ (1832023 / 100000) (916013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90476800 :
    ThetaLowerSegment 90476800 90509568 (2261590224451 / 25000) (2262414651001 / 25000) := by
  exact
    packedTile16384 90476800 90509568 12 1800 9511 26 _ _ (1832059 / 100000) (916031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90509568 :
    ThetaLowerSegment 90509568 90542336 (2262414651001 / 25000) (4526432385127 / 50000) := by
  exact
    packedTile16384 90509568 90542336 12 1750 9513 26 _ _ (366419 / 20000) (916049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90542336 :
    ThetaLowerSegment 90542336 90575104 (4526432385127 / 50000) (452806847811 / 5000) := by
  exact
    packedTile16384 90542336 90575104 12 1786 9515 26 _ _ (1832131 / 100000) (916067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90575104 :
    ThetaLowerSegment 90575104 90607872 (452806847811 / 5000) (905937989181 / 10000) := by
  exact
    packedTile16384 90575104 90607872 12 1770 9517 26 _ _ (1832167 / 100000) (183217 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90607872 :
    ThetaLowerSegment 90607872 90640640 (905937989181 / 10000) (4531339845607 / 50000) := by
  exact
    packedTile16384 90607872 90640640 12 1801 9518 26 _ _ (458051 / 25000) (1832207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90640640 :
    ThetaLowerSegment 90640640 90673408 (4531339845607 / 50000) (4532939391127 / 50000) := by
  exact
    packedTile16384 90640640 90673408 12 1746 9520 26 _ _ (22903 / 1250) (1832243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90673408 :
    ThetaLowerSegment 90673408 90706176 (4532939391127 / 50000) (4534600349321 / 50000) := by
  exact
    packedTile16384 90673408 90706176 12 1813 9522 26 _ _ (458069 / 25000) (1832279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90706176 :
    ThetaLowerSegment 90706176 90738944 (4534600349321 / 50000) (4536220113129 / 50000) := by
  exact
    packedTile16384 90706176 90738944 12 1768 9523 26 _ _ (229039 / 12500) (366463 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90738944 :
    ThetaLowerSegment 90738944 90771712 (4536220113129 / 50000) (4537892130679 / 50000) := by
  exact
    packedTile16384 90738944 90771712 12 1825 9525 26 _ _ (458087 / 25000) (1832351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90771712 :
    ThetaLowerSegment 90771712 90804480 (4537892130679 / 50000) (4539533030551 / 50000) := by
  exact
    packedTile16384 90771712 90804480 12 1791 9527 26 _ _ (57262 / 3125) (1832387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90804480 :
    ThetaLowerSegment 90804480 90837248 (4539533030551 / 50000) (4541177627501 / 50000) := by
  exact
    packedTile16384 90804480 90837248 12 1795 9529 26 _ _ (91621 / 5000) (1832423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90837248 :
    ThetaLowerSegment 90837248 90870016 (4541177627501 / 50000) (4542782858957 / 50000) := by
  exact
    packedTile16384 90837248 90870016 12 1752 9530 26 _ _ (229057 / 12500) (1832459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90870016 :
    ThetaLowerSegment 90870016 90902784 (4542782858957 / 50000) (9088862372821 / 100000) := by
  exact
    packedTile16384 90870016 90902784 12 1799 9532 26 _ _ (1832493 / 100000) (114531 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90902784 :
    ThetaLowerSegment 90902784 90935552 (9088862372821 / 100000) (9092215900891 / 100000) := by
  exact
    packedTile16384 90902784 90935552 12 1830 9534 26 _ _ (1832529 / 100000) (458133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90935552 :
    ThetaLowerSegment 90935552 90968320 (9092215900891 / 100000) (9095514517891 / 100000) := by
  exact
    packedTile16384 90935552 90968320 12 1800 9536 26 _ _ (366513 / 20000) (229071 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell90968320 :
    ThetaLowerSegment 90968320 91001088 (9095514517891 / 100000) (4549354370717 / 50000) := by
  exact
    packedTile16384 90968320 91001088 12 1743 9537 26 _ _ (1832601 / 100000) (458151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91001088 :
    ThetaLowerSegment 91001088 91033856 (4549354370717 / 50000) (9102023981767 / 100000) := by
  exact
    packedTile16384 91001088 91033856 12 1809 9539 26 _ _ (1832637 / 100000) (11454 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91033856 :
    ThetaLowerSegment 91033856 91066624 (9102023981767 / 100000) (9105275143669 / 100000) := by
  exact
    packedTile16384 91033856 91066624 12 1774 9541 26 _ _ (1832673 / 100000) (458169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91066624 :
    ThetaLowerSegment 91066624 91099392 (9105275143669 / 100000) (9108530034853 / 100000) := by
  exact
    packedTile16384 91066624 91099392 12 1776 9542 26 _ _ (1832709 / 100000) (229089 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91099392 :
    ThetaLowerSegment 91099392 91132160 (9108530034853 / 100000) (9111799651933 / 100000) := by
  exact
    packedTile16384 91099392 91132160 12 1784 9544 26 _ _ (366549 / 20000) (458187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91132160 :
    ThetaLowerSegment 91132160 91164928 (9111799651933 / 100000) (284845401194 / 3125) := by
  exact
    packedTile16384 91132160 91164928 12 1775 9546 26 _ _ (1832781 / 100000) (114549 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91164928 :
    ThetaLowerSegment 91164928 91197696 (284845401194 / 3125) (2279600806921 / 25000) := by
  exact
    packedTile16384 91164928 91197696 12 1828 9548 26 _ _ (1832817 / 100000) (91641 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91197696 :
    ThetaLowerSegment 91197696 91230464 (2279600806921 / 25000) (4560856680101 / 50000) := by
  exact
    packedTile16384 91197696 91230464 12 1806 9549 26 _ _ (1832853 / 100000) (229107 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91230464 :
    ThetaLowerSegment 91230464 91263232 (4560856680101 / 50000) (4562500780637 / 50000) := by
  exact
    packedTile16384 91230464 91263232 12 1794 9551 26 _ _ (229111 / 12500) (1832891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91263232 :
    ThetaLowerSegment 91263232 91296000 (4562500780637 / 50000) (4564185237793 / 50000) := by
  exact
    packedTile16384 91263232 91296000 12 1838 9553 26 _ _ (458231 / 25000) (1832927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91296000 :
    ThetaLowerSegment 91296000 91328768 (4564185237793 / 50000) (4565800075553 / 50000) := by
  exact
    packedTile16384 91296000 91328768 12 1762 9554 26 _ _ (11456 / 625) (1832963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91328768 :
    ThetaLowerSegment 91328768 91361536 (4565800075553 / 50000) (4567455270941 / 50000) := by
  exact
    packedTile16384 91328768 91361536 12 1806 9556 26 _ _ (458249 / 25000) (1832999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91361536 :
    ThetaLowerSegment 91361536 91394304 (4567455270941 / 50000) (4569077504261 / 50000) := by
  exact
    packedTile16384 91361536 91394304 12 1770 9558 26 _ _ (229129 / 12500) (366607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91394304 :
    ThetaLowerSegment 91394304 91427072 (4569077504261 / 50000) (4570697019839 / 50000) := by
  exact
    packedTile16384 91394304 91427072 12 1767 9560 26 _ _ (458267 / 25000) (1833071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91427072 :
    ThetaLowerSegment 91427072 91459840 (4570697019839 / 50000) (914464413307 / 10000) := by
  exact
    packedTile16384 91427072 91459840 12 1773 9561 26 _ _ (114569 / 6250) (1833107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91459840 :
    ThetaLowerSegment 91459840 91492608 (914464413307 / 10000) (914793645251 / 10000) := by
  exact
    packedTile16384 91459840 91492608 12 1796 9563 26 _ _ (91657 / 5000) (1833143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91492608 :
    ThetaLowerSegment 91492608 91525376 (914793645251 / 10000) (1830238067627 / 20000) := by
  exact
    packedTile16384 91492608 91525376 12 1775 9565 26 _ _ (73327 / 4000) (916589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91525376 :
    ThetaLowerSegment 91525376 91558144 (1830238067627 / 20000) (1144313785407 / 12500) := by
  exact
    packedTile16384 91525376 91558144 12 1811 9566 26 _ _ (1833211 / 100000) (916607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91558144 :
    ThetaLowerSegment 91558144 91590912 (1144313785407 / 12500) (9157701966283 / 100000) := by
  exact
    packedTile16384 91558144 91590912 12 1741 9568 26 _ _ (1833247 / 100000) (7333 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91590912 :
    ThetaLowerSegment 91590912 91623680 (9157701966283 / 100000) (458051835403 / 5000) := by
  exact
    packedTile16384 91590912 91623680 12 1819 9570 26 _ _ (1833283 / 100000) (916643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91623680 :
    ThetaLowerSegment 91623680 91656448 (458051835403 / 5000) (9164360515407 / 100000) := by
  exact
    packedTile16384 91623680 91656448 12 1813 9572 26 _ _ (1833319 / 100000) (916661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91656448 :
    ThetaLowerSegment 91656448 91689216 (9164360515407 / 100000) (9167653219191 / 100000) := by
  exact
    packedTile16384 91656448 91689216 12 1796 9573 26 _ _ (916677 / 50000) (1833357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91689216 :
    ThetaLowerSegment 91689216 91721984 (9167653219191 / 100000) (9170975321871 / 100000) := by
  exact
    packedTile16384 91689216 91721984 12 1812 9575 26 _ _ (183339 / 10000) (1833393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91721984 :
    ThetaLowerSegment 91721984 91754752 (9170975321871 / 100000) (9174222319317 / 100000) := by
  exact
    packedTile16384 91721984 91754752 12 1771 9577 26 _ _ (916713 / 50000) (1833429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91754752 :
    ThetaLowerSegment 91754752 91787520 (9174222319317 / 100000) (2294371011609 / 25000) := by
  exact
    packedTile16384 91754752 91787520 12 1779 9578 26 _ _ (1833461 / 100000) (229183 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91787520 :
    ThetaLowerSegment 91787520 91820288 (2294371011609 / 25000) (9180701833671 / 100000) := by
  exact
    packedTile16384 91787520 91820288 12 1755 9580 26 _ _ (1833497 / 100000) (3667 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91820288 :
    ThetaLowerSegment 91820288 91853056 (9180701833671 / 100000) (9183928851751 / 100000) := by
  exact
    packedTile16384 91820288 91853056 12 1760 9582 26 _ _ (1833533 / 100000) (57298 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91853056 :
    ThetaLowerSegment 91853056 91885824 (9183928851751 / 100000) (1837437054059 / 20000) := by
  exact
    packedTile16384 91853056 91885824 12 1776 9584 26 _ _ (1833569 / 100000) (458393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91885824 :
    ThetaLowerSegment 91885824 91918592 (1837437054059 / 20000) (9190441750999 / 100000) := by
  exact
    packedTile16384 91885824 91918592 12 1776 9585 26 _ _ (458401 / 25000) (1833607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91918592 :
    ThetaLowerSegment 91918592 91951360 (9190441750999 / 100000) (9193767973959 / 100000) := by
  exact
    packedTile16384 91918592 91951360 12 1814 9587 26 _ _ (45841 / 2500) (1833643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91951360 :
    ThetaLowerSegment 91951360 91984128 (9193767973959 / 100000) (9197086927519 / 100000) := by
  exact
    packedTile16384 91951360 91984128 12 1810 9589 26 _ _ (458419 / 25000) (1833679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell91984128 :
    ThetaLowerSegment 91984128 92016896 (9197086927519 / 100000) (9200332595989 / 100000) := by
  exact
    packedTile16384 91984128 92016896 12 1770 9590 26 _ _ (1833711 / 100000) (916857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92016896 :
    ThetaLowerSegment 92016896 92049664 (9200332595989 / 100000) (230090512609 / 2500) := by
  exact
    packedTile16384 92016896 92049664 12 1793 9592 26 _ _ (1833747 / 100000) (1467 / 80) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92049664 :
    ThetaLowerSegment 92049664 92082432 (230090512609 / 2500) (4603445068833 / 50000) := by
  exact
    packedTile16384 92049664 92082432 12 1783 9594 26 _ _ (916891 / 50000) (366757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92082432 :
    ThetaLowerSegment 92082432 92115200 (4603445068833 / 50000) (460508908667 / 5000) := by
  exact
    packedTile16384 92082432 92115200 12 1793 9595 26 _ _ (916909 / 50000) (1833821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92115200 :
    ThetaLowerSegment 92115200 92147968 (460508908667 / 5000) (2303366109927 / 25000) := by
  exact
    packedTile16384 92115200 92147968 12 1792 9597 26 _ _ (916927 / 50000) (1833857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92147968 :
    ThetaLowerSegment 92147968 92180736 (2303366109927 / 25000) (4608355211619 / 50000) := by
  exact
    packedTile16384 92147968 92180736 12 1770 9599 26 _ _ (1833889 / 100000) (458473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92180736 :
    ThetaLowerSegment 92180736 92213504 (4608355211619 / 50000) (9220035329263 / 100000) := by
  exact
    packedTile16384 92180736 92213504 12 1813 9601 26 _ _ (73357 / 4000) (229241 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92213504 :
    ThetaLowerSegment 92213504 92246272 (9220035329263 / 100000) (9223250261143 / 100000) := by
  exact
    packedTile16384 92213504 92246272 12 1753 9602 26 _ _ (45849 / 2500) (1833963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92246272 :
    ThetaLowerSegment 92246272 92279040 (9223250261143 / 100000) (9226498268059 / 100000) := by
  exact
    packedTile16384 92246272 92279040 12 1771 9604 26 _ _ (458499 / 25000) (1833999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92279040 :
    ThetaLowerSegment 92279040 92311808 (9226498268059 / 100000) (4614886006697 / 50000) := by
  exact
    packedTile16384 92279040 92311808 12 1785 9606 26 _ _ (1834031 / 100000) (917017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92311808 :
    ThetaLowerSegment 92311808 92344576 (4614886006697 / 50000) (9233020146051 / 100000) := by
  exact
    packedTile16384 92311808 92344576 12 1771 9607 26 _ _ (1834067 / 100000) (183407 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92344576 :
    ThetaLowerSegment 92344576 92377344 (9233020146051 / 100000) (9236264672489 / 100000) := by
  exact
    packedTile16384 92344576 92377344 12 1769 9609 26 _ _ (917051 / 50000) (366821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92377344 :
    ThetaLowerSegment 92377344 92410112 (9236264672489 / 100000) (1847913957833 / 20000) := by
  exact
    packedTile16384 92377344 92410112 12 1802 9611 26 _ _ (917069 / 50000) (1834141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92410112 :
    ThetaLowerSegment 92410112 92442880 (1847913957833 / 20000) (4621425562331 / 50000) := by
  exact
    packedTile16384 92410112 92442880 12 1789 9613 26 _ _ (1834173 / 100000) (57318 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92442880 :
    ThetaLowerSegment 92442880 92475648 (4621425562331 / 50000) (4623080018849 / 50000) := by
  exact
    packedTile16384 92442880 92475648 12 1804 9614 26 _ _ (1834209 / 100000) (458553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92475648 :
    ThetaLowerSegment 92475648 92508416 (4623080018849 / 50000) (4624725335717 / 50000) := by
  exact
    packedTile16384 92475648 92508416 12 1794 9616 26 _ _ (458561 / 25000) (1834247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92508416 :
    ThetaLowerSegment 92508416 92541184 (4624725335717 / 50000) (4626339502117 / 50000) := by
  exact
    packedTile16384 92508416 92541184 12 1760 9618 26 _ _ (45857 / 2500) (1834283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92541184 :
    ThetaLowerSegment 92541184 92573952 (4626339502117 / 50000) (1156998054983 / 12500) := by
  exact
    packedTile16384 92541184 92573952 12 1802 9619 26 _ _ (366863 / 20000) (917159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92573952 :
    ThetaLowerSegment 92573952 92606720 (1156998054983 / 12500) (4629594524657 / 50000) := by
  exact
    packedTile16384 92573952 92606720 12 1747 9621 26 _ _ (36687 / 2000) (1834353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92606720 :
    ThetaLowerSegment 92606720 92639488 (4629594524657 / 50000) (4631271153461 / 50000) := by
  exact
    packedTile16384 92606720 92639488 12 1828 9623 26 _ _ (917193 / 50000) (1834389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92639488 :
    ThetaLowerSegment 92639488 92672256 (4631271153461 / 50000) (9265780059987 / 100000) := by
  exact
    packedTile16384 92639488 92672256 12 1765 9624 26 _ _ (1834421 / 100000) (229303 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92672256 :
    ThetaLowerSegment 92672256 92705024 (9265780059987 / 100000) (9269129776643 / 100000) := by
  exact
    packedTile16384 92672256 92705024 12 1826 9626 26 _ _ (229307 / 12500) (1834459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92705024 :
    ThetaLowerSegment 92705024 92737792 (9269129776643 / 100000) (9272404344863 / 100000) := by
  exact
    packedTile16384 92705024 92737792 12 1785 9628 26 _ _ (458623 / 25000) (366899 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92737792 :
    ThetaLowerSegment 92737792 92770560 (9272404344863 / 100000) (2318920661153 / 25000) := by
  exact
    packedTile16384 92737792 92770560 12 1787 9630 26 _ _ (1834527 / 100000) (183453 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92770560 :
    ThetaLowerSegment 92770560 92803328 (2318920661153 / 25000) (4639476834329 / 50000) := by
  exact
    packedTile16384 92770560 92803328 12 1783 9631 26 _ _ (917281 / 50000) (366913 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92803328 :
    ThetaLowerSegment 92803328 92836096 (4639476834329 / 50000) (1160285891653 / 12500) := by
  exact
    packedTile16384 92803328 92836096 12 1817 9633 26 _ _ (917299 / 50000) (1834601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92836096 :
    ThetaLowerSegment 92836096 92868864 (1160285891653 / 12500) (9285514252671 / 100000) := by
  exact
    packedTile16384 92836096 92868864 12 1759 9635 26 _ _ (1834633 / 100000) (458659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92868864 :
    ThetaLowerSegment 92868864 92901632 (9285514252671 / 100000) (9288846009759 / 100000) := by
  exact
    packedTile16384 92868864 92901632 12 1816 9636 26 _ _ (458667 / 25000) (1834671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92901632 :
    ThetaLowerSegment 92901632 92934400 (9288846009759 / 100000) (9292124625807 / 100000) := by
  exact
    packedTile16384 92901632 92934400 12 1787 9638 26 _ _ (114669 / 6250) (1834707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92934400 :
    ThetaLowerSegment 92934400 92967168 (9292124625807 / 100000) (9295368444359 / 100000) := by
  exact
    packedTile16384 92934400 92967168 12 1768 9640 26 _ _ (1834739 / 100000) (917371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92967168 :
    ThetaLowerSegment 92967168 92999936 (9295368444359 / 100000) (1859704484173 / 20000) := by
  exact
    packedTile16384 92967168 92999936 12 1719 9641 26 _ _ (917387 / 50000) (1834777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell92999936 :
    ThetaLowerSegment 92999936 93032704 (1859704484173 / 20000) (9301755354323 / 100000) := by
  exact
    packedTile16384 92999936 93032704 12 1762 9643 26 _ _ (1834809 / 100000) (458703 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93032704 :
    ThetaLowerSegment 93032704 93065472 (9301755354323 / 100000) (2326252133627 / 25000) := by
  exact
    packedTile16384 93032704 93065472 12 1773 9645 26 _ _ (366969 / 20000) (57339 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93065472 :
    ThetaLowerSegment 93065472 93098240 (2326252133627 / 25000) (2327070490107 / 25000) := by
  exact
    packedTile16384 93065472 93098240 12 1784 9647 26 _ _ (11468 / 625) (1834883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93098240 :
    ThetaLowerSegment 93098240 93131008 (2327070490107 / 25000) (9311538934553 / 100000) := by
  exact
    packedTile16384 93098240 93131008 12 1775 9648 26 _ _ (366983 / 20000) (917459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93131008 :
    ThetaLowerSegment 93131008 93147392 (9311538934553 / 100000) (9313184884703 / 100000) := by
  exact
    packedTile16384 93131008 93147392 11 897 9650 26 _ _ (36699 / 2000) (1834953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93147392 :
    ThetaLowerSegment 93147392 93163776 (9313184884703 / 100000) (9314845530743 / 100000) := by
  exact
    packedTile16384 93147392 93163776 11 905 9651 26 _ _ (229371 / 12500) (1834971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93163776 :
    ThetaLowerSegment 93163776 93196544 (9314845530743 / 100000) (1164772462311 / 12500) := by
  exact
    packedTile16384 93163776 93196544 12 1817 9652 26 _ _ (366997 / 20000) (458747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93196544 :
    ThetaLowerSegment 93196544 93229312 (1164772462311 / 12500) (1864280766077 / 20000) := by
  exact
    packedTile16384 93196544 93229312 12 1757 9653 26 _ _ (1835021 / 100000) (114689 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93229312 :
    ThetaLowerSegment 93229312 93262080 (1864280766077 / 20000) (9324673900177 / 100000) := by
  exact
    packedTile16384 93229312 93262080 12 1782 9655 26 _ _ (114691 / 6250) (1835059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93262080 :
    ThetaLowerSegment 93262080 93294848 (9324673900177 / 100000) (9327903660337 / 100000) := by
  exact
    packedTile16384 93262080 93294848 12 1760 9657 26 _ _ (1835091 / 100000) (917547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93294848 :
    ThetaLowerSegment 93294848 93311232 (9327903660337 / 100000) (9329538757603 / 100000) := by
  exact
    packedTile16384 93294848 93311232 11 891 9658 26 _ _ (917563 / 50000) (1835129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93311232 :
    ThetaLowerSegment 93311232 93327616 (9329538757603 / 100000) (9331221584651 / 100000) := by
  exact
    packedTile16384 93311232 93327616 11 917 9659 26 _ _ (229393 / 12500) (1835147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93327616 :
    ThetaLowerSegment 93327616 93360384 (9331221584651 / 100000) (2333642688369 / 25000) := by
  exact
    packedTile16384 93327616 93360384 12 1825 9660 26 _ _ (1835161 / 100000) (458791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93360384 :
    ThetaLowerSegment 93360384 93393152 (2333642688369 / 25000) (583614952347 / 6250) := by
  exact
    packedTile16384 93360384 93393152 12 1781 9662 26 _ _ (458799 / 25000) (1835199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93393152 :
    ThetaLowerSegment 93393152 93425920 (583614952347 / 6250) (373644458177 / 4000) := by
  exact
    packedTile16384 93393152 93425920 12 1783 9664 26 _ _ (1835231 / 100000) (917617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93425920 :
    ThetaLowerSegment 93425920 93458688 (373644458177 / 4000) (9344372722107 / 100000) := by
  exact
    packedTile16384 93425920 93458688 12 1777 9665 26 _ _ (917633 / 50000) (1835269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93458688 :
    ThetaLowerSegment 93458688 93491456 (9344372722107 / 100000) (9347630383157 / 100000) := by
  exact
    packedTile16384 93458688 93491456 12 1775 9667 26 _ _ (917651 / 50000) (367061 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93491456 :
    ThetaLowerSegment 93491456 93524224 (9347630383157 / 100000) (9350985379193 / 100000) := by
  exact
    packedTile16384 93491456 93524224 12 1828 9669 26 _ _ (1835337 / 100000) (91767 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93524224 :
    ThetaLowerSegment 93524224 93556992 (9350985379193 / 100000) (9354200950937 / 100000) := by
  exact
    packedTile16384 93524224 93556992 12 1752 9670 26 _ _ (458843 / 25000) (14683 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93556992 :
    ThetaLowerSegment 93556992 93589760 (9354200950937 / 100000) (584842322027 / 6250) := by
  exact
    packedTile16384 93556992 93589760 12 1785 9672 26 _ _ (1835407 / 100000) (183541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93589760 :
    ThetaLowerSegment 93589760 93622528 (584842322027 / 6250) (4680367530991 / 50000) := by
  exact
    packedTile16384 93589760 93622528 12 1775 9674 26 _ _ (917721 / 50000) (367089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93622528 :
    ThetaLowerSegment 93622528 93655296 (4680367530991 / 50000) (1872796404159 / 20000) := by
  exact
    packedTile16384 93622528 93655296 12 1769 9675 26 _ _ (1835477 / 100000) (45887 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93655296 :
    ThetaLowerSegment 93655296 93688064 (1872796404159 / 20000) (9367252903179 / 100000) := by
  exact
    packedTile16384 93655296 93688064 12 1782 9677 26 _ _ (229439 / 12500) (367103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93688064 :
    ThetaLowerSegment 93688064 93720832 (9367252903179 / 100000) (4685231637441 / 50000) := by
  exact
    packedTile16384 93688064 93720832 12 1749 9679 26 _ _ (1835547 / 100000) (36711 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93720832 :
    ThetaLowerSegment 93720832 93737216 (4685231637441 / 50000) (1171512806201 / 12500) := by
  exact
    packedTile16384 93720832 93737216 11 893 9680 26 _ _ (917791 / 50000) (367117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93737216 :
    ThetaLowerSegment 93737216 93753600 (1171512806201 / 12500) (9373748981911 / 100000) := by
  exact
    packedTile16384 93737216 93753600 11 897 9681 26 _ _ (1835599 / 100000) (917801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93753600 :
    ThetaLowerSegment 93753600 93769984 (9373748981911 / 100000) (9375434078317 / 100000) := by
  exact
    packedTile16384 93753600 93769984 11 918 9682 26 _ _ (1835617 / 100000) (91781 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93769984 :
    ThetaLowerSegment 93769984 93802752 (9375434078317 / 100000) (9378615232039 / 100000) := by
  exact
    packedTile16384 93769984 93802752 12 1733 9683 26 _ _ (917817 / 50000) (1835637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93802752 :
    ThetaLowerSegment 93802752 93819136 (9378615232039 / 100000) (4690162119939 / 50000) := by
  exact
    packedTile16384 93802752 93819136 11 931 9685 26 _ _ (1835669 / 100000) (229459 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93819136 :
    ThetaLowerSegment 93819136 93835520 (4690162119939 / 50000) (117274406167 / 1250) := by
  exact
    packedTile16384 93819136 93835520 11 887 9686 26 _ _ (917843 / 50000) (1835689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93835520 :
    ThetaLowerSegment 93835520 93851904 (117274406167 / 1250) (1172945300721 / 12500) := by
  exact
    packedTile16384 93835520 93851904 11 877 9686 26 _ _ (229463 / 12500) (1835707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93851904 :
    ThetaLowerSegment 93851904 93868288 (1172945300721 / 12500) (938521822611 / 10000) := by
  exact
    packedTile16384 93851904 93868288 11 902 9687 26 _ _ (1835721 / 100000) (458931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93868288 :
    ThetaLowerSegment 93868288 93884672 (938521822611 / 10000) (938687039121 / 10000) := by
  exact
    packedTile16384 93868288 93884672 11 900 9688 26 _ _ (1835739 / 100000) (917871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93884672 :
    ThetaLowerSegment 93884672 93901056 (938687039121 / 10000) (4694275971853 / 50000) := by
  exact
    packedTile16384 93884672 93901056 11 916 9689 26 _ _ (458939 / 25000) (1835759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93901056 :
    ThetaLowerSegment 93901056 93933824 (4694275971853 / 50000) (4695935511549 / 50000) := by
  exact
    packedTile16384 93901056 93933824 12 1808 9690 26 _ _ (917887 / 50000) (1835777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93933824 :
    ThetaLowerSegment 93933824 93966592 (4695935511549 / 50000) (4697562038323 / 50000) := by
  exact
    packedTile16384 93933824 93966592 12 1772 9691 26 _ _ (1835809 / 100000) (458953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93966592 :
    ThetaLowerSegment 93966592 93999360 (4697562038323 / 50000) (9398349652797 / 100000) := by
  exact
    packedTile16384 93966592 93999360 12 1757 9693 26 _ _ (1835843 / 100000) (917923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell93999360 :
    ThetaLowerSegment 93999360 94015744 (9398349652797 / 100000) (1879998919897 / 20000) := by
  exact
    packedTile16384 93999360 94015744 11 896 9695 26 _ _ (917939 / 50000) (1835881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94015744 :
    ThetaLowerSegment 94015744 94032128 (1879998919897 / 20000) (9401725849413 / 100000) := by
  exact
    packedTile16384 94015744 94032128 11 943 9696 26 _ _ (229487 / 12500) (1835899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94032128 :
    ThetaLowerSegment 94032128 94064896 (9401725849413 / 100000) (9405045180117 / 100000) := by
  exact
    packedTile16384 94032128 94064896 12 1808 9697 26 _ _ (1835913 / 100000) (458979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94064896 :
    ThetaLowerSegment 94064896 94097664 (9405045180117 / 100000) (9408346214621 / 100000) := by
  exact
    packedTile16384 94064896 94097664 12 1798 9698 26 _ _ (458987 / 25000) (1835951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94097664 :
    ThetaLowerSegment 94097664 94130432 (9408346214621 / 100000) (9411599576497 / 100000) := by
  exact
    packedTile16384 94097664 94130432 12 1772 9700 26 _ _ (1835983 / 100000) (917993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94130432 :
    ThetaLowerSegment 94130432 94163200 (9411599576497 / 100000) (1882975740929 / 20000) := by
  exact
    packedTile16384 94130432 94163200 12 1786 9702 26 _ _ (918009 / 50000) (1836021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94163200 :
    ThetaLowerSegment 94163200 94195968 (1882975740929 / 20000) (1177261704181 / 12500) := by
  exact
    packedTile16384 94163200 94195968 12 1751 9703 26 _ _ (1836053 / 100000) (229507 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94195968 :
    ThetaLowerSegment 94195968 94228736 (1177261704181 / 12500) (2355351483599 / 25000) := by
  exact
    packedTile16384 94195968 94228736 12 1804 9705 26 _ _ (1836087 / 100000) (183609 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94228736 :
    ThetaLowerSegment 94228736 94261504 (2355351483599 / 25000) (4712339869961 / 50000) := by
  exact
    packedTile16384 94228736 94261504 12 1783 9707 26 _ _ (918061 / 50000) (14689 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94261504 :
    ThetaLowerSegment 94261504 94294272 (4712339869961 / 50000) (4713985066633 / 50000) := by
  exact
    packedTile16384 94261504 94294272 12 1792 9708 26 _ _ (1836157 / 100000) (11476 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94294272 :
    ThetaLowerSegment 94294272 94327040 (4713985066633 / 50000) (4715605506073 / 50000) := by
  exact
    packedTile16384 94294272 94327040 12 1765 9710 26 _ _ (57381 / 3125) (367239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94327040 :
    ThetaLowerSegment 94327040 94359808 (4715605506073 / 50000) (1179307871049 / 12500) := by
  exact
    packedTile16384 94327040 94359808 12 1771 9712 26 _ _ (918113 / 50000) (1836229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94359808 :
    ThetaLowerSegment 94359808 94392576 (1179307871049 / 12500) (1887547404351 / 20000) := by
  exact
    packedTile16384 94359808 94392576 12 1783 9713 26 _ _ (1836261 / 100000) (229533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94392576 :
    ThetaLowerSegment 94392576 94425344 (1887547404351 / 20000) (9440992774563 / 100000) := by
  exact
    packedTile16384 94392576 94425344 12 1773 9715 26 _ _ (229537 / 12500) (1836299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94425344 :
    ThetaLowerSegment 94425344 94458112 (9440992774563 / 100000) (37777023739 / 400) := by
  exact
    packedTile16384 94425344 94458112 12 1777 9717 26 _ _ (1836331 / 100000) (918167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94458112 :
    ThetaLowerSegment 94458112 94490880 (37777023739 / 400) (37790245567 / 400) := by
  exact
    packedTile16384 94458112 94490880 12 1800 9718 26 _ _ (367273 / 20000) (114773 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94490880 :
    ThetaLowerSegment 94490880 94523648 (37790245567 / 400) (189017632059 / 2000) := by
  exact
    packedTile16384 94490880 94523648 12 1808 9720 26 _ _ (4591 / 250) (1836403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94523648 :
    ThetaLowerSegment 94523648 94556416 (189017632059 / 2000) (1890831193311 / 20000) := by
  exact
    packedTile16384 94523648 94556416 12 1783 9722 26 _ _ (367287 / 20000) (918219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94556416 :
    ThetaLowerSegment 94556416 94589184 (1890831193311 / 20000) (9457366114367 / 100000) := by
  exact
    packedTile16384 94556416 94589184 12 1748 9724 26 _ _ (1836469 / 100000) (229559 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94589184 :
    ThetaLowerSegment 94589184 94621952 (9457366114367 / 100000) (1892136935419 / 20000) := by
  exact
    packedTile16384 94589184 94621952 12 1807 9725 26 _ _ (229563 / 12500) (1836507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94621952 :
    ThetaLowerSegment 94621952 94654720 (1892136935419 / 20000) (9463950043437 / 100000) := by
  exact
    packedTile16384 94621952 94654720 12 1778 9727 26 _ _ (1836539 / 100000) (918271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94654720 :
    ThetaLowerSegment 94654720 94687488 (9463950043437 / 100000) (2366807999847 / 25000) := by
  exact
    packedTile16384 94654720 94687488 12 1787 9729 26 _ _ (1836573 / 100000) (57393 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94687488 :
    ThetaLowerSegment 94687488 94720256 (2366807999847 / 25000) (473521752187 / 5000) := by
  exact
    packedTile16384 94687488 94720256 12 1744 9730 26 _ _ (57394 / 3125) (1836611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94720256 :
    ThetaLowerSegment 94720256 94736640 (473521752187 / 5000) (296003554204 / 3125) := by
  exact
    packedTile16384 94720256 94736640 11 914 9732 26 _ _ (918321 / 50000) (367329 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94736640 :
    ThetaLowerSegment 94736640 94769408 (296003554204 / 3125) (296106866329 / 3125) := by
  exact
    packedTile16384 94736640 94769408 12 1800 9733 26 _ _ (91833 / 5000) (1836663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94769408 :
    ThetaLowerSegment 94769408 94802176 (296106866329 / 3125) (4739354620741 / 50000) := by
  exact
    packedTile16384 94769408 94802176 12 1791 9734 26 _ _ (918347 / 50000) (1836697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94802176 :
    ThetaLowerSegment 94802176 94834944 (4739354620741 / 50000) (9482109026861 / 100000) := by
  exact
    packedTile16384 94802176 94834944 12 1851 9736 26 _ _ (1836729 / 100000) (459183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94834944 :
    ThetaLowerSegment 94834944 94867712 (9482109026861 / 100000) (9485396832631 / 100000) := by
  exact
    packedTile16384 94834944 94867712 12 1790 9738 26 _ _ (1836763 / 100000) (918383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94867712 :
    ThetaLowerSegment 94867712 94900480 (9485396832631 / 100000) (9488701232233 / 100000) := by
  exact
    packedTile16384 94867712 94900480 12 1799 9740 26 _ _ (918399 / 50000) (1836801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94900480 :
    ThetaLowerSegment 94900480 94933248 (9488701232233 / 100000) (9492062634793 / 100000) := by
  exact
    packedTile16384 94900480 94933248 12 1830 9741 26 _ _ (57401 / 3125) (367367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94933248 :
    ThetaLowerSegment 94933248 94966016 (9492062634793 / 100000) (237383352373 / 2500) := by
  exact
    packedTile16384 94933248 94966016 12 1781 9743 27 _ _ (1836867 / 100000) (183687 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94966016 :
    ThetaLowerSegment 94966016 94998784 (237383352373 / 2500) (9498646027423 / 100000) := by
  exact
    packedTile16384 94966016 94998784 12 1803 9745 27 _ _ (1836901 / 100000) (229613 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell94998784 :
    ThetaLowerSegment 94998784 95031552 (9498646027423 / 100000) (1900376541731 / 20000) := by
  exact
    packedTile16384 94998784 95031552 12 1762 9746 27 _ _ (229617 / 12500) (1836939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95031552 :
    ThetaLowerSegment 95031552 95064320 (1900376541731 / 20000) (1901028666081 / 20000) := by
  exact
    packedTile16384 95031552 95064320 12 1775 9748 27 _ _ (183697 / 10000) (1836973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95064320 :
    ThetaLowerSegment 95064320 95097088 (1901028666081 / 20000) (380335352289 / 4000) := by
  exact
    packedTile16384 95064320 95097088 12 1764 9750 27 _ _ (367401 / 20000) (114813 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95097088 :
    ThetaLowerSegment 95097088 95129856 (380335352289 / 4000) (1902327073251 / 20000) := by
  exact
    packedTile16384 95097088 95129856 12 1770 9751 27 _ _ (1837039 / 100000) (918521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95129856 :
    ThetaLowerSegment 95129856 95162624 (1902327073251 / 20000) (9514925565789 / 100000) := by
  exact
    packedTile16384 95129856 95162624 12 1791 9753 27 _ _ (918537 / 50000) (1837077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95162624 :
    ThetaLowerSegment 95162624 95195392 (9514925565789 / 100000) (380728706533 / 4000) := by
  exact
    packedTile16384 95162624 95195392 12 1792 9755 27 _ _ (459277 / 25000) (1837111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95195392 :
    ThetaLowerSegment 95195392 95228160 (380728706533 / 4000) (9521550240727 / 100000) := by
  exact
    packedTile16384 95195392 95228160 12 1814 9756 27 _ _ (1837143 / 100000) (918573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95228160 :
    ThetaLowerSegment 95228160 95260928 (9521550240727 / 100000) (9524765300477 / 100000) := by
  exact
    packedTile16384 95228160 95260928 12 1750 9758 27 _ _ (1837177 / 100000) (91859 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95260928 :
    ThetaLowerSegment 95260928 95293696 (9524765300477 / 100000) (9528057584381 / 100000) := by
  exact
    packedTile16384 95260928 95293696 12 1792 9760 27 _ _ (459303 / 25000) (367443 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95293696 :
    ThetaLowerSegment 95293696 95326464 (9528057584381 / 100000) (9531340742983 / 100000) := by
  exact
    packedTile16384 95293696 95326464 12 1787 9761 27 _ _ (918623 / 50000) (1837249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95326464 :
    ThetaLowerSegment 95326464 95359232 (9531340742983 / 100000) (9534557820263 / 100000) := by
  exact
    packedTile16384 95326464 95359232 12 1751 9763 27 _ _ (11483 / 625) (1837283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95359232 :
    ThetaLowerSegment 95359232 95392000 (9534557820263 / 100000) (4768929737659 / 50000) := by
  exact
    packedTile16384 95359232 95392000 12 1797 9765 27 _ _ (367463 / 20000) (918659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95392000 :
    ThetaLowerSegment 95392000 95424768 (4768929737659 / 50000) (4770594375853 / 50000) := by
  exact
    packedTile16384 95392000 95424768 12 1812 9766 27 _ _ (1837349 / 100000) (229669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95424768 :
    ThetaLowerSegment 95424768 95457536 (4770594375853 / 50000) (2386119416819 / 25000) := by
  exact
    packedTile16384 95424768 95457536 12 1790 9768 27 _ _ (1837383 / 100000) (918693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95457536 :
    ThetaLowerSegment 95457536 95490304 (2386119416819 / 25000) (954784565447 / 10000) := by
  exact
    packedTile16384 95457536 95490304 12 1833 9770 27 _ _ (918709 / 50000) (1837421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95490304 :
    ThetaLowerSegment 95490304 95523072 (954784565447 / 10000) (4775563671871 / 50000) := by
  exact
    packedTile16384 95490304 95523072 12 1786 9771 27 _ _ (459363 / 25000) (367491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95523072 :
    ThetaLowerSegment 95523072 95555840 (4775563671871 / 50000) (955444951843 / 10000) := by
  exact
    packedTile16384 95523072 95555840 12 1808 9773 27 _ _ (918743 / 50000) (1837489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95555840 :
    ThetaLowerSegment 95555840 95588608 (955444951843 / 10000) (4778830752569 / 50000) := by
  exact
    packedTile16384 95555840 95588608 12 1748 9775 27 _ _ (1837521 / 100000) (459381 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95588608 :
    ThetaLowerSegment 95588608 95621376 (4778830752569 / 50000) (1195108734521 / 12500) := by
  exact
    packedTile16384 95588608 95621376 12 1746 9776 27 _ _ (367511 / 20000) (918779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95621376 :
    ThetaLowerSegment 95621376 95654144 (1195108734521 / 12500) (298879629217 / 3125) := by
  exact
    packedTile16384 95621376 95654144 12 1784 9778 27 _ _ (1837589 / 100000) (229699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95654144 :
    ThetaLowerSegment 95654144 95686912 (298879629217 / 3125) (9567435642491 / 100000) := by
  exact
    packedTile16384 95654144 95686912 12 1789 9780 27 _ _ (1837623 / 100000) (918813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95686912 :
    ThetaLowerSegment 95686912 95719680 (9567435642491 / 100000) (9570651543991 / 100000) := by
  exact
    packedTile16384 95686912 95719680 12 1750 9781 27 _ _ (918829 / 50000) (1837661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95719680 :
    ThetaLowerSegment 95719680 95752448 (9570651543991 / 100000) (9573874855759 / 100000) := by
  exact
    packedTile16384 95719680 95752448 12 1754 9783 27 _ _ (459423 / 25000) (367539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95752448 :
    ThetaLowerSegment 95752448 95785216 (9573874855759 / 100000) (9577164385299 / 100000) := by
  exact
    packedTile16384 95752448 95785216 12 1790 9785 27 _ _ (918863 / 50000) (1837729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95785216 :
    ThetaLowerSegment 95785216 95817984 (9577164385299 / 100000) (9580455813459 / 100000) := by
  exact
    packedTile16384 95785216 95817984 12 1791 9786 27 _ _ (11486 / 625) (1837763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95817984 :
    ThetaLowerSegment 95817984 95850752 (9580455813459 / 100000) (2395938663871 / 25000) := by
  exact
    packedTile16384 95817984 95850752 12 1795 9788 27 _ _ (367559 / 20000) (918899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95850752 :
    ThetaLowerSegment 95850752 95883520 (2395938663871 / 25000) (4793536887329 / 50000) := by
  exact
    packedTile16384 95850752 95883520 12 1806 9790 27 _ _ (1837829 / 100000) (229729 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95883520 :
    ThetaLowerSegment 95883520 95916288 (4793536887329 / 50000) (9590376414469 / 100000) := by
  exact
    packedTile16384 95883520 95916288 12 1797 9792 27 _ _ (1837863 / 100000) (918933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95916288 :
    ThetaLowerSegment 95916288 95949056 (9590376414469 / 100000) (9593629492159 / 100000) := by
  exact
    packedTile16384 95916288 95949056 12 1770 9793 27 _ _ (1837897 / 100000) (18379 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95949056 :
    ThetaLowerSegment 95949056 95981824 (9593629492159 / 100000) (4798495533979 / 50000) := by
  exact
    packedTile16384 95949056 95981824 12 1829 9795 27 _ _ (1837931 / 100000) (918967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell95981824 :
    ThetaLowerSegment 95981824 96014592 (4798495533979 / 50000) (1200026857321 / 12500) := by
  exact
    packedTile16384 95981824 96014592 12 1754 9797 27 _ _ (367593 / 20000) (114873 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96014592 :
    ThetaLowerSegment 96014592 96047360 (1200026857321 / 12500) (1200436042071 / 12500) := by
  exact
    packedTile16384 96014592 96047360 12 1781 9798 27 _ _ (919 / 50) (1838003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96047360 :
    ThetaLowerSegment 96047360 96080128 (1200436042071 / 12500) (1200838571517 / 12500) := by
  exact
    packedTile16384 96047360 96080128 12 1752 9800 27 _ _ (919017 / 50000) (1838037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96080128 :
    ThetaLowerSegment 96080128 96112896 (1200838571517 / 12500) (300313378842 / 3125) := by
  exact
    packedTile16384 96080128 96112896 12 1806 9802 27 _ _ (459517 / 25000) (1838071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96112896 :
    ThetaLowerSegment 96112896 96145664 (300313378842 / 3125) (4806623319773 / 50000) := by
  exact
    packedTile16384 96112896 96145664 12 1751 9803 27 _ _ (919051 / 50000) (367621 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96145664 :
    ThetaLowerSegment 96145664 96178432 (4806623319773 / 50000) (4808312566757 / 50000) := by
  exact
    packedTile16384 96145664 96178432 12 1838 9805 27 _ _ (229767 / 12500) (1838139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96178432 :
    ThetaLowerSegment 96178432 96211200 (4808312566757 / 50000) (4809889716617 / 50000) := by
  exact
    packedTile16384 96178432 96211200 12 1716 9807 27 _ _ (183817 / 10000) (1838173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96211200 :
    ThetaLowerSegment 96211200 96243968 (4809889716617 / 50000) (962298526101 / 10000) := by
  exact
    packedTile16384 96211200 96243968 12 1744 9808 27 _ _ (459551 / 25000) (1838207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96243968 :
    ThetaLowerSegment 96243968 96276736 (962298526101 / 10000) (601644414597 / 6250) := by
  exact
    packedTile16384 96243968 96276736 12 1809 9810 27 _ _ (919119 / 50000) (1838241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96276736 :
    ThetaLowerSegment 96276736 96309504 (601644414597 / 6250) (601846854301 / 6250) := by
  exact
    packedTile16384 96276736 96309504 12 1762 9812 27 _ _ (57446 / 3125) (73531 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96309504 :
    ThetaLowerSegment 96309504 96342272 (601846854301 / 6250) (963285678131 / 10000) := by
  exact
    packedTile16384 96309504 96342272 12 1799 9813 27 _ _ (919153 / 50000) (1838309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96342272 :
    ThetaLowerSegment 96342272 96375040 (963285678131 / 10000) (963609593639 / 10000) := by
  exact
    packedTile16384 96342272 96375040 12 1762 9815 27 _ _ (91917 / 5000) (1838343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96375040 :
    ThetaLowerSegment 96375040 96407808 (963609593639 / 10000) (4819719050161 / 50000) := by
  exact
    packedTile16384 96375040 96407808 12 1818 9817 27 _ _ (919187 / 50000) (1838377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96407808 :
    ThetaLowerSegment 96407808 96440576 (4819719050161 / 50000) (4821385567013 / 50000) := by
  exact
    packedTile16384 96407808 96440576 12 1813 9818 27 _ _ (229801 / 12500) (1838411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96440576 :
    ThetaLowerSegment 96440576 96473344 (4821385567013 / 50000) (48229914461 / 500) := by
  exact
    packedTile16384 96440576 96473344 12 1747 9820 27 _ _ (919221 / 50000) (367689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96473344 :
    ThetaLowerSegment 96473344 96506112 (48229914461 / 500) (2412307869823 / 25000) := by
  exact
    packedTile16384 96473344 96506112 12 1767 9822 27 _ _ (459619 / 25000) (1838479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96506112 :
    ThetaLowerSegment 96506112 96538880 (2412307869823 / 25000) (603276215977 / 6250) := by
  exact
    packedTile16384 96506112 96538880 12 1734 9823 27 _ _ (183851 / 10000) (1838513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96538880 :
    ThetaLowerSegment 96538880 96571648 (603276215977 / 6250) (603485809993 / 6250) := by
  exact
    packedTile16384 96538880 96571648 12 1824 9825 27 _ _ (114909 / 6250) (1838547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96571648 :
    ThetaLowerSegment 96571648 96604416 (603485809993 / 6250) (60369081144 / 625) := by
  exact
    packedTile16384 96571648 96604416 12 1784 9827 27 _ _ (919289 / 50000) (1838581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96604416 :
    ThetaLowerSegment 96604416 96637184 (60369081144 / 625) (2415608547627 / 25000) := by
  exact
    packedTile16384 96604416 96637184 12 1839 9828 27 _ _ (459653 / 25000) (367723 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96637184 :
    ThetaLowerSegment 96637184 96669952 (2415608547627 / 25000) (2416430422389 / 25000) := by
  exact
    packedTile16384 96637184 96669952 12 1788 9830 27 _ _ (919323 / 50000) (1838649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96669952 :
    ThetaLowerSegment 96669952 96702720 (2416430422389 / 25000) (2417258288059 / 25000) := by
  exact
    packedTile16384 96669952 96702720 12 1801 9832 27 _ _ (45967 / 2500) (1838683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96702720 :
    ThetaLowerSegment 96702720 96735488 (2417258288059 / 25000) (4836130047653 / 50000) := by
  exact
    packedTile16384 96702720 96735488 12 1755 9833 27 _ _ (919357 / 50000) (1838717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96735488 :
    ThetaLowerSegment 96735488 96768256 (4836130047653 / 50000) (4837770210869 / 50000) := by
  exact
    packedTile16384 96735488 96768256 12 1784 9835 27 _ _ (459687 / 25000) (1838751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96768256 :
    ThetaLowerSegment 96768256 96801024 (4837770210869 / 50000) (2419706121151 / 25000) := by
  exact
    packedTile16384 96768256 96801024 12 1786 9837 27 _ _ (1838781 / 100000) (57462 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96801024 :
    ThetaLowerSegment 96801024 96833792 (2419706121151 / 25000) (9682183999609 / 100000) := by
  exact
    packedTile16384 96801024 96833792 12 1827 9838 27 _ _ (367763 / 20000) (919409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96833792 :
    ThetaLowerSegment 96833792 96866560 (9682183999609 / 100000) (9685383596869 / 100000) := by
  exact
    packedTile16384 96833792 96866560 12 1740 9840 27 _ _ (1838849 / 100000) (459713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96866560 :
    ThetaLowerSegment 96866560 96899328 (9685383596869 / 100000) (9688579575523 / 100000) := by
  exact
    packedTile16384 96866560 96899328 12 1738 9842 27 _ _ (1838883 / 100000) (919443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96899328 :
    ThetaLowerSegment 96899328 96932096 (9688579575523 / 100000) (302870688824 / 3125) := by
  exact
    packedTile16384 96899328 96932096 12 1785 9843 27 _ _ (1838917 / 100000) (45973 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96932096 :
    ThetaLowerSegment 96932096 96964864 (302870688824 / 3125) (9695188704727 / 100000) := by
  exact
    packedTile16384 96932096 96964864 12 1809 9845 27 _ _ (1838951 / 100000) (919477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96964864 :
    ThetaLowerSegment 96964864 96997632 (9695188704727 / 100000) (1939702349763 / 20000) := by
  exact
    packedTile16384 96964864 96997632 12 1807 9847 27 _ _ (229873 / 12500) (1838987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell96997632 :
    ThetaLowerSegment 96997632 97030400 (1939702349763 / 20000) (9701805430053 / 100000) := by
  exact
    packedTile16384 96997632 97030400 12 1791 9848 27 _ _ (919509 / 50000) (1839021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97030400 :
    ThetaLowerSegment 97030400 97063168 (9701805430053 / 100000) (9705115723653 / 100000) := by
  exact
    packedTile16384 97030400 97063168 12 1800 9850 27 _ _ (459763 / 25000) (367811 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97063168 :
    ThetaLowerSegment 97063168 97095936 (9705115723653 / 100000) (9708339641411 / 100000) := by
  exact
    packedTile16384 97063168 97095936 12 1753 9852 27 _ _ (919543 / 50000) (1839089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97095936 :
    ThetaLowerSegment 97095936 97128704 (9708339641411 / 100000) (9711616953251 / 100000) := by
  exact
    packedTile16384 97095936 97128704 12 1782 9853 27 _ _ (22989 / 1250) (1839123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97128704 :
    ThetaLowerSegment 97128704 97161472 (9711616953251 / 100000) (4857422333383 / 50000) := by
  exact
    packedTile16384 97128704 97161472 12 1755 9855 27 _ _ (1839153 / 100000) (459789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97161472 :
    ThetaLowerSegment 97161472 97194240 (4857422333383 / 50000) (9718061404829 / 100000) := by
  exact
    packedTile16384 97161472 97194240 12 1749 9857 27 _ _ (1839187 / 100000) (183919 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97194240 :
    ThetaLowerSegment 97194240 97227008 (9718061404829 / 100000) (2430307595653 / 25000) := by
  exact
    packedTile16384 97194240 97227008 12 1723 9858 27 _ _ (1839221 / 100000) (229903 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97227008 :
    ThetaLowerSegment 97227008 97259776 (2430307595653 / 25000) (4862297189089 / 50000) := by
  exact
    packedTile16384 97227008 97259776 12 1829 9860 27 _ _ (919627 / 50000) (1839257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97259776 :
    ThetaLowerSegment 97259776 97292544 (4862297189089 / 50000) (4863931396477 / 50000) := by
  exact
    packedTile16384 97259776 97292544 12 1777 9862 27 _ _ (229911 / 12500) (1839291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97292544 :
    ThetaLowerSegment 97292544 97325312 (4863931396477 / 50000) (4865573911023 / 50000) := by
  exact
    packedTile16384 97292544 97325312 12 1786 9863 27 _ _ (919661 / 50000) (73573 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97325312 :
    ThetaLowerSegment 97325312 97358080 (4865573911023 / 50000) (9734383247491 / 100000) := by
  exact
    packedTile16384 97325312 97358080 12 1759 9865 27 _ _ (367871 / 20000) (919679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97358080 :
    ThetaLowerSegment 97358080 97390848 (9734383247491 / 100000) (4868835117817 / 50000) := by
  exact
    packedTile16384 97358080 97390848 12 1787 9867 27 _ _ (1839389 / 100000) (57481 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97390848 :
    ThetaLowerSegment 97390848 97423616 (4868835117817 / 50000) (4870490598517 / 50000) := by
  exact
    packedTile16384 97390848 97423616 12 1800 9868 27 _ _ (1839423 / 100000) (919713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97423616 :
    ThetaLowerSegment 97423616 97456384 (4870490598517 / 50000) (4872120356533 / 50000) := by
  exact
    packedTile16384 97423616 97456384 12 1772 9870 27 _ _ (57483 / 3125) (1839459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97456384 :
    ThetaLowerSegment 97456384 97489152 (4872120356533 / 50000) (1218451102407 / 12500) := by
  exact
    packedTile16384 97456384 97489152 12 1831 9872 27 _ _ (183949 / 10000) (1839493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97489152 :
    ThetaLowerSegment 97489152 97521920 (1218451102407 / 12500) (2437734129543 / 25000) := by
  exact
    packedTile16384 97489152 97521920 12 1809 9873 27 _ _ (459881 / 25000) (1839527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97521920 :
    ThetaLowerSegment 97521920 97554688 (2437734129543 / 25000) (9754271635013 / 100000) := by
  exact
    packedTile16384 97521920 97554688 12 1813 9875 27 _ _ (1839557 / 100000) (45989 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97554688 :
    ThetaLowerSegment 97554688 97587456 (9754271635013 / 100000) (1951524673963 / 20000) := by
  exact
    packedTile16384 97554688 97587456 12 1822 9876 27 _ _ (1839591 / 100000) (919797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97587456 :
    ThetaLowerSegment 97587456 97620224 (1951524673963 / 20000) (9760883183543 / 100000) := by
  exact
    packedTile16384 97587456 97620224 12 1772 9878 27 _ _ (229953 / 12500) (1839627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97620224 :
    ThetaLowerSegment 97620224 97652992 (9760883183543 / 100000) (9764133859229 / 100000) := by
  exact
    packedTile16384 97620224 97652992 12 1767 9880 27 _ _ (919829 / 50000) (1839661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97652992 :
    ThetaLowerSegment 97652992 97685760 (9764133859229 / 100000) (9767401152221 / 100000) := by
  exact
    packedTile16384 97652992 97685760 12 1776 9881 27 _ _ (459923 / 25000) (367939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97685760 :
    ThetaLowerSegment 97685760 97718528 (9767401152221 / 100000) (9770646427121 / 100000) := by
  exact
    packedTile16384 97685760 97718528 12 1764 9883 27 _ _ (73589 / 4000) (114983 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97718528 :
    ThetaLowerSegment 97718528 97751296 (9770646427121 / 100000) (9773957993321 / 100000) := by
  exact
    packedTile16384 97718528 97751296 12 1800 9885 27 _ _ (1839759 / 100000) (919881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97751296 :
    ThetaLowerSegment 97751296 97784064 (9773957993321 / 100000) (9777247541417 / 100000) := by
  exact
    packedTile16384 97751296 97784064 12 1788 9886 27 _ _ (114987 / 6250) (367959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97784064 :
    ThetaLowerSegment 97784064 97816832 (9777247541417 / 100000) (9780557388391 / 100000) := by
  exact
    packedTile16384 97784064 97816832 12 1799 9888 27 _ _ (919913 / 50000) (1839829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97816832 :
    ThetaLowerSegment 97816832 97849600 (9780557388391 / 100000) (9783854415719 / 100000) := by
  exact
    packedTile16384 97816832 97849600 12 1792 9890 27 _ _ (1839859 / 100000) (919931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97849600 :
    ThetaLowerSegment 97849600 97882368 (9783854415719 / 100000) (9787055829539 / 100000) := by
  exact
    packedTile16384 97849600 97882368 12 1740 9891 27 _ _ (1839893 / 100000) (229987 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97882368 :
    ThetaLowerSegment 97882368 97915136 (9787055829539 / 100000) (9790402654933 / 100000) := by
  exact
    packedTile16384 97882368 97915136 12 1819 9893 27 _ _ (919963 / 50000) (1839929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97915136 :
    ThetaLowerSegment 97915136 97947904 (9790402654933 / 100000) (9793736662453 / 100000) := by
  exact
    packedTile16384 97915136 97947904 12 1812 9895 27 _ _ (45999 / 2500) (1839963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97947904 :
    ThetaLowerSegment 97947904 97980672 (9793736662453 / 100000) (1224624411257 / 12500) := by
  exact
    packedTile16384 97947904 97980672 12 1771 9896 27 _ _ (1839993 / 100000) (459999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell97980672 :
    ThetaLowerSegment 97980672 98013440 (1224624411257 / 12500) (9800187736901 / 100000) := by
  exact
    packedTile16384 97980672 98013440 12 1735 9898 27 _ _ (1840027 / 100000) (184003 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98013440 :
    ThetaLowerSegment 98013440 98046208 (9800187736901 / 100000) (9803396801541 / 100000) := by
  exact
    packedTile16384 98013440 98046208 12 1744 9900 27 _ _ (92003 / 5000) (1840063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98046208 :
    ThetaLowerSegment 98046208 98078976 (9803396801541 / 100000) (61291735546 / 625) := by
  exact
    packedTile16384 98046208 98078976 12 1783 9901 27 _ _ (1840093 / 100000) (57503 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98078976 :
    ThetaLowerSegment 98078976 98111744 (61291735546 / 625) (9809929191769 / 100000) := by
  exact
    packedTile16384 98078976 98111744 12 1767 9903 27 _ _ (1840127 / 100000) (184013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98111744 :
    ThetaLowerSegment 98111744 98144512 (9809929191769 / 100000) (9813180754489 / 100000) := by
  exact
    packedTile16384 98111744 98144512 12 1767 9905 27 _ _ (11501 / 625) (1840163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98144512 :
    ThetaLowerSegment 98144512 98177280 (9813180754489 / 100000) (9816428696899 / 100000) := by
  exact
    packedTile16384 98144512 98177280 12 1765 9906 27 _ _ (920097 / 50000) (1840197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98177280 :
    ThetaLowerSegment 98177280 98210048 (9816428696899 / 100000) (9819689579143 / 100000) := by
  exact
    packedTile16384 98177280 98210048 12 1772 9908 27 _ _ (1840227 / 100000) (184023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98210048 :
    ThetaLowerSegment 98210048 98242816 (9819689579143 / 100000) (9822976283503 / 100000) := by
  exact
    packedTile16384 98210048 98242816 12 1786 9910 27 _ _ (92013 / 5000) (1840263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98242816 :
    ThetaLowerSegment 98242816 98275584 (9822976283503 / 100000) (9826296173879 / 100000) := by
  exact
    packedTile16384 98242816 98275584 12 1804 9911 27 _ _ (920147 / 50000) (1840297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98275584 :
    ThetaLowerSegment 98275584 98308352 (9826296173879 / 100000) (4914794259441 / 50000) := by
  exact
    packedTile16384 98275584 98308352 12 1789 9913 27 _ _ (1840327 / 100000) (184033 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98308352 :
    ThetaLowerSegment 98308352 98341120 (4914794259441 / 50000) (4916417456961 / 50000) := by
  exact
    packedTile16384 98308352 98341120 12 1764 9915 27 _ _ (46009 / 2500) (1840363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98341120 :
    ThetaLowerSegment 98341120 98373888 (4916417456961 / 50000) (4918086694319 / 50000) := by
  exact
    packedTile16384 98341120 98373888 12 1814 9916 27 _ _ (920197 / 50000) (1840397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98373888 :
    ThetaLowerSegment 98373888 98406656 (4918086694319 / 50000) (1967879195263 / 20000) := by
  exact
    packedTile16384 98373888 98406656 12 1751 9918 27 _ _ (1840427 / 100000) (184043 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98406656 :
    ThetaLowerSegment 98406656 98439424 (1967879195263 / 20000) (393707689607 / 4000) := by
  exact
    packedTile16384 98406656 98439424 12 1791 9920 27 _ _ (92023 / 5000) (1840463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98439424 :
    ThetaLowerSegment 98439424 98472192 (393707689607 / 4000) (9846029055797 / 100000) := by
  exact
    packedTile16384 98439424 98472192 12 1813 9921 27 _ _ (920247 / 50000) (1840497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98472192 :
    ThetaLowerSegment 98472192 98504960 (9846029055797 / 100000) (4924625909287 / 50000) := by
  exact
    packedTile16384 98472192 98504960 12 1751 9923 27 _ _ (1840527 / 100000) (184053 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98504960 :
    ThetaLowerSegment 98504960 98537728 (4924625909287 / 50000) (4926310021687 / 50000) := by
  exact
    packedTile16384 98504960 98537728 12 1830 9924 27 _ _ (23007 / 1250) (1840563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98537728 :
    ThetaLowerSegment 98537728 98570496 (4926310021687 / 50000) (307997507138 / 3125) := by
  exact
    packedTile16384 98537728 98570496 12 1793 9926 27 _ _ (920297 / 50000) (1840597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98570496 :
    ThetaLowerSegment 98570496 98603264 (307997507138 / 3125) (2464799136119 / 25000) := by
  exact
    packedTile16384 98570496 98603264 12 1780 9928 27 _ _ (1840627 / 100000) (184063 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98603264 :
    ThetaLowerSegment 98603264 98636032 (2464799136119 / 25000) (308201876083 / 3125) := by
  exact
    packedTile16384 98603264 98636032 12 1773 9929 27 _ _ (92033 / 5000) (1840663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98636032 :
    ThetaLowerSegment 98636032 98668800 (308201876083 / 3125) (9865749353047 / 100000) := by
  exact
    packedTile16384 98636032 98668800 12 1787 9931 27 _ _ (1840693 / 100000) (230087 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98668800 :
    ThetaLowerSegment 98668800 98701568 (9865749353047 / 100000) (9868970623547 / 100000) := by
  exact
    packedTile16384 98668800 98701568 12 1750 9933 27 _ _ (920363 / 50000) (1840729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98701568 :
    ThetaLowerSegment 98701568 98734336 (9868970623547 / 100000) (9872223246467 / 100000) := by
  exact
    packedTile16384 98701568 98734336 12 1767 9934 27 _ _ (46019 / 2500) (1840763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98734336 :
    ThetaLowerSegment 98734336 98767104 (9872223246467 / 100000) (1975087454209 / 20000) := by
  exact
    packedTile16384 98734336 98767104 12 1746 9936 27 _ _ (1840793 / 100000) (460199 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98767104 :
    ThetaLowerSegment 98767104 98799872 (1975087454209 / 20000) (9878655034893 / 100000) := by
  exact
    packedTile16384 98767104 98799872 12 1748 9938 27 _ _ (920413 / 50000) (1840829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98799872 :
    ThetaLowerSegment 98799872 98832640 (9878655034893 / 100000) (9881939127349 / 100000) := by
  exact
    packedTile16384 98799872 98832640 12 1784 9939 27 _ _ (1840859 / 100000) (920431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98832640 :
    ThetaLowerSegment 98832640 98865408 (9881939127349 / 100000) (1977047969341 / 20000) := by
  exact
    packedTile16384 98832640 98865408 12 1793 9941 27 _ _ (460223 / 25000) (368179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98865408 :
    ThetaLowerSegment 98865408 98898176 (1977047969341 / 20000) (1977695238571 / 20000) := by
  exact
    packedTile16384 98865408 98898176 12 1758 9943 27 _ _ (73637 / 4000) (57529 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98898176 :
    ThetaLowerSegment 98898176 98930944 (1977695238571 / 20000) (1978335892303 / 20000) := by
  exact
    packedTile16384 98898176 98930944 12 1740 9944 27 _ _ (1840959 / 100000) (920481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98930944 :
    ThetaLowerSegment 98930944 98963712 (1978335892303 / 20000) (9894868059659 / 100000) := by
  exact
    packedTile16384 98930944 98963712 12 1732 9946 27 _ _ (57531 / 3125) (368199 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98963712 :
    ThetaLowerSegment 98963712 98996480 (9894868059659 / 100000) (1237266524623 / 12500) := by
  exact
    packedTile16384 98963712 98996480 12 1773 9948 27 _ _ (73641 / 4000) (460257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell98996480 :
    ThetaLowerSegment 98996480 99029248 (1237266524623 / 12500) (990151422053 / 10000) := by
  exact
    packedTile16384 98996480 99029248 12 1837 9949 27 _ _ (920529 / 50000) (1841061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99029248 :
    ThetaLowerSegment 99029248 99062016 (990151422053 / 10000) (9904841071967 / 100000) := by
  exact
    packedTile16384 99029248 99062016 12 1807 9951 27 _ _ (1841091 / 100000) (920547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99062016 :
    ThetaLowerSegment 99062016 99094784 (9904841071967 / 100000) (1981626232111 / 20000) := by
  exact
    packedTile16384 99062016 99094784 12 1787 9952 27 _ _ (460281 / 25000) (1841127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99094784 :
    ThetaLowerSegment 99094784 99127552 (1981626232111 / 20000) (9911323726793 / 100000) := by
  exact
    packedTile16384 99094784 99127552 12 1734 9954 27 _ _ (1841157 / 100000) (46029 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99127552 :
    ThetaLowerSegment 99127552 99160320 (9911323726793 / 100000) (9914652598313 / 100000) := by
  exact
    packedTile16384 99127552 99160320 12 1808 9956 27 _ _ (184119 / 10000) (1841193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99160320 :
    ThetaLowerSegment 99160320 99193088 (9914652598313 / 100000) (4958941972339 / 50000) := by
  exact
    packedTile16384 99160320 99193088 12 1755 9957 27 _ _ (1841223 / 100000) (920613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99193088 :
    ThetaLowerSegment 99193088 99225856 (4958941972339 / 50000) (992109141263 / 10000) := by
  exact
    packedTile16384 99193088 99225856 12 1742 9959 27 _ _ (230157 / 12500) (1841259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99225856 :
    ThetaLowerSegment 99225856 99258624 (992109141263 / 10000) (2481093147407 / 25000) := by
  exact
    packedTile16384 99225856 99258624 12 1782 9961 27 _ _ (1841289 / 100000) (460323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99258624 :
    ThetaLowerSegment 99258624 99291392 (2481093147407 / 25000) (4963785482971 / 50000) := by
  exact
    packedTile16384 99258624 99291392 12 1737 9962 27 _ _ (920661 / 50000) (73653 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99291392 :
    ThetaLowerSegment 99291392 99324160 (4963785482971 / 50000) (2482703858363 / 25000) := by
  exact
    packedTile16384 99291392 99324160 12 1762 9964 27 _ _ (368271 / 20000) (920679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99324160 :
    ThetaLowerSegment 99324160 99356928 (2482703858363 / 25000) (2483542610597 / 25000) := by
  exact
    packedTile16384 99324160 99356928 12 1822 9966 27 _ _ (460347 / 25000) (1841391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99356928 :
    ThetaLowerSegment 99356928 99389696 (2483542610597 / 25000) (9937468427399 / 100000) := by
  exact
    packedTile16384 99356928 99389696 12 1791 9967 27 _ _ (1841421 / 100000) (115089 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99389696 :
    ThetaLowerSegment 99389696 99422464 (9937468427399 / 100000) (9940687288991 / 100000) := by
  exact
    packedTile16384 99389696 99422464 12 1748 9969 27 _ _ (920727 / 50000) (1841457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99422464 :
    ThetaLowerSegment 99422464 99455232 (9940687288991 / 100000) (1242988966591 / 12500) := by
  exact
    packedTile16384 99422464 99455232 12 1751 9971 27 _ _ (1841487 / 100000) (184149 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99455232 :
    ThetaLowerSegment 99455232 99488000 (1242988966591 / 12500) (1243411365241 / 12500) := by
  exact
    packedTile16384 99455232 99488000 12 1835 9972 27 _ _ (23019 / 1250) (1841523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99488000 :
    ThetaLowerSegment 99488000 99520768 (1243411365241 / 12500) (9950519164337 / 100000) := by
  exact
    packedTile16384 99488000 99520768 12 1753 9974 27 _ _ (1841553 / 100000) (460389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99520768 :
    ThetaLowerSegment 99520768 99553536 (9950519164337 / 100000) (9953769563627 / 100000) := by
  exact
    packedTile16384 99520768 99553536 12 1765 9976 27 _ _ (920793 / 50000) (1841589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99553536 :
    ThetaLowerSegment 99553536 99586304 (9953769563627 / 100000) (9957084477827 / 100000) := by
  exact
    packedTile16384 99553536 99586304 12 1800 9977 27 _ _ (1841619 / 100000) (920811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99586304 :
    ThetaLowerSegment 99586304 99619072 (9957084477827 / 100000) (9960541258631 / 100000) := by
  exact
    packedTile16384 99586304 99619072 12 1877 9979 27 _ _ (460413 / 25000) (368331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99619072 :
    ThetaLowerSegment 99619072 99651840 (9960541258631 / 100000) (4981908808123 / 50000) := by
  exact
    packedTile16384 99619072 99651840 12 1779 9980 27 _ _ (368337 / 20000) (230211 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99651840 :
    ThetaLowerSegment 99651840 99684608 (4981908808123 / 50000) (4983514786219 / 50000) := by
  exact
    packedTile16384 99651840 99684608 12 1744 9982 27 _ _ (920859 / 50000) (1841721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99684608 :
    ThetaLowerSegment 99684608 99717376 (4983514786219 / 50000) (1246287104839 / 12500) := by
  exact
    packedTile16384 99684608 99717376 12 1774 9984 27 _ _ (1841751 / 100000) (920877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99717376 :
    ThetaLowerSegment 99717376 99750144 (1246287104839 / 12500) (623345342879 / 6250) := by
  exact
    packedTile16384 99717376 99750144 12 1753 9985 27 _ _ (230223 / 12500) (1841787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99750144 :
    ThetaLowerSegment 99750144 99782912 (623345342879 / 6250) (1247103482769 / 12500) := by
  exact
    packedTile16384 99750144 99782912 12 1793 9987 27 _ _ (230227 / 12500) (1841819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99782912 :
    ThetaLowerSegment 99782912 99815680 (1247103482769 / 12500) (9980078725637 / 100000) := by
  exact
    packedTile16384 99782912 99815680 12 1765 9989 27 _ _ (1841849 / 100000) (460463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99815680 :
    ThetaLowerSegment 99815680 99848448 (9980078725637 / 100000) (399332743843 / 4000) := by
  exact
    packedTile16384 99815680 99848448 12 1759 9990 27 _ _ (920941 / 50000) (368377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99848448 :
    ThetaLowerSegment 99848448 99881216 (399332743843 / 4000) (1997327545381 / 20000) := by
  exact
    packedTile16384 99848448 99881216 12 1802 9992 27 _ _ (368383 / 20000) (920959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99881216 :
    ThetaLowerSegment 99881216 99913984 (1997327545381 / 20000) (9989923762137 / 100000) := by
  exact
    packedTile16384 99881216 99913984 12 1784 9994 27 _ _ (460487 / 25000) (1841951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99913984 :
    ThetaLowerSegment 99913984 99946752 (9989923762137 / 100000) (2498298319603 / 25000) := by
  exact
    packedTile16384 99913984 99946752 12 1775 9995 27 _ _ (1841981 / 100000) (57562 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99946752 :
    ThetaLowerSegment 99946752 99979520 (2498298319603 / 25000) (4998263660971 / 50000) := by
  exact
    packedTile16384 99946752 99979520 12 1810 9997 27 _ _ (1842013 / 100000) (57563 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell99979520 :
    ThetaLowerSegment 99979520 100012288 (4998263660971 / 50000) (2499955685559 / 25000) := by
  exact
    packedTile16384 99979520 100012288 12 1789 9998 27 _ _ (921023 / 50000) (1842049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100012288 :
    ThetaLowerSegment 100012288 100045056 (2499955685559 / 25000) (10003070327513 / 100000) := by
  exact
    packedTile16384 100012288 100045056 12 1763 10000 27 _ _ (1842079 / 100000) (921041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100045056 :
    ThetaLowerSegment 100045056 100077824 (10003070327513 / 100000) (10006345602649 / 100000) := by
  exact
    packedTile16384 100045056 100077824 12 1778 10002 27 _ _ (57566 / 3125) (368423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100077824 :
    ThetaLowerSegment 100077824 100110592 (10006345602649 / 100000) (2001920871077 / 20000) := by
  exact
    packedTile16384 100077824 100110592 12 1769 10003 27 _ _ (57567 / 3125) (1842147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100110592 :
    ThetaLowerSegment 100110592 100143360 (2001920871077 / 20000) (5006475795497 / 50000) := by
  exact
    packedTile16384 100110592 100143360 12 1817 10005 27 _ _ (1842177 / 100000) (92109 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100143360 :
    ThetaLowerSegment 100143360 100176128 (5006475795497 / 50000) (5008109835767 / 50000) := by
  exact
    packedTile16384 100143360 100176128 12 1774 10007 27 _ _ (184221 / 10000) (1842213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100176128 :
    ThetaLowerSegment 100176128 100208896 (5008109835767 / 50000) (2504881163869 / 25000) := by
  exact
    packedTile16384 100176128 100208896 12 1794 10008 27 _ _ (1842243 / 100000) (921123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100208896 :
    ThetaLowerSegment 100208896 100241664 (2504881163869 / 25000) (10022813116351 / 100000) := by
  exact
    packedTile16384 100208896 100241664 12 1785 10010 27 _ _ (73691 / 4000) (921139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100241664 :
    ThetaLowerSegment 100241664 100274432 (10022813116351 / 100000) (10026103478439 / 100000) := by
  exact
    packedTile16384 100241664 100274432 12 1786 10012 27 _ _ (460577 / 25000) (1842311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100274432 :
    ThetaLowerSegment 100274432 100307200 (10026103478439 / 100000) (5014686816857 / 50000) := by
  exact
    packedTile16384 100274432 100307200 12 1775 10013 27 _ _ (1842341 / 100000) (230293 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100307200 :
    ThetaLowerSegment 100307200 100339968 (5014686816857 / 50000) (627039204027 / 6250) := by
  exact
    packedTile16384 100307200 100339968 12 1766 10015 27 _ _ (1842373 / 100000) (230297 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100339968 :
    ThetaLowerSegment 100339968 100372736 (627039204027 / 6250) (501793310709 / 5000) := by
  exact
    packedTile16384 100339968 100372736 12 1758 10016 27 _ _ (921203 / 50000) (1842409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100372736 :
    ThetaLowerSegment 100372736 100405504 (501793310709 / 5000) (5019552610971 / 50000) := by
  exact
    packedTile16384 100372736 100405504 12 1758 10018 27 _ _ (1842439 / 100000) (921221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100405504 :
    ThetaLowerSegment 100405504 100438272 (5019552610971 / 50000) (10042331388663 / 100000) := by
  exact
    packedTile16384 100405504 100438272 12 1751 10020 27 _ _ (1842471 / 100000) (921237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100438272 :
    ThetaLowerSegment 100438272 100471040 (10042331388663 / 100000) (10045601833263 / 100000) := by
  exact
    packedTile16384 100438272 100471040 12 1775 10021 27 _ _ (230313 / 12500) (1842507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100471040 :
    ThetaLowerSegment 100471040 100503808 (10045601833263 / 100000) (10048888919271 / 100000) := by
  exact
    packedTile16384 100471040 100503808 12 1784 10023 27 _ _ (1842537 / 100000) (92127 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100503808 :
    ThetaLowerSegment 100503808 100536576 (10048888919271 / 100000) (251305184651 / 2500) := by
  exact
    packedTile16384 100503808 100536576 12 1801 10025 27 _ _ (1842569 / 100000) (460643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100536576 :
    ThetaLowerSegment 100536576 100569344 (251305184651 / 2500) (314233054249 / 3125) := by
  exact
    packedTile16384 100536576 100569344 12 1764 10026 27 _ _ (921301 / 50000) (368521 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100569344 :
    ThetaLowerSegment 100569344 100602112 (314233054249 / 3125) (5029349464587 / 50000) := by
  exact
    packedTile16384 100569344 100602112 12 1759 10028 27 _ _ (921317 / 50000) (1842637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100602112 :
    ThetaLowerSegment 100602112 100634880 (5029349464587 / 50000) (2515482741773 / 25000) := by
  exact
    packedTile16384 100602112 100634880 12 1754 10030 27 _ _ (1842667 / 100000) (184267 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100634880 :
    ThetaLowerSegment 100634880 100667648 (2515482741773 / 25000) (10065253353389 / 100000) := by
  exact
    packedTile16384 100634880 100667648 12 1803 10031 27 _ _ (1842699 / 100000) (921351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100667648 :
    ThetaLowerSegment 100667648 100700416 (10065253353389 / 100000) (10068505775369 / 100000) := by
  exact
    packedTile16384 100667648 100700416 12 1765 10033 27 _ _ (460683 / 25000) (368547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100700416 :
    ThetaLowerSegment 100700416 100733184 (10068505775369 / 100000) (10071726928589 / 100000) := by
  exact
    packedTile16384 100700416 100733184 12 1748 10034 27 _ _ (368553 / 20000) (115173 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100733184 :
    ThetaLowerSegment 100733184 100765952 (10071726928589 / 100000) (5037511846211 / 50000) := by
  exact
    packedTile16384 100733184 100765952 12 1789 10036 27 _ _ (1842797 / 100000) (4607 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100765952 :
    ThetaLowerSegment 100765952 100798720 (5037511846211 / 50000) (5039111422651 / 50000) := by
  exact
    packedTile16384 100765952 100798720 12 1736 10038 27 _ _ (184283 / 10000) (1842833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100798720 :
    ThetaLowerSegment 100798720 100831488 (5039111422651 / 50000) (2520365188459 / 25000) := by
  exact
    packedTile16384 100798720 100831488 12 1757 10039 27 _ _ (921431 / 50000) (368573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100831488 :
    ThetaLowerSegment 100831488 100864256 (2520365188459 / 25000) (10084742949831 / 100000) := by
  exact
    packedTile16384 100831488 100864256 12 1781 10041 27 _ _ (368579 / 20000) (921449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100864256 :
    ThetaLowerSegment 100864256 100897024 (10084742949831 / 100000) (2017609095003 / 20000) := by
  exact
    packedTile16384 100864256 100897024 12 1792 10043 27 _ _ (1842927 / 100000) (184293 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100897024 :
    ThetaLowerSegment 100897024 100929792 (2017609095003 / 20000) (2018278826667 / 20000) := by
  exact
    packedTile16384 100897024 100929792 12 1817 10044 27 _ _ (23037 / 1250) (1842963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100929792 :
    ThetaLowerSegment 100929792 100962560 (2018278826667 / 20000) (10094676502087 / 100000) := by
  exact
    packedTile16384 100929792 100962560 12 1781 10046 27 _ _ (115187 / 6250) (368599 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100962560 :
    ThetaLowerSegment 100962560 100995328 (10094676502087 / 100000) (5048970249681 / 50000) := by
  exact
    packedTile16384 100962560 100995328 12 1771 10048 27 _ _ (73721 / 4000) (460757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell100995328 :
    ThetaLowerSegment 100995328 101028096 (5048970249681 / 50000) (10101278275589 / 100000) := by
  exact
    packedTile16384 100995328 101028096 12 1811 10049 27 _ _ (1843057 / 100000) (92153 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101028096 :
    ThetaLowerSegment 101028096 101060864 (10101278275589 / 100000) (10104595835789 / 100000) := by
  exact
    packedTile16384 101028096 101060864 12 1800 10051 27 _ _ (1843089 / 100000) (460773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101060864 :
    ThetaLowerSegment 101060864 101093632 (10104595835789 / 100000) (10107869220461 / 100000) := by
  exact
    packedTile16384 101060864 101093632 12 1776 10052 27 _ _ (921561 / 50000) (2949 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101093632 :
    ThetaLowerSegment 101093632 101126400 (10107869220461 / 100000) (10111155564043 / 100000) := by
  exact
    packedTile16384 101093632 101126400 12 1783 10054 27 _ _ (921577 / 50000) (1843157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101126400 :
    ThetaLowerSegment 101126400 101159168 (10111155564043 / 100000) (10114473300643 / 100000) := by
  exact
    packedTile16384 101126400 101159168 12 1800 10056 27 _ _ (1843187 / 100000) (184319 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101159168 :
    ThetaLowerSegment 101159168 101191936 (10114473300643 / 100000) (5058841172461 / 50000) := by
  exact
    packedTile16384 101159168 101191936 12 1741 10057 27 _ _ (1843219 / 100000) (921611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101191936 :
    ThetaLowerSegment 101191936 101224704 (5058841172461 / 50000) (2024197458793 / 20000) := by
  exact
    packedTile16384 101191936 101224704 12 1793 10059 27 _ _ (1843251 / 100000) (921627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101224704 :
    ThetaLowerSegment 101224704 101257472 (2024197458793 / 20000) (10124321794721 / 100000) := by
  exact
    packedTile16384 101224704 101257472 12 1809 10061 27 _ _ (460821 / 25000) (1843287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101257472 :
    ThetaLowerSegment 101257472 101290240 (10124321794721 / 100000) (10127569717513 / 100000) := by
  exact
    packedTile16384 101257472 101290240 12 1762 10062 27 _ _ (460829 / 25000) (1843319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101290240 :
    ThetaLowerSegment 101290240 101323008 (10127569717513 / 100000) (633177143037 / 6250) := by
  exact
    packedTile16384 101290240 101323008 12 1771 10064 27 _ _ (1843349 / 100000) (230419 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101323008 :
    ThetaLowerSegment 101323008 101355776 (633177143037 / 6250) (5067085404101 / 50000) := by
  exact
    packedTile16384 101323008 101355776 12 1810 10065 27 _ _ (1843381 / 100000) (230423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101355776 :
    ThetaLowerSegment 101355776 101388544 (5067085404101 / 50000) (10137424432147 / 100000) := by
  exact
    packedTile16384 101355776 101388544 12 1765 10067 27 _ _ (1843413 / 100000) (230427 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101388544 :
    ThetaLowerSegment 101388544 101421312 (10137424432147 / 100000) (2028134885489 / 20000) := by
  exact
    packedTile16384 101388544 101421312 12 1763 10069 27 _ _ (921723 / 50000) (1843449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101421312 :
    ThetaLowerSegment 101421312 101454080 (2028134885489 / 20000) (10143931853071 / 100000) := by
  exact
    packedTile16384 101421312 101454080 12 1767 10070 27 _ _ (921739 / 50000) (1843481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101454080 :
    ThetaLowerSegment 101454080 101486848 (10143931853071 / 100000) (10147272293191 / 100000) := by
  exact
    packedTile16384 101454080 101486848 12 1812 10072 27 _ _ (184351 / 10000) (1843513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101486848 :
    ThetaLowerSegment 101486848 101519616 (10147272293191 / 100000) (406021930693 / 4000) := by
  exact
    packedTile16384 101486848 101519616 12 1777 10074 27 _ _ (921771 / 50000) (368709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101519616 :
    ThetaLowerSegment 101519616 101552384 (406021930693 / 4000) (406153930663 / 4000) := by
  exact
    packedTile16384 101519616 101552384 12 1790 10075 27 _ _ (73743 / 4000) (921789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101552384 :
    ThetaLowerSegment 101552384 101585152 (406153930663 / 4000) (10157052455541 / 100000) := by
  exact
    packedTile16384 101552384 101585152 12 1738 10077 27 _ _ (1843607 / 100000) (184361 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101585152 :
    ThetaLowerSegment 101585152 101617920 (10157052455541 / 100000) (10160319383849 / 100000) := by
  exact
    packedTile16384 101585152 101617920 12 1772 10078 27 _ _ (1843639 / 100000) (921821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101617920 :
    ThetaLowerSegment 101617920 101650688 (10160319383849 / 100000) (406544266041 / 4000) := by
  exact
    packedTile16384 101617920 101650688 12 1783 10080 27 _ _ (230459 / 12500) (73747 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101650688 :
    ThetaLowerSegment 101650688 101683456 (406544266041 / 4000) (10166838664137 / 100000) := by
  exact
    packedTile16384 101650688 101683456 12 1753 10082 27 _ _ (230463 / 12500) (1843707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101683456 :
    ThetaLowerSegment 101683456 101716224 (10166838664137 / 100000) (10170100233121 / 100000) := by
  exact
    packedTile16384 101683456 101716224 12 1769 10083 27 _ _ (230467 / 12500) (1843739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101716224 :
    ThetaLowerSegment 101716224 101748992 (10170100233121 / 100000) (10173374765089 / 100000) := by
  exact
    packedTile16384 101716224 101748992 12 1776 10085 27 _ _ (230471 / 12500) (1843771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101748992 :
    ThetaLowerSegment 101748992 101781760 (10173374765089 / 100000) (10176612477889 / 100000) := by
  exact
    packedTile16384 101748992 101781760 12 1756 10087 27 _ _ (9219 / 500) (1843803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101781760 :
    ThetaLowerSegment 101781760 101814528 (10176612477889 / 100000) (2544984227197 / 25000) := by
  exact
    packedTile16384 101781760 101814528 12 1803 10088 27 _ _ (1843833 / 100000) (460959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101814528 :
    ThetaLowerSegment 101814528 101847296 (2544984227197 / 25000) (10183154453213 / 100000) := by
  exact
    packedTile16384 101814528 101847296 12 1745 10090 27 _ _ (368773 / 20000) (460967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101847296 :
    ThetaLowerSegment 101847296 101880064 (10183154453213 / 100000) (509322843637 / 5000) := by
  exact
    packedTile16384 101847296 101880064 12 1791 10091 27 _ _ (1843897 / 100000) (18439 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101880064 :
    ThetaLowerSegment 101880064 101912832 (509322843637 / 5000) (10189781476727 / 100000) := by
  exact
    packedTile16384 101880064 101912832 12 1803 10093 27 _ _ (1843929 / 100000) (460983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101912832 :
    ThetaLowerSegment 101912832 101945600 (10189781476727 / 100000) (10193111670293 / 100000) := by
  exact
    packedTile16384 101912832 101945600 12 1806 10095 27 _ _ (1843961 / 100000) (460991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101945600 :
    ThetaLowerSegment 101945600 101978368 (10193111670293 / 100000) (10196430857693 / 100000) := by
  exact
    packedTile16384 101945600 101978368 12 1800 10096 27 _ _ (1843993 / 100000) (460999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell101978368 :
    ThetaLowerSegment 101978368 102011136 (10196430857693 / 100000) (10199668967349 / 100000) := by
  exact
    packedTile16384 101978368 102011136 12 1756 10098 27 _ _ (922013 / 50000) (1844029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102011136 :
    ThetaLowerSegment 102011136 102043904 (10199668967349 / 100000) (10203004868271 / 100000) := by
  exact
    packedTile16384 102011136 102043904 12 1809 10100 27 _ _ (922029 / 50000) (1844061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102043904 :
    ThetaLowerSegment 102043904 102076672 (10203004868271 / 100000) (10206283660291 / 100000) := by
  exact
    packedTile16384 102043904 102076672 12 1778 10101 27 _ _ (184409 / 10000) (1844093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102076672 :
    ThetaLowerSegment 102076672 102109440 (10206283660291 / 100000) (10209568041573 / 100000) := by
  exact
    packedTile16384 102076672 102109440 12 1781 10103 27 _ _ (922061 / 50000) (14753 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102109440 :
    ThetaLowerSegment 102109440 102142208 (10209568041573 / 100000) (10212760272147 / 100000) := by
  exact
    packedTile16384 102109440 102142208 12 1731 10104 27 _ _ (922077 / 50000) (1844157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102142208 :
    ThetaLowerSegment 102142208 102174976 (10212760272147 / 100000) (10216155418573 / 100000) := by
  exact
    packedTile16384 102142208 102174976 12 1841 10106 27 _ _ (922093 / 50000) (1844189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102174976 :
    ThetaLowerSegment 102174976 102207744 (10216155418573 / 100000) (10219471322537 / 100000) := by
  exact
    packedTile16384 102174976 102207744 12 1798 10108 27 _ _ (922109 / 50000) (1844221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102207744 :
    ThetaLowerSegment 102207744 102240512 (10219471322537 / 100000) (10222656342287 / 100000) := by
  exact
    packedTile16384 102207744 102240512 12 1727 10109 27 _ _ (7377 / 400) (1844253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102240512 :
    ThetaLowerSegment 102240512 102273280 (10222656342287 / 100000) (10226016624091 / 100000) := by
  exact
    packedTile16384 102240512 102273280 12 1822 10111 27 _ _ (922141 / 50000) (368857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102273280 :
    ThetaLowerSegment 102273280 102306048 (10226016624091 / 100000) (10229352988117 / 100000) := by
  exact
    packedTile16384 102273280 102306048 12 1809 10113 27 _ _ (922157 / 50000) (1844317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102306048 :
    ThetaLowerSegment 102306048 102338816 (10229352988117 / 100000) (10232676499609 / 100000) := by
  exact
    packedTile16384 102306048 102338816 12 1802 10114 27 _ _ (922173 / 50000) (1844349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102338816 :
    ThetaLowerSegment 102338816 102371584 (10232676499609 / 100000) (10235970558717 / 100000) := by
  exact
    packedTile16384 102338816 102371584 12 1786 10116 27 _ _ (922189 / 50000) (1844381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102371584 :
    ThetaLowerSegment 102371584 102404352 (10235970558717 / 100000) (10239237008827 / 100000) := by
  exact
    packedTile16384 102371584 102404352 12 1771 10117 27 _ _ (184441 / 10000) (1844413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102404352 :
    ThetaLowerSegment 102404352 102437120 (10239237008827 / 100000) (10242505360051 / 100000) := by
  exact
    packedTile16384 102404352 102437120 12 1772 10119 27 _ _ (922221 / 50000) (368889 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102437120 :
    ThetaLowerSegment 102437120 102469888 (10242505360051 / 100000) (10245768234557 / 100000) := by
  exact
    packedTile16384 102437120 102469888 12 1769 10121 27 _ _ (922237 / 50000) (1844477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102469888 :
    ThetaLowerSegment 102469888 102502656 (10245768234557 / 100000) (10249086500851 / 100000) := by
  exact
    packedTile16384 102469888 102502656 12 1799 10122 27 _ _ (922253 / 50000) (1844509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102502656 :
    ThetaLowerSegment 102502656 102535424 (10249086500851 / 100000) (2050473217883 / 20000) := by
  exact
    packedTile16384 102502656 102535424 12 1778 10124 27 _ _ (922269 / 50000) (1844541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102535424 :
    ThetaLowerSegment 102535424 102568192 (2050473217883 / 20000) (2051128409147 / 20000) := by
  exact
    packedTile16384 102535424 102568192 12 1776 10125 27 _ _ (184457 / 10000) (1844573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102568192 :
    ThetaLowerSegment 102568192 102600960 (2051128409147 / 20000) (10258923592693 / 100000) := by
  exact
    packedTile16384 102568192 102600960 12 1779 10127 27 _ _ (922301 / 50000) (368921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102600960 :
    ThetaLowerSegment 102600960 102633728 (10258923592693 / 100000) (10262205196579 / 100000) := by
  exact
    packedTile16384 102600960 102633728 12 1779 10129 27 _ _ (922317 / 50000) (1844637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102633728 :
    ThetaLowerSegment 102633728 102666496 (10262205196579 / 100000) (10265461032069 / 100000) := by
  exact
    packedTile16384 102633728 102666496 12 1765 10130 27 _ _ (922333 / 50000) (1844669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102666496 :
    ThetaLowerSegment 102666496 102699264 (10265461032069 / 100000) (10268731681623 / 100000) := by
  exact
    packedTile16384 102666496 102699264 12 1773 10132 27 _ _ (922349 / 50000) (1844701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102699264 :
    ThetaLowerSegment 102699264 102732032 (10268731681623 / 100000) (10272015301023 / 100000) := by
  exact
    packedTile16384 102699264 102732032 12 1780 10134 27 _ _ (184473 / 10000) (1844733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102732032 :
    ThetaLowerSegment 102732032 102764800 (10272015301023 / 100000) (10275297132621 / 100000) := by
  exact
    packedTile16384 102732032 102764800 12 1779 10135 27 _ _ (922381 / 50000) (368953 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102764800 :
    ThetaLowerSegment 102764800 102797568 (10275297132621 / 100000) (10278523677327 / 100000) := by
  exact
    packedTile16384 102764800 102797568 12 1749 10137 27 _ _ (922397 / 50000) (1844797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102797568 :
    ThetaLowerSegment 102797568 102830336 (10278523677327 / 100000) (10281814846911 / 100000) := by
  exact
    packedTile16384 102797568 102830336 12 1784 10138 27 _ _ (922413 / 50000) (1844829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102830336 :
    ThetaLowerSegment 102830336 102863104 (10281814846911 / 100000) (10285096849293 / 100000) := by
  exact
    packedTile16384 102830336 102863104 12 1779 10140 27 _ _ (922429 / 50000) (1844861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102863104 :
    ThetaLowerSegment 102863104 102895872 (10285096849293 / 100000) (10288391821047 / 100000) := by
  exact
    packedTile16384 102863104 102895872 12 1786 10142 27 _ _ (1844889 / 100000) (461223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102895872 :
    ThetaLowerSegment 102895872 102928640 (10288391821047 / 100000) (10291657331217 / 100000) := by
  exact
    packedTile16384 102895872 102928640 12 1770 10143 27 _ _ (1844921 / 100000) (461231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102928640 :
    ThetaLowerSegment 102928640 102961408 (10291657331217 / 100000) (5147456836631 / 50000) := by
  exact
    packedTile16384 102928640 102961408 12 1765 10145 27 _ _ (1844953 / 100000) (461239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102961408 :
    ThetaLowerSegment 102961408 102994176 (5147456836631 / 50000) (2574531909283 / 25000) := by
  exact
    packedTile16384 102961408 102994176 12 1742 10146 27 _ _ (368997 / 20000) (461247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell102994176 :
    ThetaLowerSegment 102994176 103026944 (2574531909283 / 25000) (2575358476899 / 25000) := by
  exact
    packedTile16384 102994176 103026944 12 1792 10148 27 _ _ (1845017 / 100000) (92251 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103026944 :
    ThetaLowerSegment 103026944 103059712 (2575358476899 / 25000) (2060947678071 / 20000) := by
  exact
    packedTile16384 103026944 103059712 12 1791 10150 27 _ _ (1845049 / 100000) (461263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103059712 :
    ThetaLowerSegment 103059712 103092480 (2060947678071 / 20000) (82464756727 / 800) := by
  exact
    packedTile16384 103059712 103092480 12 1819 10151 27 _ _ (46127 / 2500) (1845083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103092480 :
    ThetaLowerSegment 103092480 103125248 (82464756727 / 800) (10311281099299 / 100000) := by
  exact
    packedTile16384 103092480 103125248 12 1727 10153 27 _ _ (230639 / 12500) (369023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103125248 :
    ThetaLowerSegment 103125248 103158016 (10311281099299 / 100000) (10314567300763 / 100000) := by
  exact
    packedTile16384 103125248 103158016 12 1781 10155 27 _ _ (230643 / 12500) (1845147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103158016 :
    ThetaLowerSegment 103158016 103190784 (10314567300763 / 100000) (82542548007 / 800) := by
  exact
    packedTile16384 103158016 103190784 12 1762 10156 27 _ _ (230647 / 12500) (1845179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103190784 :
    ThetaLowerSegment 103190784 103223552 (82542548007 / 800) (10321077138203 / 100000) := by
  exact
    packedTile16384 103190784 103223552 12 1766 10158 27 _ _ (230651 / 12500) (1845211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103223552 :
    ThetaLowerSegment 103223552 103256320 (10321077138203 / 100000) (10324254639761 / 100000) := by
  exact
    packedTile16384 103223552 103256320 12 1722 10159 27 _ _ (1845239 / 100000) (922621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103256320 :
    ThetaLowerSegment 103256320 103289088 (10324254639761 / 100000) (5163798212771 / 50000) := by
  exact
    packedTile16384 103256320 103289088 12 1811 10161 27 _ _ (1845271 / 100000) (922637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103289088 :
    ThetaLowerSegment 103289088 103321856 (5163798212771 / 50000) (10330890291397 / 100000) := by
  exact
    packedTile16384 103289088 103321856 12 1785 10163 27 _ _ (1845303 / 100000) (922653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103321856 :
    ThetaLowerSegment 103321856 103354624 (10330890291397 / 100000) (2066835735317 / 20000) := by
  exact
    packedTile16384 103321856 103354624 12 1782 10164 27 _ _ (922667 / 50000) (1845337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103354624 :
    ThetaLowerSegment 103354624 103387392 (2066835735317 / 20000) (10337492953921 / 100000) := by
  exact
    packedTile16384 103354624 103387392 12 1796 10166 27 _ _ (922683 / 50000) (1845369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103387392 :
    ThetaLowerSegment 103387392 103420160 (10337492953921 / 100000) (10340786989351 / 100000) := by
  exact
    packedTile16384 103387392 103420160 12 1785 10167 27 _ _ (922699 / 50000) (1845401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103420160 :
    ThetaLowerSegment 103420160 103452928 (10340786989351 / 100000) (10344125372221 / 100000) := by
  exact
    packedTile16384 103420160 103452928 12 1809 10169 27 _ _ (184543 / 10000) (1845433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103452928 :
    ThetaLowerSegment 103452928 103485696 (10344125372221 / 100000) (103473346289 / 1000) := by
  exact
    packedTile16384 103452928 103485696 12 1739 10171 27 _ _ (1845461 / 100000) (230683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103485696 :
    ThetaLowerSegment 103485696 103518464 (103473346289 / 1000) (10350658361793 / 100000) := by
  exact
    packedTile16384 103485696 103518464 12 1801 10172 27 _ _ (1845493 / 100000) (230687 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103518464 :
    ThetaLowerSegment 103518464 103551232 (10350658361793 / 100000) (1294237157271 / 12500) := by
  exact
    packedTile16384 103518464 103551232 12 1755 10174 27 _ _ (73821 / 4000) (230691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103551232 :
    ThetaLowerSegment 103551232 103584000 (1294237157271 / 12500) (2589287743349 / 25000) := by
  exact
    packedTile16384 103551232 103584000 12 1763 10176 27 _ _ (461389 / 25000) (1845559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103584000 :
    ThetaLowerSegment 103584000 103616768 (2589287743349 / 25000) (1295051054527 / 12500) := by
  exact
    packedTile16384 103584000 103616768 12 1765 10177 27 _ _ (461397 / 25000) (1845591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103616768 :
    ThetaLowerSegment 103616768 103649536 (1295051054527 / 12500) (5181819134733 / 50000) := by
  exact
    packedTile16384 103616768 103649536 12 1750 10179 27 _ _ (1845619 / 100000) (922811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103649536 :
    ThetaLowerSegment 103649536 103682304 (5181819134733 / 50000) (2591720730981 / 25000) := by
  exact
    packedTile16384 103649536 103682304 12 1758 10180 27 _ _ (1845651 / 100000) (922827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103682304 :
    ThetaLowerSegment 103682304 103715072 (2591720730981 / 25000) (10370177468079 / 100000) := by
  exact
    packedTile16384 103682304 103715072 12 1785 10182 27 _ _ (1845683 / 100000) (922843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103715072 :
    ThetaLowerSegment 103715072 103747840 (10370177468079 / 100000) (10373494216137 / 100000) := by
  exact
    packedTile16384 103715072 103747840 12 1797 10184 27 _ _ (922857 / 50000) (1845717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103747840 :
    ThetaLowerSegment 103747840 103780608 (10373494216137 / 100000) (10376755649319 / 100000) := by
  exact
    packedTile16384 103747840 103780608 12 1767 10185 27 _ _ (922873 / 50000) (1845749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103780608 :
    ThetaLowerSegment 103780608 103813376 (10376755649319 / 100000) (1297500757827 / 12500) := by
  exact
    packedTile16384 103780608 103813376 12 1761 10187 27 _ _ (1845777 / 100000) (92289 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103813376 :
    ThetaLowerSegment 103813376 103846144 (1297500757827 / 12500) (5191607039329 / 50000) := by
  exact
    packedTile16384 103813376 103846144 12 1738 10188 27 _ _ (1845809 / 100000) (461453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103846144 :
    ThetaLowerSegment 103846144 103878912 (5191607039329 / 50000) (1298320304279 / 12500) := by
  exact
    packedTile16384 103846144 103878912 12 1814 10190 27 _ _ (1845841 / 100000) (461461 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103878912 :
    ThetaLowerSegment 103878912 103911680 (1298320304279 / 12500) (1298730318597 / 12500) := by
  exact
    packedTile16384 103878912 103911680 12 1777 10192 27 _ _ (115367 / 6250) (14767 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103911680 :
    ThetaLowerSegment 103911680 103944448 (1298730318597 / 12500) (1299138032643 / 12500) := by
  exact
    packedTile16384 103911680 103944448 12 1767 10193 27 _ _ (115369 / 6250) (1845907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103944448 :
    ThetaLowerSegment 103944448 103977216 (1299138032643 / 12500) (10396414022599 / 100000) := by
  exact
    packedTile16384 103944448 103977216 12 1793 10195 27 _ _ (369187 / 20000) (922969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell103977216 :
    ThetaLowerSegment 103977216 104009984 (10396414022599 / 100000) (10399721995463 / 100000) := by
  exact
    packedTile16384 103977216 104009984 12 1792 10196 27 _ _ (1845967 / 100000) (184597 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104009984 :
    ThetaLowerSegment 104009984 104042752 (10399721995463 / 100000) (10403068789837 / 100000) := by
  exact
    packedTile16384 104009984 104042752 12 1813 10198 27 _ _ (922999 / 50000) (1846001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104042752 :
    ThetaLowerSegment 104042752 104075520 (10403068789837 / 100000) (10406397181927 / 100000) := by
  exact
    packedTile16384 104042752 104075520 12 1803 10200 27 _ _ (184603 / 10000) (1846033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104075520 :
    ThetaLowerSegment 104075520 104108288 (10406397181927 / 100000) (520481666343 / 5000) := by
  exact
    packedTile16384 104075520 104108288 12 1753 10201 27 _ _ (1846061 / 100000) (115379 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104108288 :
    ThetaLowerSegment 104108288 104141056 (520481666343 / 5000) (2082604181503 / 20000) := by
  exact
    packedTile16384 104108288 104141056 12 1835 10203 27 _ _ (1846093 / 100000) (115381 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104141056 :
    ThetaLowerSegment 104141056 104173824 (2082604181503 / 20000) (10416290393119 / 100000) := by
  exact
    packedTile16384 104141056 104173824 12 1771 10204 27 _ _ (461531 / 25000) (1846127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104173824 :
    ThetaLowerSegment 104173824 104206592 (10416290393119 / 100000) (10419526704587 / 100000) := by
  exact
    packedTile16384 104173824 104206592 12 1753 10206 27 _ _ (461539 / 25000) (1846159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104206592 :
    ThetaLowerSegment 104206592 104239360 (10419526704587 / 100000) (521144245937 / 5000) := by
  exact
    packedTile16384 104206592 104239360 12 1819 10208 27 _ _ (1846187 / 100000) (184619 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104239360 :
    ThetaLowerSegment 104239360 104272128 (521144245937 / 5000) (10426250575977 / 100000) := by
  exact
    packedTile16384 104239360 104272128 12 1823 10209 27 _ _ (1846219 / 100000) (923111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104272128 :
    ThetaLowerSegment 104272128 104304896 (10426250575977 / 100000) (10429498129727 / 100000) := by
  exact
    packedTile16384 104272128 104304896 12 1759 10211 27 _ _ (1477 / 80) (1846253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104304896 :
    ThetaLowerSegment 104304896 104337664 (10429498129727 / 100000) (10432736506601 / 100000) := by
  exact
    packedTile16384 104304896 104337664 12 1754 10212 27 _ _ (1846281 / 100000) (461571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104337664 :
    ThetaLowerSegment 104337664 104370432 (10432736506601 / 100000) (10436008173237 / 100000) := by
  exact
    packedTile16384 104337664 104370432 12 1772 10214 27 _ _ (1846313 / 100000) (461579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104370432 :
    ThetaLowerSegment 104370432 104403200 (10436008173237 / 100000) (10439257738677 / 100000) := by
  exact
    packedTile16384 104370432 104403200 12 1760 10216 27 _ _ (230793 / 12500) (1846347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104403200 :
    ThetaLowerSegment 104403200 104435968 (10439257738677 / 100000) (10442579369101 / 100000) := by
  exact
    packedTile16384 104403200 104435968 12 1799 10217 27 _ _ (230797 / 12500) (1846379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104435968 :
    ThetaLowerSegment 104435968 104468736 (10442579369101 / 100000) (5222917292321 / 50000) := by
  exact
    packedTile16384 104435968 104468736 12 1763 10219 27 _ _ (1846407 / 100000) (184641 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104468736 :
    ThetaLowerSegment 104468736 104501504 (5222917292321 / 50000) (5224551389951 / 50000) := by
  exact
    packedTile16384 104468736 104501504 12 1770 10220 27 _ _ (923219 / 50000) (1846441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104501504 :
    ThetaLowerSegment 104501504 104534272 (5224551389951 / 50000) (653272381657 / 6250) := by
  exact
    packedTile16384 104501504 104534272 12 1763 10222 27 _ _ (184647 / 10000) (1846473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104534272 :
    ThetaLowerSegment 104534272 104567040 (653272381657 / 6250) (1045564118529 / 10000) := by
  exact
    packedTile16384 104534272 104567040 12 1778 10224 27 _ _ (1846501 / 100000) (230813 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104567040 :
    ThetaLowerSegment 104567040 104599808 (1045564118529 / 10000) (5229466775923 / 50000) := by
  exact
    packedTile16384 104567040 104599808 12 1783 10225 27 _ _ (461633 / 25000) (369307 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104599808 :
    ThetaLowerSegment 104599808 104632576 (5229466775923 / 50000) (5231131453369 / 50000) := by
  exact
    packedTile16384 104599808 104632576 12 1803 10227 27 _ _ (461641 / 25000) (1846567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104632576 :
    ThetaLowerSegment 104632576 104665344 (5231131453369 / 50000) (5232737991019 / 50000) := by
  exact
    packedTile16384 104632576 104665344 12 1740 10229 27 _ _ (369319 / 20000) (923299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104665344 :
    ThetaLowerSegment 104665344 104698112 (5232737991019 / 50000) (1046867433827 / 10000) := by
  exact
    packedTile16384 104665344 104698112 12 1732 10230 27 _ _ (923313 / 50000) (1846629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104698112 :
    ThetaLowerSegment 104698112 104730880 (1046867433827 / 10000) (209438489127 / 2000) := by
  exact
    packedTile16384 104698112 104730880 12 1760 10232 27 _ _ (923329 / 50000) (1846661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104730880 :
    ThetaLowerSegment 104730880 104763648 (209438489127 / 2000) (2618811200793 / 25000) := by
  exact
    packedTile16384 104730880 104763648 12 1798 10233 27 _ _ (1846689 / 100000) (461673 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104763648 :
    ThetaLowerSegment 104763648 104796416 (2618811200793 / 25000) (2619619140793 / 25000) := by
  exact
    packedTile16384 104763648 104796416 12 1750 10235 27 _ _ (11542 / 625) (1846723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104796416 :
    ThetaLowerSegment 104796416 104829184 (2619619140793 / 25000) (2620450640881 / 25000) := by
  exact
    packedTile16384 104796416 104829184 12 1801 10237 27 _ _ (57711 / 3125) (369351 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104829184 :
    ThetaLowerSegment 104829184 104861952 (2620450640881 / 25000) (5242550458981 / 50000) := by
  exact
    packedTile16384 104829184 104861952 12 1786 10238 27 _ _ (1846783 / 100000) (923393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104861952 :
    ThetaLowerSegment 104861952 104894720 (5242550458981 / 50000) (5244173808487 / 50000) := by
  exact
    packedTile16384 104861952 104894720 12 1758 10240 27 _ _ (923407 / 50000) (1846817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104894720 :
    ThetaLowerSegment 104894720 104927488 (5244173808487 / 50000) (10491607298399 / 100000) := by
  exact
    packedTile16384 104894720 104927488 12 1765 10241 27 _ _ (369369 / 20000) (57714 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104927488 :
    ThetaLowerSegment 104927488 104960256 (10491607298399 / 100000) (10494865189427 / 100000) := by
  exact
    packedTile16384 104927488 104960256 12 1764 10243 27 _ _ (1846877 / 100000) (11543 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104960256 :
    ThetaLowerSegment 104960256 104993024 (10494865189427 / 100000) (10498169307839 / 100000) := by
  exact
    packedTile16384 104960256 104993024 12 1789 10245 27 _ _ (461727 / 25000) (1846911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell104993024 :
    ThetaLowerSegment 104993024 105025792 (10498169307839 / 100000) (10501401451089 / 100000) := by
  exact
    packedTile16384 104993024 105025792 12 1750 10246 27 _ _ (1846939 / 100000) (923471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105025792 :
    ThetaLowerSegment 105025792 105058560 (10501401451089 / 100000) (10504735231939 / 100000) := by
  exact
    packedTile16384 105025792 105058560 12 1805 10248 27 _ _ (184697 / 10000) (1846973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105058560 :
    ThetaLowerSegment 105058560 105091328 (10504735231939 / 100000) (1313497551587 / 12500) := by
  exact
    packedTile16384 105058560 105091328 12 1757 10249 27 _ _ (1847001 / 100000) (461751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105091328 :
    ThetaLowerSegment 105091328 105124096 (1313497551587 / 12500) (2627817032859 / 25000) := by
  exact
    packedTile16384 105091328 105124096 12 1780 10251 27 _ _ (1847033 / 100000) (461759 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105124096 :
    ThetaLowerSegment 105124096 105156864 (2627817032859 / 25000) (2628644979297 / 25000) := by
  exact
    packedTile16384 105124096 105156864 12 1793 10253 27 _ _ (230883 / 12500) (1847067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105156864 :
    ThetaLowerSegment 105156864 105189632 (2628644979297 / 25000) (10517880675953 / 100000) := by
  exact
    packedTile16384 105156864 105189632 12 1787 10254 27 _ _ (369419 / 20000) (923549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105189632 :
    ThetaLowerSegment 105189632 105222400 (10517880675953 / 100000) (10521196267123 / 100000) := by
  exact
    packedTile16384 105189632 105222400 12 1795 10256 27 _ _ (923563 / 50000) (1847129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105222400 :
    ThetaLowerSegment 105222400 105255168 (10521196267123 / 100000) (10524443569129 / 100000) := by
  exact
    packedTile16384 105222400 105255168 12 1758 10257 27 _ _ (1847157 / 100000) (46179 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105255168 :
    ThetaLowerSegment 105255168 105287936 (10524443569129 / 100000) (10527637357181 / 100000) := by
  exact
    packedTile16384 105255168 105287936 12 1729 10259 27 _ _ (461797 / 25000) (1847191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105287936 :
    ThetaLowerSegment 105287936 105320704 (10527637357181 / 100000) (10530929101439 / 100000) := by
  exact
    packedTile16384 105287936 105320704 12 1782 10260 27 _ _ (1847219 / 100000) (923611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105320704 :
    ThetaLowerSegment 105320704 105353472 (10530929101439 / 100000) (10534206124713 / 100000) := by
  exact
    packedTile16384 105320704 105353472 12 1774 10262 27 _ _ (1847251 / 100000) (923627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105353472 :
    ThetaLowerSegment 105353472 105386240 (10534206124713 / 100000) (2107506615919 / 20000) := by
  exact
    packedTile16384 105353472 105386240 12 1801 10264 27 _ _ (923641 / 50000) (369457 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105386240 :
    ThetaLowerSegment 105386240 105419008 (2107506615919 / 20000) (10540824991361 / 100000) := by
  exact
    packedTile16384 105386240 105419008 12 1782 10265 27 _ _ (1847313 / 100000) (461829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105419008 :
    ThetaLowerSegment 105419008 105451776 (10540824991361 / 100000) (10544063385393 / 100000) := by
  exact
    packedTile16384 105419008 105451776 12 1753 10267 27 _ _ (115459 / 6250) (1847347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105451776 :
    ThetaLowerSegment 105451776 105484544 (10544063385393 / 100000) (2636834695317 / 25000) := by
  exact
    packedTile16384 105451776 105484544 12 1773 10268 27 _ _ (14779 / 800) (923689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105484544 :
    ThetaLowerSegment 105484544 105517312 (2636834695317 / 25000) (5275294184211 / 50000) := by
  exact
    packedTile16384 105484544 105517312 12 1759 10270 27 _ _ (923703 / 50000) (1847409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105517312 :
    ThetaLowerSegment 105517312 105550080 (5275294184211 / 50000) (10553826925483 / 100000) := by
  exact
    packedTile16384 105517312 105550080 12 1753 10272 27 _ _ (1847437 / 100000) (23093 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105550080 :
    ThetaLowerSegment 105550080 105582848 (10553826925483 / 100000) (2111420866743 / 20000) := by
  exact
    packedTile16384 105550080 105582848 12 1774 10273 27 _ _ (461867 / 25000) (1847471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105582848 :
    ThetaLowerSegment 105582848 105615616 (2111420866743 / 20000) (2112071186391 / 20000) := by
  exact
    packedTile16384 105582848 105615616 12 1760 10275 27 _ _ (1847499 / 100000) (923751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105615616 :
    ThetaLowerSegment 105615616 105648384 (2112071186391 / 20000) (2112727059541 / 20000) := by
  exact
    packedTile16384 105615616 105648384 12 1775 10276 27 _ _ (184753 / 10000) (1847533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105648384 :
    ThetaLowerSegment 105648384 105681152 (2112727059541 / 20000) (5283440731191 / 50000) := by
  exact
    packedTile16384 105648384 105681152 12 1757 10278 27 _ _ (1847561 / 100000) (461891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105681152 :
    ThetaLowerSegment 105681152 105713920 (5283440731191 / 50000) (1057015909059 / 10000) := by
  exact
    packedTile16384 105681152 105713920 12 1774 10280 27 _ _ (230949 / 12500) (369519 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105713920 :
    ThetaLowerSegment 105713920 105746688 (1057015909059 / 10000) (10573497745351 / 100000) := by
  exact
    packedTile16384 105713920 105746688 12 1807 10281 27 _ _ (1847623 / 100000) (923813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105746688 :
    ThetaLowerSegment 105746688 105779456 (10573497745351 / 100000) (10576749616391 / 100000) := by
  exact
    packedTile16384 105746688 105779456 12 1760 10283 27 _ _ (923827 / 50000) (1847657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105779456 :
    ThetaLowerSegment 105779456 105812224 (10576749616391 / 100000) (10580042191061 / 100000) := by
  exact
    packedTile16384 105779456 105812224 12 1782 10284 27 _ _ (369537 / 20000) (230961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105812224 :
    ThetaLowerSegment 105812224 105844992 (10580042191061 / 100000) (10583332973257 / 100000) := by
  exact
    packedTile16384 105812224 105844992 12 1781 10286 27 _ _ (461929 / 25000) (1847719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105844992 :
    ThetaLowerSegment 105844992 105877760 (10583332973257 / 100000) (10586618267423 / 100000) := by
  exact
    packedTile16384 105844992 105877760 12 1778 10288 27 _ _ (1847747 / 100000) (7391 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105877760 :
    ThetaLowerSegment 105877760 105910528 (10586618267423 / 100000) (423594740357 / 4000) := by
  exact
    packedTile16384 105877760 105910528 12 1759 10289 27 _ _ (923889 / 50000) (1847781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105910528 :
    ThetaLowerSegment 105910528 105943296 (423594740357 / 4000) (662068539453 / 6250) := by
  exact
    packedTile16384 105910528 105943296 12 1747 10291 27 _ _ (1847809 / 100000) (461953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105943296 :
    ThetaLowerSegment 105943296 105976064 (662068539453 / 6250) (662274573613 / 6250) := by
  exact
    packedTile16384 105943296 105976064 12 1784 10292 27 _ _ (11549 / 625) (1847843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell105976064 :
    ThetaLowerSegment 105976064 106008832 (662274573613 / 6250) (10599654670123 / 100000) := by
  exact
    packedTile16384 105976064 106008832 12 1765 10294 27 _ _ (1847871 / 100000) (923937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106008832 :
    ThetaLowerSegment 106008832 106041600 (10599654670123 / 100000) (10602873715407 / 100000) := by
  exact
    packedTile16384 106008832 106041600 12 1742 10296 27 _ _ (923951 / 50000) (369581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106041600 :
    ThetaLowerSegment 106041600 106074368 (10602873715407 / 100000) (5303106465169 / 50000) := by
  exact
    packedTile16384 106041600 106074368 12 1807 10297 27 _ _ (1847933 / 100000) (57748 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106074368 :
    ThetaLowerSegment 106074368 106107136 (5303106465169 / 50000) (5304728977561 / 50000) := by
  exact
    packedTile16384 106074368 106107136 12 1756 10299 27 _ _ (461991 / 25000) (1847967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106107136 :
    ThetaLowerSegment 106107136 106139904 (5304728977561 / 50000) (663295672031 / 6250) := by
  exact
    packedTile16384 106107136 106139904 12 1771 10300 27 _ _ (923997 / 50000) (1847997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106139904 :
    ThetaLowerSegment 106139904 106172672 (663295672031 / 6250) (5307975006023 / 50000) := by
  exact
    packedTile16384 106139904 106172672 12 1742 10302 27 _ _ (73921 / 4000) (462007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106172672 :
    ThetaLowerSegment 106172672 106205440 (5307975006023 / 50000) (5309649344759 / 50000) := by
  exact
    packedTile16384 106172672 106205440 12 1812 10304 27 _ _ (231007 / 12500) (1848059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106205440 :
    ThetaLowerSegment 106205440 106238208 (5309649344759 / 50000) (10622545778377 / 100000) := by
  exact
    packedTile16384 106205440 106238208 12 1757 10305 27 _ _ (1848087 / 100000) (184809 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106238208 :
    ThetaLowerSegment 106238208 106270976 (10622545778377 / 100000) (10625746718753 / 100000) := by
  exact
    packedTile16384 106238208 106270976 12 1732 10307 27 _ _ (924059 / 50000) (1848121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106270976 :
    ThetaLowerSegment 106270976 106303744 (10625746718753 / 100000) (5314552402743 / 50000) := by
  exact
    packedTile16384 106270976 106303744 12 1817 10308 27 _ _ (1848149 / 100000) (231019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106303744 :
    ThetaLowerSegment 106303744 106336512 (5314552402743 / 50000) (5316211144293 / 50000) := by
  exact
    packedTile16384 106303744 106336512 12 1795 10310 27 _ _ (92409 / 5000) (1848183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106336512 :
    ThetaLowerSegment 106336512 106369280 (5316211144293 / 50000) (5317839417303 / 50000) := by
  exact
    packedTile16384 106336512 106369280 12 1762 10311 27 _ _ (184821 / 10000) (1848213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106369280 :
    ThetaLowerSegment 106369280 106402048 (5317839417303 / 50000) (2659728314089 / 25000) := by
  exact
    packedTile16384 106369280 106402048 12 1750 10313 27 _ _ (1848241 / 100000) (462061 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106402048 :
    ThetaLowerSegment 106402048 106434816 (2659728314089 / 25000) (2660553105469 / 25000) := by
  exact
    packedTile16384 106402048 106434816 12 1785 10315 27 _ _ (115517 / 6250) (73931 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106434816 :
    ThetaLowerSegment 106434816 106467584 (2660553105469 / 25000) (5322738262487 / 50000) := by
  exact
    packedTile16384 106434816 106467584 12 1766 10316 27 _ _ (1848303 / 100000) (924153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106467584 :
    ThetaLowerSegment 106467584 106500352 (5322738262487 / 50000) (5324372189743 / 50000) := by
  exact
    packedTile16384 106467584 106500352 12 1768 10318 27 _ _ (924167 / 50000) (1848337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106500352 :
    ThetaLowerSegment 106500352 106533120 (5324372189743 / 50000) (5326035717343 / 50000) := by
  exact
    packedTile16384 106500352 106533120 12 1800 10319 27 _ _ (462091 / 25000) (1848367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106533120 :
    ThetaLowerSegment 106533120 106565888 (5326035717343 / 50000) (5327680788893 / 50000) := by
  exact
    packedTile16384 106533120 106565888 12 1780 10321 27 _ _ (369679 / 20000) (924199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106565888 :
    ThetaLowerSegment 106565888 106598656 (5327680788893 / 50000) (5329346220719 / 50000) := by
  exact
    packedTile16384 106565888 106598656 12 1802 10323 27 _ _ (924213 / 50000) (1848429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106598656 :
    ThetaLowerSegment 106598656 106631424 (5329346220719 / 50000) (5330958075223 / 50000) := by
  exact
    packedTile16384 106598656 106631424 12 1744 10324 27 _ _ (1848457 / 100000) (92423 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106631424 :
    ThetaLowerSegment 106631424 106664192 (5330958075223 / 50000) (2133040182369 / 20000) := by
  exact
    packedTile16384 106631424 106664192 12 1777 10326 27 _ _ (1848487 / 100000) (184849 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106664192 :
    ThetaLowerSegment 106664192 106696960 (2133040182369 / 20000) (10668487576849 / 100000) := by
  exact
    packedTile16384 106664192 106696960 12 1778 10327 27 _ _ (924259 / 50000) (1848521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106696960 :
    ThetaLowerSegment 106696960 106729728 (10668487576849 / 100000) (5335852950329 / 50000) := by
  exact
    packedTile16384 106696960 106729728 12 1741 10329 27 _ _ (1848549 / 100000) (231069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106729728 :
    ThetaLowerSegment 106729728 106762496 (5335852950329 / 50000) (5337475079279 / 50000) := by
  exact
    packedTile16384 106729728 106762496 12 1755 10331 27 _ _ (92429 / 5000) (1848583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106762496 :
    ThetaLowerSegment 106762496 106795264 (5337475079279 / 50000) (5339087067199 / 50000) := by
  exact
    packedTile16384 106762496 106795264 12 1744 10332 27 _ _ (184861 / 10000) (1848613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106795264 :
    ThetaLowerSegment 106795264 106828032 (5339087067199 / 50000) (10681525720531 / 100000) := by
  exact
    packedTile16384 106795264 106828032 12 1813 10334 27 _ _ (1848641 / 100000) (462161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106828032 :
    ThetaLowerSegment 106828032 106860800 (10681525720531 / 100000) (10684796021299 / 100000) := by
  exact
    packedTile16384 106828032 106860800 12 1769 10335 27 _ _ (57771 / 3125) (73947 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106860800 :
    ThetaLowerSegment 106860800 106893568 (10684796021299 / 100000) (10688058980329 / 100000) := by
  exact
    packedTile16384 106860800 106893568 12 1765 10337 27 _ _ (924351 / 50000) (369741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106893568 :
    ThetaLowerSegment 106893568 106926336 (10688058980329 / 100000) (10691272078283 / 100000) := by
  exact
    packedTile16384 106893568 106926336 12 1738 10338 27 _ _ (1848733 / 100000) (57773 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106926336 :
    ThetaLowerSegment 106926336 106959104 (10691272078283 / 100000) (2138913684899 / 20000) := by
  exact
    packedTile16384 106926336 106959104 12 1783 10340 27 _ _ (462191 / 25000) (1848767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106959104 :
    ThetaLowerSegment 106959104 106991872 (2138913684899 / 20000) (10697866672991 / 100000) := by
  exact
    packedTile16384 106959104 106991872 12 1784 10342 27 _ _ (924397 / 50000) (1848797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell106991872 :
    ThetaLowerSegment 106991872 107024640 (10697866672991 / 100000) (5350607447533 / 50000) := by
  exact
    packedTile16384 106991872 107024640 12 1811 10343 27 _ _ (73953 / 4000) (462207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107024640 :
    ThetaLowerSegment 107024640 107057408 (5350607447533 / 50000) (10704430053911 / 100000) := by
  exact
    packedTile16384 107024640 107057408 12 1739 10345 27 _ _ (369771 / 20000) (924429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107057408 :
    ThetaLowerSegment 107057408 107090176 (10704430053911 / 100000) (10707693337701 / 100000) := by
  exact
    packedTile16384 107057408 107090176 12 1765 10346 27 _ _ (924443 / 50000) (1848889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107090176 :
    ThetaLowerSegment 107090176 107122944 (10707693337701 / 100000) (2677745640261 / 25000) := by
  exact
    packedTile16384 107090176 107122944 12 1779 10348 27 _ _ (1848917 / 100000) (46223 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107122944 :
    ThetaLowerSegment 107122944 107155712 (2677745640261 / 25000) (2142855846709 / 20000) := by
  exact
    packedTile16384 107122944 107155712 12 1783 10350 27 _ _ (1848947 / 100000) (36979 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107155712 :
    ThetaLowerSegment 107155712 107188480 (2142855846709 / 20000) (2143523327767 / 20000) := by
  exact
    packedTile16384 107155712 107188480 12 1805 10351 27 _ _ (924489 / 50000) (1848981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107188480 :
    ThetaLowerSegment 107188480 107221248 (2143523327767 / 20000) (10720937457203 / 100000) := by
  exact
    packedTile16384 107188480 107221248 12 1796 10353 27 _ _ (115563 / 6250) (1849011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107221248 :
    ThetaLowerSegment 107221248 107254016 (10720937457203 / 100000) (10724254633169 / 100000) := by
  exact
    packedTile16384 107221248 107254016 12 1794 10354 27 _ _ (1849039 / 100000) (924521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107254016 :
    ThetaLowerSegment 107254016 107286784 (10724254633169 / 100000) (10727516392649 / 100000) := by
  exact
    packedTile16384 107254016 107286784 12 1764 10356 27 _ _ (184907 / 10000) (1849073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107286784 :
    ThetaLowerSegment 107286784 107319552 (10727516392649 / 100000) (10730813337949 / 100000) := by
  exact
    packedTile16384 107286784 107319552 12 1783 10357 27 _ _ (18491 / 1000) (1849103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107319552 :
    ThetaLowerSegment 107319552 107352320 (10730813337949 / 100000) (10734119584177 / 100000) := by
  exact
    packedTile16384 107319552 107352320 12 1788 10359 27 _ _ (1849131 / 100000) (924567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107352320 :
    ThetaLowerSegment 107352320 107385088 (10734119584177 / 100000) (1342171532297 / 12500) := by
  exact
    packedTile16384 107352320 107385088 12 1759 10361 27 _ _ (1849161 / 100000) (462291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107385088 :
    ThetaLowerSegment 107385088 107417856 (1342171532297 / 12500) (671292066631 / 6250) := by
  exact
    packedTile16384 107385088 107417856 12 1785 10362 27 _ _ (231149 / 12500) (369839 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107417856 :
    ThetaLowerSegment 107417856 107450624 (671292066631 / 6250) (1342999283601 / 12500) := by
  exact
    packedTile16384 107417856 107450624 12 1796 10364 27 _ _ (924611 / 50000) (73969 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107450624 :
    ThetaLowerSegment 107450624 107483392 (1342999283601 / 12500) (671703984257 / 6250) := by
  exact
    packedTile16384 107450624 107483392 12 1768 10365 27 _ _ (1849253 / 100000) (231157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107483392 :
    ThetaLowerSegment 107483392 107516160 (671703984257 / 6250) (5375238900983 / 50000) := by
  exact
    packedTile16384 107483392 107516160 12 1738 10367 27 _ _ (1849283 / 100000) (924643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107516160 :
    ThetaLowerSegment 107516160 107548928 (5375238900983 / 50000) (1344217730147 / 12500) := by
  exact
    packedTile16384 107516160 107548928 12 1765 10368 27 _ _ (924657 / 50000) (1849317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107548928 :
    ThetaLowerSegment 107548928 107581696 (1344217730147 / 12500) (1344622967651 / 12500) := by
  exact
    packedTile16384 107548928 107581696 12 1753 10370 27 _ _ (57792 / 3125) (1849347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107581696 :
    ThetaLowerSegment 107581696 107614464 (1344622967651 / 12500) (10760277478083 / 100000) := by
  exact
    packedTile16384 107581696 107614464 12 1781 10372 27 _ _ (2959 / 160) (924689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107614464 :
    ThetaLowerSegment 107614464 107647232 (10760277478083 / 100000) (5381813375269 / 50000) := by
  exact
    packedTile16384 107614464 107647232 12 1811 10373 27 _ _ (369881 / 20000) (57794 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107647232 :
    ThetaLowerSegment 107647232 107663616 (5381813375269 / 50000) (5382632675417 / 50000) := by
  exact
    packedTile16384 107647232 107663616 11 886 10375 27 _ _ (462359 / 25000) (1849439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107663616 :
    ThetaLowerSegment 107663616 107667712 (5382632675417 / 50000) (10765696272917 / 100000) := by
  exact
    packedTile16384 107663616 107667712 9 233 10376 27 _ _ (1849451 / 100000) (924727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_88412416_107667712 :
    ThetaLowerSegment 88412416 107667712 (1768014080011 / 20000) (10765696272917 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell88412416 cell88445184)
                      (ThetaLowerSegment.join cell88477952 cell88510720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell88543488 cell88576256)
                      (ThetaLowerSegment.join cell88609024 cell88641792)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell88674560 cell88707328)
                      (ThetaLowerSegment.join cell88740096 cell88772864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell88805632 cell88838400)
                      (ThetaLowerSegment.join cell88871168 cell88903936))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell88936704 cell88969472)
                      (ThetaLowerSegment.join cell89002240 cell89035008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89067776 cell89100544)
                      (ThetaLowerSegment.join cell89133312 cell89166080)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89198848 cell89231616)
                      (ThetaLowerSegment.join cell89264384 cell89297152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89329920 cell89362688)
                      (ThetaLowerSegment.join cell89395456 cell89428224)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89460992 cell89493760)
                      (ThetaLowerSegment.join cell89526528 cell89559296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89592064 cell89624832)
                      (ThetaLowerSegment.join cell89657600 cell89690368)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89723136 cell89739520)
                      (ThetaLowerSegment.join cell89755904 cell89772288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89788672 cell89805056)
                      (ThetaLowerSegment.join cell89821440 cell89837824))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89854208 cell89870592)
                      (ThetaLowerSegment.join cell89886976 cell89903360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89919744 cell89936128)
                      (ThetaLowerSegment.join cell89952512 cell89968896)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell89985280 cell90001664)
                      (ThetaLowerSegment.join cell90018048 cell90034432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90050816 cell90067200)
                      (ThetaLowerSegment.join cell90083584 cell90099968))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90116352 cell90132736)
                      (ThetaLowerSegment.join cell90149120 cell90165504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90198272 cell90231040)
                      (ThetaLowerSegment.join cell90247424 cell90280192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90312960 cell90345728)
                      (ThetaLowerSegment.join cell90378496 cell90411264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90444032 cell90476800)
                      (ThetaLowerSegment.join cell90509568 cell90542336))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90575104 cell90607872)
                      (ThetaLowerSegment.join cell90640640 cell90673408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90706176 cell90738944)
                      (ThetaLowerSegment.join cell90771712 cell90804480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90837248 cell90870016)
                      (ThetaLowerSegment.join cell90902784 cell90935552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell90968320 cell91001088)
                      (ThetaLowerSegment.join cell91033856 cell91066624)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell91099392 cell91132160)
                      (ThetaLowerSegment.join cell91164928 cell91197696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell91230464 cell91263232)
                      (ThetaLowerSegment.join cell91296000 cell91328768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell91361536 cell91394304)
                      (ThetaLowerSegment.join cell91427072 cell91459840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell91492608 cell91525376)
                      (ThetaLowerSegment.join cell91558144 cell91590912))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell91623680 cell91656448)
                      (ThetaLowerSegment.join cell91689216 cell91721984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell91754752 cell91787520)
                      (ThetaLowerSegment.join cell91820288 cell91853056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell91885824 cell91918592)
                      (ThetaLowerSegment.join cell91951360 cell91984128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell92016896 cell92049664)
                      (ThetaLowerSegment.join cell92082432 cell92115200)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell92147968 cell92180736)
                      (ThetaLowerSegment.join cell92213504 cell92246272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell92279040 cell92311808)
                      (ThetaLowerSegment.join cell92344576 cell92377344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell92410112 cell92442880)
                      (ThetaLowerSegment.join cell92475648 cell92508416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell92541184 cell92573952)
                      (ThetaLowerSegment.join cell92606720 cell92639488))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell92672256 cell92705024)
                      (ThetaLowerSegment.join cell92737792 cell92770560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell92803328 cell92836096)
                      (ThetaLowerSegment.join cell92868864 cell92901632)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell92934400 cell92967168)
                      (ThetaLowerSegment.join cell92999936 cell93032704))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93065472 cell93098240)
                      (ThetaLowerSegment.join cell93131008 cell93147392)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93163776 cell93196544)
                      (ThetaLowerSegment.join cell93229312 cell93262080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93294848 cell93311232)
                      (ThetaLowerSegment.join cell93327616 cell93360384)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93393152 cell93425920)
                      (ThetaLowerSegment.join cell93458688 cell93491456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93524224 cell93556992)
                      (ThetaLowerSegment.join cell93589760 cell93622528))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93655296 cell93688064)
                      (ThetaLowerSegment.join cell93720832 cell93737216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93753600 cell93769984)
                      (ThetaLowerSegment.join cell93802752 cell93819136)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93835520 cell93851904)
                      (ThetaLowerSegment.join cell93868288 cell93884672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell93901056 cell93933824)
                      (ThetaLowerSegment.join cell93966592 cell93999360))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell94015744 cell94032128)
                      (ThetaLowerSegment.join cell94064896 cell94097664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell94130432 cell94163200)
                      (ThetaLowerSegment.join cell94195968 cell94228736)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell94261504 cell94294272)
                      (ThetaLowerSegment.join cell94327040 cell94359808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell94392576 cell94425344)
                      (ThetaLowerSegment.join cell94458112 cell94490880))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell94523648 cell94556416)
                      (ThetaLowerSegment.join cell94589184 cell94621952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell94654720 cell94687488)
                      (ThetaLowerSegment.join cell94720256 cell94736640)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell94769408 cell94802176)
                      (ThetaLowerSegment.join cell94834944 cell94867712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell94900480 cell94933248)
                      (ThetaLowerSegment.join cell94966016 cell94998784)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell95031552 cell95064320)
                      (ThetaLowerSegment.join cell95097088 cell95129856))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell95162624 cell95195392)
                      (ThetaLowerSegment.join cell95228160 cell95260928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell95293696 cell95326464)
                      (ThetaLowerSegment.join cell95359232 cell95392000))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell95424768 cell95457536)
                      (ThetaLowerSegment.join cell95490304 cell95523072))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell95555840 cell95588608)
                      (ThetaLowerSegment.join cell95621376 cell95654144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell95686912 cell95719680)
                      (ThetaLowerSegment.join cell95752448 cell95785216)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell95817984 cell95850752)
                      (ThetaLowerSegment.join cell95883520 cell95916288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell95949056 cell95981824)
                      (ThetaLowerSegment.join cell96014592 cell96047360))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell96080128 cell96112896)
                      (ThetaLowerSegment.join cell96145664 cell96178432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell96211200 cell96243968)
                      (ThetaLowerSegment.join cell96276736 cell96309504)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell96342272 cell96375040)
                      (ThetaLowerSegment.join cell96407808 cell96440576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell96473344 cell96506112)
                      (ThetaLowerSegment.join cell96538880 cell96571648))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell96604416 cell96637184)
                      (ThetaLowerSegment.join cell96669952 cell96702720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell96735488 cell96768256)
                      (ThetaLowerSegment.join cell96801024 cell96833792)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell96866560 cell96899328)
                      (ThetaLowerSegment.join cell96932096 cell96964864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell96997632 cell97030400)
                      (ThetaLowerSegment.join cell97063168 cell97095936)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell97128704 cell97161472)
                      (ThetaLowerSegment.join cell97194240 cell97227008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell97259776 cell97292544)
                      (ThetaLowerSegment.join cell97325312 cell97358080)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell97390848 cell97423616)
                      (ThetaLowerSegment.join cell97456384 cell97489152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell97521920 cell97554688)
                      (ThetaLowerSegment.join cell97587456 cell97620224))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell97652992 cell97685760)
                      (ThetaLowerSegment.join cell97718528 cell97751296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell97784064 cell97816832)
                      (ThetaLowerSegment.join cell97849600 cell97882368)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell97915136 cell97947904)
                      (ThetaLowerSegment.join cell97980672 cell98013440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell98046208 cell98078976)
                      (ThetaLowerSegment.join cell98111744 cell98144512))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell98177280 cell98210048)
                      (ThetaLowerSegment.join cell98242816 cell98275584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell98308352 cell98341120)
                      (ThetaLowerSegment.join cell98373888 cell98406656)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell98439424 cell98472192)
                      (ThetaLowerSegment.join cell98504960 cell98537728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell98570496 cell98603264)
                      (ThetaLowerSegment.join cell98636032 cell98668800))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell98701568 cell98734336)
                      (ThetaLowerSegment.join cell98767104 cell98799872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell98832640 cell98865408)
                      (ThetaLowerSegment.join cell98898176 cell98930944)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell98963712 cell98996480)
                      (ThetaLowerSegment.join cell99029248 cell99062016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell99094784 cell99127552)
                      (ThetaLowerSegment.join cell99160320 cell99193088)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell99225856 cell99258624)
                      (ThetaLowerSegment.join cell99291392 cell99324160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell99356928 cell99389696)
                      (ThetaLowerSegment.join cell99422464 cell99455232)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell99488000 cell99520768)
                      (ThetaLowerSegment.join cell99553536 cell99586304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell99619072 cell99651840)
                      (ThetaLowerSegment.join cell99684608 cell99717376))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell99750144 cell99782912)
                      (ThetaLowerSegment.join cell99815680 cell99848448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell99881216 cell99913984)
                      (ThetaLowerSegment.join cell99946752 cell99979520)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell100012288 cell100045056)
                      (ThetaLowerSegment.join cell100077824 cell100110592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell100143360 cell100176128)
                      (ThetaLowerSegment.join cell100208896 cell100241664)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell100274432 cell100307200)
                      (ThetaLowerSegment.join cell100339968 cell100372736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell100405504 cell100438272)
                      (ThetaLowerSegment.join cell100471040 cell100503808)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell100536576 cell100569344)
                      (ThetaLowerSegment.join cell100602112 cell100634880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell100667648 cell100700416)
                      (ThetaLowerSegment.join cell100733184 cell100765952))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell100798720 cell100831488)
                      (ThetaLowerSegment.join cell100864256 cell100897024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell100929792 cell100962560)
                      (ThetaLowerSegment.join cell100995328 cell101028096)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell101060864 cell101093632)
                      (ThetaLowerSegment.join cell101126400 cell101159168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell101191936 cell101224704)
                      (ThetaLowerSegment.join cell101257472 cell101290240)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell101323008 cell101355776)
                      (ThetaLowerSegment.join cell101388544 cell101421312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell101454080 cell101486848)
                      (ThetaLowerSegment.join cell101519616 cell101552384)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell101585152 cell101617920)
                      (ThetaLowerSegment.join cell101650688 cell101683456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell101716224 cell101748992)
                      (ThetaLowerSegment.join cell101781760 cell101814528))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell101847296 cell101880064)
                      (ThetaLowerSegment.join cell101912832 cell101945600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell101978368 cell102011136)
                      (ThetaLowerSegment.join cell102043904 cell102076672)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell102109440 cell102142208)
                      (ThetaLowerSegment.join cell102174976 cell102207744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell102240512 cell102273280)
                      (ThetaLowerSegment.join cell102306048 cell102338816))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell102371584 cell102404352)
                      (ThetaLowerSegment.join cell102437120 cell102469888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell102502656 cell102535424)
                      (ThetaLowerSegment.join cell102568192 cell102600960)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell102633728 cell102666496)
                      (ThetaLowerSegment.join cell102699264 cell102732032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell102764800 cell102797568)
                      (ThetaLowerSegment.join cell102830336 cell102863104))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell102895872 cell102928640)
                      (ThetaLowerSegment.join cell102961408 cell102994176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell103026944 cell103059712)
                      (ThetaLowerSegment.join cell103092480 cell103125248)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell103158016 cell103190784)
                      (ThetaLowerSegment.join cell103223552 cell103256320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell103289088 cell103321856)
                      (ThetaLowerSegment.join cell103354624 cell103387392)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell103420160 cell103452928)
                      (ThetaLowerSegment.join cell103485696 cell103518464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell103551232 cell103584000)
                      (ThetaLowerSegment.join cell103616768 cell103649536)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell103682304 cell103715072)
                      (ThetaLowerSegment.join cell103747840 cell103780608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell103813376 cell103846144)
                      (ThetaLowerSegment.join cell103878912 cell103911680))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell103944448 cell103977216)
                      (ThetaLowerSegment.join cell104009984 cell104042752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell104075520 cell104108288)
                      (ThetaLowerSegment.join cell104141056 cell104173824)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell104206592 cell104239360)
                      (ThetaLowerSegment.join cell104272128 cell104304896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell104337664 cell104370432)
                      (ThetaLowerSegment.join cell104403200 cell104435968)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell104468736 cell104501504)
                  (ThetaLowerSegment.join cell104534272 cell104567040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell104599808 cell104632576)
                  (ThetaLowerSegment.join cell104665344 cell104698112)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell104730880 cell104763648)
                  (ThetaLowerSegment.join cell104796416 cell104829184))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell104861952 cell104894720)
                  (ThetaLowerSegment.join cell104927488 cell104960256))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell104993024 cell105025792)
                  (ThetaLowerSegment.join cell105058560 cell105091328))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell105124096 cell105156864)
                  (ThetaLowerSegment.join cell105189632 cell105222400)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell105255168 cell105287936)
                  (ThetaLowerSegment.join cell105320704 cell105353472))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell105386240 cell105419008)
                  (ThetaLowerSegment.join cell105451776 cell105484544)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell105517312 cell105550080)
                  (ThetaLowerSegment.join cell105582848 cell105615616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell105648384 cell105681152)
                  (ThetaLowerSegment.join cell105713920 cell105746688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell105779456 cell105812224)
                  (ThetaLowerSegment.join cell105844992 cell105877760))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell105910528 cell105943296)
                  (ThetaLowerSegment.join cell105976064 cell106008832))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell106041600 cell106074368)
                  (ThetaLowerSegment.join cell106107136 cell106139904))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell106172672 cell106205440)
                  (ThetaLowerSegment.join cell106238208 cell106270976)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell106303744 cell106336512)
                  (ThetaLowerSegment.join cell106369280 cell106402048))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell106434816 cell106467584)
                  (ThetaLowerSegment.join cell106500352 cell106533120))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell106565888 cell106598656)
                  (ThetaLowerSegment.join cell106631424 cell106664192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell106696960 cell106729728)
                  (ThetaLowerSegment.join cell106762496 cell106795264)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell106828032 cell106860800)
                  (ThetaLowerSegment.join cell106893568 cell106926336))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell106959104 cell106991872)
                  (ThetaLowerSegment.join cell107024640 cell107057408))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell107090176 cell107122944)
                  (ThetaLowerSegment.join cell107155712 cell107188480))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell107221248 cell107254016)
                  (ThetaLowerSegment.join cell107286784 cell107319552)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell107352320 cell107385088)
                  (ThetaLowerSegment.join cell107417856 cell107450624))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell107483392 cell107516160)
                  (ThetaLowerSegment.join cell107548928 cell107581696)))))
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell107614464 cell107647232)
            cell107663616))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
