/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleLowNumerics

/-! # Rational cells for the low triple bridge -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A low-bridge interval with its even radius and correction, all rational.
The endpoints define a closed logarithmic cell; the radius and correction
supply the local shifted witness throughout that cell. -/
structure LowBridgeCell where
  lo : ℚ
  hi : ℚ
  radius : ℚ
  correction : ℚ

/-- Check the radius, correction and endpoint budget for a low-bridge cell.
The additional rational margin turns the correction lower bound into a strict
inequality. Every accepted cell supports the uniform triple witness bound. -/
def LowBridgeCell.check (c : LowBridgeCell) : Bool :=
  localCorrectionCheck c.radius (c.correction + 1 / 1000000) 5 &&
    decide
      (c.radius ≤ (10954451 / 20000000 : ℚ) * c.lo ∧
        (2 / 3 - 10954451 / 20000000 : ℚ) * c.hi ≤ c.correction + 54753 / 30000000)

/-- The low-bridge rational cells in block 0, ordered by their endpoints. -/
def lowBridgeCells0 : List LowBridgeCell :=
  [⟨197 / 5, 19701 / 500, 2158026847 / 100000000, 4694939 / 1000000⟩,
    ⟨19701 / 500, 9851 / 250, 215813639151 / 10000000000, 4695009 / 1000000⟩,
    ⟨9851 / 250, 19703 / 500, 107912296801 / 5000000000, 4695069 / 1000000⟩,
    ⟨19703 / 500, 4926 / 125, 215835548053 / 10000000000, 4695139 / 1000000⟩,
    ⟨4926 / 125, 3941 / 100, 26980812813 / 1250000000, 4695209 / 1000000⟩,
    ⟨3941 / 100, 9853 / 250, 43171491391 / 2000000000, 4695279 / 1000000⟩,
    ⟨9853 / 250, 19707 / 500, 107934205703 / 5000000000, 4695349 / 1000000⟩,
    ⟨19707 / 500, 4927 / 125, 215879365857 / 10000000000, 4695419 / 1000000⟩,
    ⟨4927 / 125, 19709 / 500, 53972580077 / 2500000000, 4695489 / 1000000⟩,
    ⟨19709 / 500, 1971 / 50, 215901274759 / 10000000000, 4695559 / 1000000⟩]

set_option maxRecDepth 8192 in
/-- Every cell in block 0 passes the rational correction and budget checks.
Kernel reduction verifies the finite arithmetic input to the covering theorem. -/
theorem lowBridgeCells0_checked : lowBridgeCells0.all LowBridgeCell.check = true := by
  decide +kernel

/-- The low-bridge rational cells in block 1, ordered by their endpoints. -/
def lowBridgeCells1 : List LowBridgeCell :=
  [⟨1971 / 50, 19711 / 500, 21591222921 / 1000000000, 4695629 / 1000000⟩,
    ⟨19711 / 500, 4928 / 125, 215923183661 / 10000000000, 4695699 / 1000000⟩,
    ⟨4928 / 125, 19713 / 500, 843492727 / 39062500, 4695769 / 1000000⟩,
    ⟨19713 / 500, 9857 / 250, 215945092563 / 10000000000, 4695829 / 1000000⟩,
    ⟨9857 / 250, 3943 / 100, 107978023507 / 5000000000, 4695899 / 1000000⟩,
    ⟨3943 / 100, 4929 / 125, 43193400293 / 2000000000, 4695969 / 1000000⟩,
    ⟨4929 / 125, 19717 / 500, 53994488979 / 2500000000, 4696039 / 1000000⟩,
    ⟨19717 / 500, 9859 / 250, 215988910367 / 10000000000, 4696109 / 1000000⟩,
    ⟨9859 / 250, 19719 / 500, 107999932409 / 5000000000, 4696179 / 1000000⟩,
    ⟨19719 / 500, 986 / 25, 216010819269 / 10000000000, 4696249 / 1000000⟩]

set_option maxRecDepth 8192 in
/-- Every cell in block 1 passes the rational correction and budget checks.
Kernel reduction verifies the finite arithmetic input to the covering theorem. -/
theorem lowBridgeCells1_checked : lowBridgeCells1.all LowBridgeCell.check = true := by
  decide +kernel

/-- The low-bridge rational cells in block 2, ordered by their endpoints. -/
def lowBridgeCells2 : List LowBridgeCell :=
  [⟨986 / 25, 19721 / 500, 5400544343 / 250000000, 4696319 / 1000000⟩,
    ⟨19721 / 500, 9861 / 250, 216032728171 / 10000000000, 4696389 / 1000000⟩,
    ⟨9861 / 250, 19723 / 500, 108021841311 / 5000000000, 4696459 / 1000000⟩,
    ⟨19723 / 500, 4931 / 125, 216054637073 / 10000000000, 4696519 / 1000000⟩,
    ⟨4931 / 125, 789 / 20, 54016397881 / 2500000000, 4696589 / 1000000⟩,
    ⟨789 / 20, 9863 / 250, 8643061839 / 400000000, 4696659 / 1000000⟩,
    ⟨9863 / 250, 19727 / 500, 108043750213 / 5000000000, 4696729 / 1000000⟩,
    ⟨19727 / 500, 4932 / 125, 216098454877 / 10000000000, 4696799 / 1000000⟩,
    ⟨4932 / 125, 19729 / 500, 13506838083 / 625000000, 4696869 / 1000000⟩,
    ⟨19729 / 500, 1973 / 50, 216120363779 / 10000000000, 4696939 / 1000000⟩]

set_option maxRecDepth 8192 in
/-- Every cell in block 2 passes the rational correction and budget checks.
Kernel reduction verifies the finite arithmetic input to the covering theorem. -/
theorem lowBridgeCells2_checked : lowBridgeCells2.all LowBridgeCell.check = true := by
  decide +kernel

/-- The low-bridge rational cells in block 3, ordered by their endpoints. -/
def lowBridgeCells3 : List LowBridgeCell :=
  [⟨1973 / 50, 19731 / 500, 21613131823 / 1000000000, 4697009 / 1000000⟩,
    ⟨19731 / 500, 4933 / 125, 216142272681 / 10000000000, 4697079 / 1000000⟩,
    ⟨4933 / 125, 19733 / 500, 54038306783 / 2500000000, 4697149 / 1000000⟩,
    ⟨19733 / 500, 9867 / 250, 216164181583 / 10000000000, 4697209 / 1000000⟩,
    ⟨9867 / 250, 3947 / 100, 108087568017 / 5000000000, 4697279 / 1000000⟩,
    ⟨3947 / 100, 4934 / 125, 43237218097 / 2000000000, 4697349 / 1000000⟩,
    ⟨4934 / 125, 19737 / 500, 27024630617 / 1250000000, 4697419 / 1000000⟩,
    ⟨19737 / 500, 9869 / 250, 216207999387 / 10000000000, 4697489 / 1000000⟩,
    ⟨9869 / 250, 19739 / 500, 108109476919 / 5000000000, 4697559 / 1000000⟩,
    ⟨19739 / 500, 987 / 25, 216229908289 / 10000000000, 4697629 / 1000000⟩]

set_option maxRecDepth 8192 in
/-- Every cell in block 3 passes the rational correction and budget checks.
Kernel reduction verifies the finite arithmetic input to the covering theorem. -/
theorem lowBridgeCells3_checked : lowBridgeCells3.all LowBridgeCell.check = true := by
  decide +kernel

/-- The low-bridge rational cells in block 4, ordered by their endpoints. -/
def lowBridgeCells4 : List LowBridgeCell :=
  [⟨987 / 25, 19741 / 500, 10812043137 / 500000000, 4697699 / 1000000⟩,
    ⟨19741 / 500, 9871 / 250, 216251817191 / 10000000000, 4697769 / 1000000⟩,
    ⟨9871 / 250, 19743 / 500, 108131385821 / 5000000000, 4697839 / 1000000⟩,
    ⟨19743 / 500, 4936 / 125, 216273726093 / 10000000000, 4697899 / 1000000⟩,
    ⟨4936 / 125, 3949 / 100, 6758896267 / 312500000, 4697969 / 1000000⟩,
    ⟨3949 / 100, 9873 / 250, 43259126999 / 2000000000, 4698039 / 1000000⟩,
    ⟨9873 / 250, 19747 / 500, 108153294723 / 5000000000, 4698109 / 1000000⟩,
    ⟨19747 / 500, 4937 / 125, 216317543897 / 10000000000, 4698179 / 1000000⟩,
    ⟨4937 / 125, 19749 / 500, 54082124587 / 2500000000, 4698249 / 1000000⟩,
    ⟨19749 / 500, 79 / 2, 216339452799 / 10000000000, 4698319 / 1000000⟩]

set_option maxRecDepth 8192 in
/-- Every cell in block 4 passes the rational correction and budget checks.
Kernel reduction verifies the finite arithmetic input to the covering theorem. -/
theorem lowBridgeCells4_checked : lowBridgeCells4.all LowBridgeCell.check = true := by
  decide +kernel

/-- The low-bridge rational cells in block 5, ordered by their endpoints. -/
def lowBridgeCells5 : List LowBridgeCell :=
  [⟨79 / 2, 19751 / 500, 865401629 / 40000000, 4698389 / 1000000⟩,
    ⟨19751 / 500, 4938 / 125, 216361361701 / 10000000000, 4698459 / 1000000⟩,
    ⟨4938 / 125, 19753 / 500, 27046539519 / 1250000000, 4698529 / 1000000⟩,
    ⟨19753 / 500, 9877 / 250, 216383270603 / 10000000000, 4698589 / 1000000⟩,
    ⟨9877 / 250, 3951 / 100, 108197112527 / 5000000000, 4698659 / 1000000⟩,
    ⟨3951 / 100, 4939 / 125, 43281035901 / 2000000000, 4698729 / 1000000⟩,
    ⟨4939 / 125, 19757 / 500, 54104033489 / 2500000000, 4698799 / 1000000⟩,
    ⟨19757 / 500, 9879 / 250, 216427088407 / 10000000000, 4698869 / 1000000⟩,
    ⟨9879 / 250, 19759 / 500, 108219021429 / 5000000000, 4698939 / 1000000⟩,
    ⟨19759 / 500, 988 / 25, 216448997309 / 10000000000, 4699009 / 1000000⟩]

set_option maxRecDepth 8192 in
/-- Every cell in block 5 passes the rational correction and budget checks.
Kernel reduction verifies the finite arithmetic input to the covering theorem. -/
theorem lowBridgeCells5_checked : lowBridgeCells5.all LowBridgeCell.check = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
