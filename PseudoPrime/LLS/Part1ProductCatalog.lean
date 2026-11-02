/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductBlock00
public import PseudoPrime.LLS.Part1ProductBlock01
public import PseudoPrime.LLS.Part1ProductBlock02
public import PseudoPrime.LLS.Part1ProductBlock03
public import PseudoPrime.LLS.Part1ProductBlock04
public import PseudoPrime.LLS.Part1ProductBlock05
public import PseudoPrime.LLS.Part1ProductBlock06
public import PseudoPrime.LLS.Part1ProductBlock07
public import PseudoPrime.LLS.Part1ProductBlock08
public import PseudoPrime.LLS.Part1ProductBlock09
public import PseudoPrime.LLS.Part1ProductBlock10
public import PseudoPrime.LLS.Part1ProductBlock11
public import PseudoPrime.LLS.Part1ProductBlock12
public import PseudoPrime.LLS.Part1ProductBlock13
public import PseudoPrime.LLS.Part1ProductBlock14
public import PseudoPrime.LLS.Part1ProductBlock15
public import PseudoPrime.LLS.Part1ProductBlock16
public import PseudoPrime.LLS.Part1ProductBlock17
public import PseudoPrime.LLS.Part1ProductBlock18
public import PseudoPrime.LLS.Part1ProductBlock19
public import PseudoPrime.LLS.Part1ProductBlock20
public import PseudoPrime.LLS.Part1ProductBlock21
public import PseudoPrime.LLS.Part1ProductBlock22
public import PseudoPrime.LLS.Part1ProductBlock23

/-! # Independent finite LLS Part 1 product catalog

This module selects product and divisor arrays and their checked windows from twenty-four
independent blocks. It imports no soundness or analytic transfer. Individual blocks must not
import this assembly: changes to selection or consumers must not invalidate other blocks.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Select the product code array of a finite certificate block.
Input: one of twenty-four block indices. Output: the corresponding 128-entry array.
Definition: exhaustive selection by block index. Role: the finite extraction interface. -/
def part1ProductCodeBlock (b : Fin 24) : Array ℕ :=
  match b with
  | ⟨0, _⟩ => part1ProductCodes00
  | ⟨1, _⟩ => part1ProductCodes01
  | ⟨2, _⟩ => part1ProductCodes02
  | ⟨3, _⟩ => part1ProductCodes03
  | ⟨4, _⟩ => part1ProductCodes04
  | ⟨5, _⟩ => part1ProductCodes05
  | ⟨6, _⟩ => part1ProductCodes06
  | ⟨7, _⟩ => part1ProductCodes07
  | ⟨8, _⟩ => part1ProductCodes08
  | ⟨9, _⟩ => part1ProductCodes09
  | ⟨10, _⟩ => part1ProductCodes10
  | ⟨11, _⟩ => part1ProductCodes11
  | ⟨12, _⟩ => part1ProductCodes12
  | ⟨13, _⟩ => part1ProductCodes13
  | ⟨14, _⟩ => part1ProductCodes14
  | ⟨15, _⟩ => part1ProductCodes15
  | ⟨16, _⟩ => part1ProductCodes16
  | ⟨17, _⟩ => part1ProductCodes17
  | ⟨18, _⟩ => part1ProductCodes18
  | ⟨19, _⟩ => part1ProductCodes19
  | ⟨20, _⟩ => part1ProductCodes20
  | ⟨21, _⟩ => part1ProductCodes21
  | ⟨22, _⟩ => part1ProductCodes22
  | ⟨23, _⟩ => part1ProductCodes23
  | ⟨n + 24, h⟩ => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 24 n) h)

/-- Select the divisor code array of a finite certificate block.
Input: one of twenty-four block indices. Output: the corresponding 128-entry array.
Definition: exhaustive selection by block index. Role: the finite extraction interface. -/
def part1DivisorCodeBlock (b : Fin 24) : Array ℕ :=
  match b with
  | ⟨0, _⟩ => part1DivisorCodes00
  | ⟨1, _⟩ => part1DivisorCodes01
  | ⟨2, _⟩ => part1DivisorCodes02
  | ⟨3, _⟩ => part1DivisorCodes03
  | ⟨4, _⟩ => part1DivisorCodes04
  | ⟨5, _⟩ => part1DivisorCodes05
  | ⟨6, _⟩ => part1DivisorCodes06
  | ⟨7, _⟩ => part1DivisorCodes07
  | ⟨8, _⟩ => part1DivisorCodes08
  | ⟨9, _⟩ => part1DivisorCodes09
  | ⟨10, _⟩ => part1DivisorCodes10
  | ⟨11, _⟩ => part1DivisorCodes11
  | ⟨12, _⟩ => part1DivisorCodes12
  | ⟨13, _⟩ => part1DivisorCodes13
  | ⟨14, _⟩ => part1DivisorCodes14
  | ⟨15, _⟩ => part1DivisorCodes15
  | ⟨16, _⟩ => part1DivisorCodes16
  | ⟨17, _⟩ => part1DivisorCodes17
  | ⟨18, _⟩ => part1DivisorCodes18
  | ⟨19, _⟩ => part1DivisorCodes19
  | ⟨20, _⟩ => part1DivisorCodes20
  | ⟨21, _⟩ => part1DivisorCodes21
  | ⟨22, _⟩ => part1DivisorCodes22
  | ⟨23, _⟩ => part1DivisorCodes23
  | ⟨n + 24, h⟩ => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 24 n) h)

/-- Every selected catalog window passes the executable coverage check.
Input: block and window indices. Claim: all sixteen positions in that window pass.
Proof: select the independent block certificate. Role: abstract finite-range extraction. -/
theorem part1ProductCatalog_checks (b : Fin 24) (j : Fin 8) :
    unitGenerationAll
        (part1ProductLeaf (5 + 128 * b.val) (part1ProductCodeBlock b) (part1DivisorCodeBlock b)) 4
        (16 * j.val) =
      true :=
  match b with
  | ⟨0, _⟩ => part1Product00_checks j
  | ⟨1, _⟩ => part1Product01_checks j
  | ⟨2, _⟩ => part1Product02_checks j
  | ⟨3, _⟩ => part1Product03_checks j
  | ⟨4, _⟩ => part1Product04_checks j
  | ⟨5, _⟩ => part1Product05_checks j
  | ⟨6, _⟩ => part1Product06_checks j
  | ⟨7, _⟩ => part1Product07_checks j
  | ⟨8, _⟩ => part1Product08_checks j
  | ⟨9, _⟩ => part1Product09_checks j
  | ⟨10, _⟩ => part1Product10_checks j
  | ⟨11, _⟩ => part1Product11_checks j
  | ⟨12, _⟩ => part1Product12_checks j
  | ⟨13, _⟩ => part1Product13_checks j
  | ⟨14, _⟩ => part1Product14_checks j
  | ⟨15, _⟩ => part1Product15_checks j
  | ⟨16, _⟩ => part1Product16_checks j
  | ⟨17, _⟩ => part1Product17_checks j
  | ⟨18, _⟩ => part1Product18_checks j
  | ⟨19, _⟩ => part1Product19_checks j
  | ⟨20, _⟩ => part1Product20_checks j
  | ⟨21, _⟩ => part1Product21_checks j
  | ⟨22, _⟩ => part1Product22_checks j
  | ⟨23, _⟩ => part1Product23_checks j
  | ⟨n + 24, h⟩ => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 24 n) h)

end PseudoPrime.LLS
