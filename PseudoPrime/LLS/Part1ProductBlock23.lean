/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCheck

/-! # Independent finite LLS Part 1 coverage certificates

This block checks 128 positions using compact product and divisor codes. Each sixteen-position
window is checked in the kernel; positions at or above 3000 are padding. Integer data is
untrusted until these checks succeed. Blocks depend only on the computational entry and not on
one another, the catalog, soundness proofs, or analytic bounds.

Keep unrelated declarations and imports out of this file. Changing a computational dependency
can invalidate these expensive proofs even when the certificate arrays are unchanged.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Exact product codes for the 128 positions starting at 2949.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes23 : Array ℕ :=
  #[34928002, 36475139, 35476226, 2648126270374944263, 188941, 101987459, 9689515176194, 36485251,
    189186, 9277199358981, 34426626, 2504019878426183939, 9552109249154, 94723, 189570,
    2828270118098438405, 67671043, 94851, 9277163467653, 2540039741879101187, 189955,
    10101801102599, 190091, 34912643, 35452802, 95109, 9552074914819, 2540039467001191947,
    202651906, 95261, 102519429, 9552076219651, 171197314, 9964359005323, 101479682, 9277163724037,
    9552042681090, 95491, 34432258, 9552042671493, 101476610, 9964393079043, 34142471,
    2720183314691134467, 135027205, 35421317, 35465986, 9552042151811, 304880386, 95883, 191889, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Exact divisor codes for the 128 positions starting at 2949.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes23 : Array ℕ :=
  #[1202626563, 423231446757378, 2177269773, 493290953027586, 2953, 285104761909250,
    284864780345347, 1170649090, 2957, 64629469699960647682, 2182778891, 493222233812994,
    423024751714307, 731033602, 2963, 73830323669959094274, 1688379397, 731295746, 493324241641475,
    423127830933506, 2969, 83035821908353789954, 2971, 1171173378, 1203675139, 731820034,
    563246843994117, 493119154335746, 2177531917, 732082178, 2190909443, 354408890806274,
    2183041035, 55500743452226138114, 2704965651, 1659547650, 284899140083715, 732606466,
    2697883677, 423643763355650, 3229257735, 73839330869214097410, 1204461571, 563246844522498,
    3230822441, 219684356403202, 1689165829, 353686799691778, 3762987011, 733392898, 2999, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product23_window0 :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product23_window1 :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product23_window2 :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product23_window3 :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product23_window4 :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product23_window5 :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product23_window6 :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product23_window7 :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product23_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 2949 part1ProductCodes23 part1DivisorCodes23) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product23_window0
  | ⟨1, _⟩ => part1Product23_window1
  | ⟨2, _⟩ => part1Product23_window2
  | ⟨3, _⟩ => part1Product23_window3
  | ⟨4, _⟩ => part1Product23_window4
  | ⟨5, _⟩ => part1Product23_window5
  | ⟨6, _⟩ => part1Product23_window6
  | ⟨7, _⟩ => part1Product23_window7

end PseudoPrime.LLS
