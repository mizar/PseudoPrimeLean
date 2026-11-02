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

/-- Exact product codes for the 128 positions starting at 1669.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes13 : Array ℕ :=
  #[106754, 36983555, 36997890, 2612097061039117955, 37008003, 101979787, 36480258, 36464771,
    9552109769986, 53643, 37012997, 713079987039861715763979, 104967, 51971, 9689480313861,
    34367767, 67654675, 34883083, 101465101, 9552042144899, 36473986, 68953859, 34129411,
    9689481618053, 108290, 36983429, 9277196999697, 9139760404995, 108547, 36456069, 108675,
    10101833077763, 101984386, 35414789, 34915074, 2720183864412868999, 9689614520067, 54539,
    34115083, 9139791859473, 109315, 9552109766925, 34392834, 9689481098499, 34115205, 54787,
    34378498, 2720184139290775303, 67658755, 54915, 35425922, 2540039741879620867, 110083,
    9964358999563, 110211, 34368391, 9689481623298, 55173, 34128645, 9689481618437, 27144294762754,
    70003459, 34115589, 34368517, 110850, 35406853, 34385154, 2540039329630914435, 101199877,
    35414403, 34918146, 2648126270410065671, 111362, 101458183, 9552042147202, 9139760405251,
    67917570, 102504453, 111746, 9277164237187, 9964359008514, 38554371, 35441669,
    2540039741879620101, 112135, 56069, 9277335144706, 34368907, 34126723, 35408133, 112519,
    2612097473390053891, 36999810, 56323, 34132493, 9552111340165, 67655683, 56459, 9552109246082,
    2504010670015777795, 67922178, 9689482665223, 9139724767874, 34893443, 36999938, 56709,
    169616130, 2540039467036313861, 113669, 104079235, 34116613, 9552078837251, 67659267, 35406725,
    114059, 10101797959555, 2648126270407707659, 34891651, 114306, 9277164233995, 114451, 35412227,
    103559554, 9552042143747, 34392706, 9964359000327, 35435266, 35418115]

/-- Exact divisor codes for the 128 positions starting at 1669.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes13 : Array ℕ :=
  #[1669, 284348847398914, 1146789891, 492911923208194, 1641971719, 422750410153986, 2693173253,
    1128701954, 422955496153091, 646881282, 2693951511, 73803372303500091394, 24617, 3225067522,
    492877563469827, 1128964098, 1654820869, 215939144916994, 1642233863, 1638309890, 1147576323,
    563178124255234, 2696048659, 423025288060930, 1693, 563143227908098, 283421134462979,
    2691342338, 1697, 215973504655362, 1699, 492878099554306, 4295925763, 422851881377794,
    2164686861, 353068860743682, 422749337456645, 648716290, 1148362755, 352895988834306, 1709,
    64607021864409538562, 2692112413, 2161549314, 1148624899, 649240578, 4295921669,
    73816812836717240322, 2697621521, 649502722, 2172559363, 422956031975426, 1721,
    55433119089071398914, 1723, 1130274818, 492981178769411, 650027010, 2168094731, 5369143298,
    492911923462151, 284451926614018, 1149411331, 1130536962, 1733, 492878636163074, 1656131589,
    422749336936450, 2172821507, 353205227003906, 3227410469, 55406167825691615234, 1741,
    352999068835842, 353273945956355, 2161811458, 1656393733, 353515537342466, 1747,
    492980106862594, 423127294582787, 563075045040130, 2697883665, 353103220482050, 1753, 651862018,
    563178124255235, 1131323394, 1643544583, 216145303347202, 1759, 563143764516866, 1150722051,
    652386306, 3226886185, 563075581648898, 1656918021, 652648450, 422748801638403, 492877563731970,
    2692374557, 46250349783247396866, 492980642676743, 1131847682, 2173345795, 653172738,
    2693697541, 422853489369090, 1777, 283661116022786, 1151508483, 353377561780226, 2165473293,
    563144301125634, 1783, 1639882754, 64602447929861120003, 423023679545346, 1787, 284040146362370,
    1789, 284555005829122, 2173607939, 4295925762, 2168881163, 64615958832359055362, 1657704453,
    1132634114]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product13_window0 :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product13_window1 :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product13_window2 :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product13_window3 :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product13_window4 :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product13_window5 :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product13_window6 :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product13_window7 :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product13_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 1669 part1ProductCodes13 part1DivisorCodes13) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product13_window0
  | ⟨1, _⟩ => part1Product13_window1
  | ⟨2, _⟩ => part1Product13_window2
  | ⟨3, _⟩ => part1Product13_window3
  | ⟨4, _⟩ => part1Product13_window4
  | ⟨5, _⟩ => part1Product13_window5
  | ⟨6, _⟩ => part1Product13_window6
  | ⟨7, _⟩ => part1Product13_window7

end PseudoPrime.LLS
