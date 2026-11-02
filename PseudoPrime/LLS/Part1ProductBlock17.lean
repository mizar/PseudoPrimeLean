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

/-- Exact product codes for the 128 positions starting at 2181.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes17 : Array ℕ :=
  #[34125189, 69777, 34931970, 750859099046804005323525, 9552042681090, 69893, 93314, 34375813,
    34404226, 9964393075211, 101469713, 9139760407043, 9277163459589, 70147, 34396941,
    9964426104583, 129794, 101459717, 34125575, 2612097473490715907, 169620611, 38558603, 140933,
    9552042671875, 9689549772034, 70533, 141189, 2540039741879621125, 138373, 18348169235459,
    9277164245634, 9139793957763, 141570, 34888199, 34397442, 9277163717893, 34125959, 70915,
    34401538, 2612097335952673031, 142082, 169613571, 27968929007874, 9277164242179, 67661315,
    9689482667781, 34145283, 34900739, 34912642, 35417859, 36505605, 2540039329630914439,
    9139724773634, 71441, 9689515173122, 9277230814469, 143106, 38034693, 143235,
    2648126270410066947, 36485250, 36471427, 143490, 2648126270375465989, 67661827, 71811,
    9552042151810, 9277164242435, 67928322, 36457229, 144007, 34901123, 35437442, 34894723,
    9277465430531, 2720183864413394693, 202648834, 72203, 34913163, 9552076217347, 9552108463107,
    9139760403719, 101472779, 9552042149507, 9552041364231, 35422085, 145026, 9552111340933, 145154,
    36991235, 36486402, 9277164242435, 145411, 34889351, 9552209383170, 35425795, 9689481106050,
    36996103, 35459331, 713079951010652344813837, 145927, 106702979, 34127367, 36474499, 67662349,
    101982087, 146323, 2648125858091634435, 9964428204811, 68958467, 34410754, 10376676388753,
    146690, 101461261, 9689513862151, 2540039329561714187, 146949, 36986757, 34404226,
    9552042669827, 9277164246786, 73617, 34926979, 9689481621509, 70021890, 73733, 34127883,
    34377733]

/-- Exact divisor codes for the 128 positions starting at 2181.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes17 : Array ℕ :=
  #[1169072131, 679915522, 3228983333, 73816883136741945346, 492980106858501, 680177666, 40963,
    1145483266, 2173599755, 46281874980638994434, 1651675143, 2165485570, 422955496677379,
    680701954, 1668190213, 423265806233602, 32781, 284177048973314, 1169858563, 563143764520962,
    2693689375, 217416613670914, 2203, 493083186081794, 633443789217795, 681488386, 2207,
    492981715382274, 24623, 73825820069795115010, 423367812751363, 353205763354626, 2213,
    422922208849922, 1668714501, 1646964738, 1170644995, 682274818, 1652199431,
    55424182224201101314, 2221, 353583184130050, 492911923470339, 2165747714, 2696056837,
    55460211055579803650, 2701557777, 1146793986, 1171169283, 285310920077314, 2697097239,
    493119154335746, 493083721895943, 683323394, 284039609753603, 422955496157186, 2237,
    217519692886018, 2239, 633443789221890, 2695274499, 423229837979650, 2243, 73825820035971985410,
    1669500933, 684109826, 353686799687683, 1647489026, 2170191885, 633409966092290, 2251,
    1147580418, 1172217859, 492981179035650, 422921136148485, 423025288065026, 3229245477,
    684896258, 2180423683, 353789878644738, 492911923990535, 64629469631241170946, 2693951519,
    1647751170, 284073969491971, 353617543868418, 2267, 633444325830658, 2269, 285379639554050,
    1173004291, 2693705730, 2273, 217622772101122, 563178124513285, 1148366850, 492980642684931,
    423367813541890, 3228196907, 64607021864409542658, 2281, 284280128188418, 1173528579,
    1148628994, 1670549509, 354030933422082, 2287, 563177588174850, 353721159426051,
    285413999292418, 2694737949, 284761700872194, 2293, 422851882430466, 563246843731971,
    422921672503298, 2297, 217691491577858, 3760619531, 492981178773506, 423230374060035, 687779842,
    3227422727, 5369147394, 1671073797, 688041986, 1174577155, 1149415426]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product17_window0 :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product17_window1 :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product17_window2 :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product17_window3 :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product17_window4 :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product17_window5 :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product17_window6 :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product17_window7 :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product17_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 2181 part1ProductCodes17 part1DivisorCodes17) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product17_window0
  | ⟨1, _⟩ => part1Product17_window1
  | ⟨2, _⟩ => part1Product17_window2
  | ⟨3, _⟩ => part1Product17_window3
  | ⟨4, _⟩ => part1Product17_window4
  | ⟨5, _⟩ => part1Product17_window5
  | ⟨6, _⟩ => part1Product17_window6
  | ⟨7, _⟩ => part1Product17_window7

end PseudoPrime.LLS
