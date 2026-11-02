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

/-- Exact product codes for the 128 positions starting at 2437.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes19 : Array ℕ :=
  #[155906, 34901763, 104088450, 2648126132969017095, 156171, 9689481620741, 101996290,
    9139724764423, 9552042676482, 78213, 156549, 2540039741913172997, 102523267, 38562051,
    9277231341442, 34380037, 34149763, 34891293, 34403586, 9552041626757, 27556612147458, 78595,
    157314, 2612097473391102471, 34939778, 78723, 34917634, 2612097473355980291, 18073290021891,
    36464133, 157826, 34904579, 34917762, 9552210430211, 38078467, 2612097473356503429, 158213,
    79109, 10101932691202, 34380423, 158466, 10101799529349, 101475074, 2612097335951101699,
    35442306, 135013381, 35462402, 9552042668421, 9552041634050, 35425283, 34918146, 9552042151299,
    34415746, 9689482668295, 34941698, 9552042148355, 106710274, 236197123, 36501767,
    2612096923634240523, 34937474, 79879, 9552041366533, 36470019, 336338439, 105128581, 160131,
    9139724766737, 9689481630466, 36472195, 34154763, 2612097473356502661, 201863173, 36470019,
    103564162, 9689514649347, 37031043, 36464773, 38075138, 9689514648579, 36491650, 80523,
    38083847, 713079987039861748794125, 161297, 204216325, 34917122, 37002627, 338434306, 34892055,
    101471618, 9552042151427, 34132491, 9689481623299, 161922, 9552042144903, 67671043, 101461271,
    9277199361794, 9552042151683, 34156675, 36988805, 162434, 9689482673923, 9964359012994,
    169614851, 162693, 2540039467036314885, 71597826, 102510979, 103564930, 9964425581829, 163074,
    9689515168779, 163219, 2540039467001193219, 9552042156802, 81667, 8933734093323, 9689481098375,
    163586, 81795, 35443970, 9552076218371, 67932930, 9139793956625, 34152963, 35430403]

/-- Exact divisor codes for the 128 positions starting at 2437.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes19 : Array ℕ :=
  #[2437, 423126759288834, 2183045123, 423265269624834, 2441, 64647483995390914562, 1656393735,
    423024215633922, 284280127922179, 697217026, 2447, 563247380344834, 2694737951, 633443789221890,
    422955496939523, 1154134018, 2176745483, 218138168176642, 1675005957, 1650896898,
    563178124517379, 698003458, 2459, 55433189423455842306, 2698407959, 698265602, 1181392899,
    563143764783106, 493083722682373, 354202732113922, 2467, 1154658306, 1181655043,
    73830323669422485506, 1656918023, 353618616561666, 2473, 699052034, 563143764516867, 1154920450,
    2477, 55473721854461915138, 3230036005, 493118617726978, 1182179331, 423470892756994,
    2172551181, 492981715382274, 423437068570629, 353789342560258, 1182441475, 1651421186,
    2701557779, 46304392978775846914, 3228196911, 353377562046466, 2183831555, 422954961383426,
    1676054533, 563178660868098, 2177269771, 700624898, 563246843994115, 4832538626, 3229245481,
    354237091852290, 2503, 1651683330, 284348847398915, 284555006095362, 2698670103,
    73830323635599355906, 2172813325, 285791956414466, 3762200579, 2168107010, 1657704455,
    218309966868482, 1676578821, 493221161644034, 1183752195, 701935618, 2177531915,
    83026744340354871298, 2521, 353514464915458, 3761938435, 1156493314, 2697629701,
    218344326606850, 4297494535, 2694754306, 2184355843, 64615958797462712322, 2531,
    285105298255874, 2703917073, 284589365833730, 563178124255235, 1652207618, 3228983339,
    423025288065026, 2539, 354030396813314, 563143764779011, 422920601907202, 2543, 423128367280130,
    1677365253, 423367813804034, 2184617987, 563178124521474, 2549, 73825890301636947970, 2551,
    493083721904130, 493220625555459, 704294914, 423471428308997, 423437604925442, 2557, 704557058,
    1185587203, 4832538626, 2173337613, 55478225454089285634, 2178056203, 1157804034]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product19_window0 :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product19_window1 :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product19_window2 :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product19_window3 :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product19_window4 :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product19_window5 :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product19_window6 :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product19_window7 :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product19_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 2437 part1ProductCodes19 part1DivisorCodes19) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product19_window0
  | ⟨1, _⟩ => part1Product19_window1
  | ⟨2, _⟩ => part1Product19_window2
  | ⟨3, _⟩ => part1Product19_window3
  | ⟨4, _⟩ => part1Product19_window4
  | ⟨5, _⟩ => part1Product19_window5
  | ⟨6, _⟩ => part1Product19_window6
  | ⟨7, _⟩ => part1Product19_window7

end PseudoPrime.LLS
