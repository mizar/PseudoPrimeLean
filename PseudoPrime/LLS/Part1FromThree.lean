/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block20
public import PseudoPrime.LLS.SmallPart1.Block21
public import PseudoPrime.LLS.SmallPart1.Block22
public import PseudoPrime.LLS.SmallPart1.Block23
public import PseudoPrime.LLS.Part1ThreeFourBounds

/-! # Original LLS Part 1 extended from q >= 3000 to q >= 3 -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Input: a block index. Output: its exact product code array.
Role: keep the finite catalog split into small source modules. -/
def part1CodeBlock (b : Fin 24) : Array ℕ :=
  match b.val with
  | 0 => block00Codes
  | 1 => block01Codes
  | 2 => block02Codes
  | 3 => block03Codes
  | 4 => block04Codes
  | 5 => block05Codes
  | 6 => block06Codes
  | 7 => block07Codes
  | 8 => block08Codes
  | 9 => block09Codes
  | 10 => block10Codes
  | 11 => block11Codes
  | 12 => block12Codes
  | 13 => block13Codes
  | 14 => block14Codes
  | 15 => block15Codes
  | 16 => block16Codes
  | 17 => block17Codes
  | 18 => block18Codes
  | 19 => block19Codes
  | 20 => block20Codes
  | 21 => block21Codes
  | 22 => block22Codes
  | _ => block23Codes

/-- Input: block and window indices. Claim: all supported finite checks pass.
Proof: use the independently kernel-checked block windows. Role: certify the full catalog. -/
theorem part1_catalog_checks (b : Fin 24) (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf (5 + 128 * b.val) (part1CodeBlock b)) 4
        (16 * j.val) =
      true := by
  fin_cases b
  · exact block00_check j
  · exact block01_check j
  · exact block02_check j
  · exact block03_check j
  · exact block04_check j
  · exact block05_check j
  · exact block06_check j
  · exact block07_check j
  · exact block08_check j
  · exact block09_check j
  · exact block10_check j
  · exact block11_check j
  · exact block12_check j
  · exact block13_check j
  · exact block14_check j
  · exact block15_check j
  · exact block16_check j
  · exact block17_check j
  · exact block18_check j
  · exact block19_check j
  · exact block20_check j
  · exact block21_check j
  · exact block22_check j
  · exact block23_check j

end PseudoPrime.LLS.SmallPart1

namespace PseudoPrime.LLS

/-- Input: 5 <= q < 3000 and a proper unit subgroup.
Claim: an outside prime lies within the original LLS Part 1 radius, without GRH.
Proof: apply finite product generation and the certified integer-cap comparisons.
Role: discharge the remaining finite range for the entrance from three. -/
theorem exists_prime_outside_lls_part1_finite {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hQ : q < 3000)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  exact
    exists_prime_outside_lls_part1_of_catalog SmallPart1.part1CodeBlock
      SmallPart1.part1_catalog_checks hq hQ H hH

/-- Input: GRH, q >= 3 and a proper unit subgroup.
Claim: the original LLS Part 1 conclusion with its unchanged correction formula.
Proof: combine the full finite range with the established analytic theorem above 3000.
Role: expose the improved entrance as a separate theorem from the paper statement. -/
theorem llsTheorem11S1_from_three_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        ∃ u : (ZMod q)ˣ,
          u ∉ H ∧
            (u : ZMod q) = (p : ZMod q) ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  obtain ⟨p, hp, hb⟩ :=
    lls_part1_from_three_of_finite_range hGRH
      (fun q _ hq hQ H hH ↦ exists_prime_outside_lls_part1_finite hq hQ H hH) q hq H hH
  obtain ⟨hp, hd, u, hu, heq⟩ := hp
  exact ⟨p, hp, hd, u, hu, heq, hb⟩

end PseudoPrime.LLS
