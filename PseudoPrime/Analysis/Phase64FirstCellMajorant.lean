/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64AdaptiveCellBounds
public import PseudoPrime.Analysis.Phase64AdaptiveCell.Block12
public import PseudoPrime.Analysis.Phase64AdaptiveCell.Block13
public import PseudoPrime.Analysis.Phase64AdaptiveCell.Block14
public import PseudoPrime.Analysis.Phase64AdaptiveCell.Block15

/-! # Complete Gamma phase majorant on the first continuous level cell -/

@[expose] public section

namespace PseudoPrime.Analysis.Phase64AdaptiveCell

/-- Input: one of the sixteen consecutive block indices. Output: its checked dyadic partition.
Role: collect compact certificate shapes while reusing independent kernel checks. -/
def trees (i : Fin 16) : RationalIntervalTree :=
  match i.val with
  | 0 => Block00.tree
  | 1 => Block01.tree
  | 2 => Block02.tree
  | 3 => Block03.tree
  | 4 => Block04.tree
  | 5 => Block05.tree
  | 6 => Block06.tree
  | 7 => Block07.tree
  | 8 => Block08.tree
  | 9 => Block09.tree
  | 10 => Block10.tree
  | 11 => Block11.tree
  | 12 => Block12.tree
  | 13 => Block13.tree
  | 14 => Block14.tree
  | _ => Block15.tree

/-- Input: any block index. Claim: its rational adaptive interval checker succeeds.
Proof: normalize only the block index and endpoint arithmetic, then reuse its checked theorem.
Role: avoid recomputing the complete arithmetic certificate during public integration. -/
theorem checked (i : Fin 16) :
    rationalIntervalTreeCheck
        (scaledPhaseIntervalCheck (10 ^ 12) phaseCell64Center phaseCell64Uncertainty)
        (5 * (i.val : ℚ) / 16) (5 * ((i.val + 1 : ℕ) : ℚ) / 16) (trees i) =
      true := by
  fin_cases i <;> norm_num only [trees, Nat.cast_ofNat]
  · exact Block00.checked
  · exact Block01.checked
  · exact Block02.checked
  · exact Block03.checked
  · exact Block04.checked
  · exact Block05.checked
  · exact Block06.checked
  · exact Block07.checked
  · exact Block08.checked
  · exact Block09.checked
  · exact Block10.checked
  · exact Block11.checked
  · exact Block12.checked
  · exact Block13.checked
  · exact Block14.checked
  · exact Block15.checked

end PseudoPrime.Analysis.Phase64AdaptiveCell

namespace PseudoPrime.Analysis

/-- Input: any scale in the first continuous level cell.
Claim: the actual signed Gamma phase is bounded by the resolvent at every ordinate in [0,5].
Proof: apply adaptive tree soundness to all blocks and join the adjacent intervals.
Role: remove the remaining low-frequency spectral premise on this scale cell. -/
theorem phaseCell64_full_positive {x : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 5,
      -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
        finiteSignedResolvent phaseResolvent64Coefficients t := by
  have hSegment (i : ℕ) (hi : i < 16) :
    ∀ t ∈ Set.Icc (5 * (i : ℝ) / 16) (5 * ((i + 1 : ℕ) : ℝ) / 16),
      -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
        finiteSignedResolvent phaseResolvent64Coefficients t := by
    have h :=
      phaseCell64_adaptive_tree_sound hlo hhi (Phase64AdaptiveCell.trees ⟨i, hi⟩) (5 * (i : ℚ) / 16)
        (5 * ((i + 1 : ℕ) : ℚ) / 16) (Phase64AdaptiveCell.checked ⟨i, hi⟩)
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using h
  have h := property_on_adjacent_chain (fun i : ℕ ↦ 5 * (i : ℝ) / 16) 15 hSegment
  norm_num only [Nat.cast_ofNat] at h
  exact h

/-- Input: any scale in the first continuous level cell and any real ordinate.
Claim: the actual signed Gamma phase is bounded globally by the candidate resolvent.
Proof: reflect the certified low interval and use the established norm tail.
Role: provide a complete analytic majorant with no spectral certificate premise. -/
theorem phaseCell64_full_phase {x : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  exact
    phase64_signed_phase_le_of_positive_low
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 163840 / 99) hlo)
      (phaseCell64_full_positive hlo hhi) t

/-- Input: any real level in [64,64.001] and any real ordinate.
Claim: the actual Gamma phase at scale L^2/(99/40) is bounded by the candidate resolvent.
Proof: transport the exact scale interval into the complete majorant theorem.
Role: expose the certificate in the intended witness-analysis coordinates. -/
theorem phaseCell64_full_phase_of_level {L : ℝ} (hlo : (64 : ℝ) ≤ L) (hhi : L ≤ 64001 / 1000)
    (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
            ((L ^ 2 / (99 / 40) : ℝ) : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  obtain ⟨ha, hb⟩ := scale64_cell_of_level hlo hhi
  exact phaseCell64_full_phase ha hb t

end PseudoPrime.Analysis
