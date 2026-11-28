/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighNegativeMoment
import Mathlib.Tactic.FinCases

/-! # Compressed sign partitions for the high Gaussian negative moments -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Quarter-unit nodes and outgoing cell signs for derivatives zero through two.
The sign zero selects Bernstein integration without a sign assumption. -/
private def correctionPlan (K : HighGaussianKernel) (j : Fin 3) : Array ℕ × Array ℤ :=
  match K, j.val with
  | .k186, 0 => (#[140, 228, 229, 242, 243, 260], #[1, 0, -1, 0, 1])
  | .k186, 1 => (#[140, 226, 227, 241, 242, 260], #[1, 0, -1, 0, 1])
  | .k186, _ => (#[140, 224, 225, 239, 240, 260], #[1, 0, -1, 0, 1])
  | .k196, 0 =>
    (#[170, 237, 239, 251, 252, 268, 269, 292, 293, 320], #[-1, 0, -1, 0, 1, 0, -1, 0, 1])
  | .k196, 1 =>
    (#[170, 235, 236, 238, 239, 250, 251, 267, 268, 291, 292, 320],
      #[-1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1])
  | .k196, _ =>
    (#[170, 233, 234, 237, 238, 249, 250, 265, 266, 289, 290, 320],
      #[-1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1])

/-- The number of cells in the compressed plan. -/
private def planCount (K : HighGaussianKernel) (j : Fin 3) : ℕ :=
  (correctionPlan K j).1.size - 1

/-- A compressed node, extended constantly beyond the last cell. -/
private def planNode (K : HighGaussianKernel) (j : Fin 3) (i : ℕ) : ℕ :=
  (correctionPlan K j).1[min i (planCount K j)]?.getD 0

/-- The sign attached to the outgoing cell. -/
private def planSign (K : HighGaussianKernel) (j : Fin 3) (i : ℕ) : ℤ :=
  (correctionPlan K j).2[i]?.getD 0

/-- The width of the outgoing cell in quarter units. -/
private def planWidth (K : HighGaussianKernel) (j : Fin 3) (i : ℕ) : ℕ :=
  planNode K j (i + 1) - planNode K j i

/-- Check the sign selected by the compressed plan, with no test for mixed cells. -/
private def planSignCheck (K : HighGaussianKernel) (j : Fin 3) (i : ℕ) : Bool :=
  let b := planNode K j i
  let w := planWidth K j i
  if planSign K j i = 1 then highProfileCellNonneg K j b w
  else if planSign K j i = -1 then highProfileCellSign K j b w (-1) else true

/-- The compact Boolean sign certificate for one high kernel and derivative. -/
public def highCompressedSignCheck (K : HighGaussianKernel) (j : Fin 3) : Bool :=
  (List.range (planCount K j)).all (planSignCheck K j)

/-- Compute the selected analytic upper bound for a single compressed cell. -/
private def planCharge (K : HighGaussianKernel) (j : Fin 3) (i : ℕ) : ℚ :=
  let b := planNode K j i
  let w := planWidth K j i
  if planSign K j i = 1 then 0
  else
    if planSign K j i = -1 then highNonposCellCharge K j b w
    else (highNegativeBlockTicks K j (b - planNode K j 0) w : ℚ) / 10 ^ 6

/-- The computed sum of charges on the compressed partition. -/
public def highCompressedMomentCharge (K : HighGaussianKernel) (j : Fin 3) : ℚ :=
  ∑ i ∈ Finset.range (planCount K j), planCharge K j i

/-- Integer caps proposed for the three compressed sums, in derivative order.
Each candidate is checked separately from the sign certificate. -/
@[expose]
public def highCompressedMomentCap (K : HighGaussianKernel) (j : Fin 3) : ℚ :=
  match K, j.val with
  | .k186, 0 => 272
  | .k186, 1 => 653
  | .k186, _ => 1577
  | .k196, 0 => 19685
  | .k196, 1 => 52535
  | .k196, _ => 149870

/-- The stored nodes are strictly increasing up to the last cell. -/
private theorem plan_step (K : HighGaussianKernel) (j : Fin 3) :
    ∀ i : Fin (planCount K j), planNode K j i < planNode K j (i + 1) := by
  cases K <;> fin_cases j <;> decide

/-- The clamped extension of the finite nodes preserves monotonicity. -/
private theorem plan_mono (K : HighGaussianKernel) (j : Fin 3) : Monotone (planNode K j) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i < planCount K j
  · exact (plan_step K j ⟨i, hi⟩).le
  · simp only [planNode, min_eq_right (Nat.le_of_not_gt hi),
      min_eq_right ((Nat.le_of_not_gt hi).trans (Nat.le_succ i)), le_refl]

/-- The compressed plan starts at the prescribed correction boundary. -/
private theorem plan_start (K : HighGaussianKernel) (j : Fin 3) :
    (planNode K j 0 : ℝ) / 4 = (profileCorrectionStart K : ℝ) := by
  cases K
  · rw [show planNode .k186 j 0 = 140 by fin_cases j <;> decide]
    norm_num only [profileCorrectionStart, Rat.cast_ofNat, Nat.cast_ofNat]
  · rw [show planNode .k196 j 0 = 170 by fin_cases j <;> decide]
    norm_num only [profileCorrectionStart, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]

/-- The compressed plan ends at the prescribed terminal sign boundary. -/
private theorem plan_end (K : HighGaussianKernel) (j : Fin 3) :
    (planNode K j (planCount K j) : ℝ) / 4 = (profileCorrectionEnd K : ℝ) := by
  cases K
  · rw [show planNode .k186 j (planCount .k186 j) = 260 by fin_cases j <;> decide]
    norm_num only [profileCorrectionEnd, Nat.cast_ofNat, Int.cast_ofNat]
  · rw [show planNode .k196 j (planCount .k196 j) = 320 by fin_cases j <;> decide]
    norm_num only [profileCorrectionEnd, Nat.cast_ofNat, Int.cast_ofNat]

/-- All stored cells lie below the bound used by the endpoint exponentials. -/
private theorem plan_cap (K : HighGaussianKernel) (j : Fin 3) :
    planNode K j (planCount K j) ≤ 320 := by cases K <;> fin_cases j <;> decide

/-- The certified compact partition bounds the entire H28 moment.
The proof consumes only a scalar Boolean result, with the nodes and
sign tags private to this module. -/
public theorem high_compressed_moment_le (K : HighGaussianKernel) (j : Fin 3)
    (h : highCompressedSignCheck K j = true) :
    highNegativeMoment K j ≤ (highCompressedMomentCharge K j : ℝ) := by
  refine
    high_negative_partition_le K j (planCount K j) (planNode K j) (planCharge K j) (plan_mono K j)
      (fun i hi ↦ plan_step K j ⟨i, hi⟩) (plan_start K j) (plan_end K j) (plan_cap K j) ?_
  intro i hi
  have hc := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  by_cases hp : planSign K j i = 1
  · exact
      Or.inl
        ⟨by simpa only [planSignCheck, ite_eq_left hp, planWidth] using hc, by
          simp only [planCharge, ite_eq_left hp, le_refl]⟩
  · by_cases hn : planSign K j i = -1
    · exact
        Or.inr
          (Or.inl
            ⟨by simpa only [planSignCheck, ite_eq_right hp, ite_eq_left hn, planWidth] using hc, by
              simp only [planCharge, ite_eq_right hp, ite_eq_left hn, planWidth, le_refl]⟩)
    · exact
        Or.inr
          (Or.inr (by simp only [planCharge, ite_eq_right hp, ite_eq_right hn, planWidth, le_refl]))

end PseudoPrime.PrimeTestBounds.MillerRabin
