/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentAtom663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerSieve663

/-! # Kernel evaluation of the first section 137 moment block -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def firstRows : Finset MomentRow663 :=
  {⟨107599, 1, 17, 17, 11586166628552, 11586166637076, 11586166628552, 11586166637076,
      1044924569808053⟩,
    ⟨107603, 1, 17, 17, 11586203802929, 11586203811453, 11586203802929, 11586203811453,
      1044947876719104⟩,
    ⟨107609, 1, 17, 17, 11586259561902, 11586259570426, 11586259561902, 11586259570426,
      1044982836435888⟩}

set_option maxRecDepth 8192 in
-- Kernel reduction checks prime-power support in this small segment and the Taylor bounds.
/-- The first 32 integers of the section 137 window have checked moments
in all six degrees. The row and coverage checks are shared across degrees. -/
theorem quarter_first_moments_663 (j : Fin 6) :
    quarterMangoldtPrefix663 107616 j - quarterMangoldtPrefix663 107584 j ∈
      Set.Icc
        ((![3632109162383, 1502930423717, 621897574326, 257334997112, 106482649292, 44061456172] :
              Fin 6 → ℝ)
            j /
          10 ^ 8)
        ((![3632109165059, 1502930455786, 621897600409, 257335013207, 106482658148, 44061460745] :
              Fin 6 → ℝ)
            j /
          10 ^ 8) := by
  have hp : quarterSievePrimeIndices663 107584 107616 = [107599, 107603, 107609] := by
    decide +kernel
  have hs : firstRows.image MomentRow663.index = [107599, 107603, 107609].toFinset := by
    decide +kernel
  have hproper :
    ∀ n ∈ Finset.Ioc 107584 107616,
      IsPrimePow n → @decide n.Prime (Nat.decidablePrime' n) = true := by
    decide +kernel
  have hs' (n : ℕ) :
    n ∈ firstRows.image MomentRow663.index ↔ n ∈ Finset.Ioc 107584 107616 ∧ IsPrimePow n := by
    rw [hs, List.mem_toFinset, ← hp, quarter_sieve_indices_iff_663 (by decide)]
    exact
      and_congr_right fun hn ↦
        ⟨fun hp' ↦ (isPrimePow_nat_iff n).mpr ⟨n, 1, hp', by decide, pow_one n⟩, fun ht ↦
          @of_decide_eq_true n.Prime (Nat.decidablePrime' n) (hproper n hn ht)⟩
  have h :=
    quarter_checked_row_sum_663 (L := 107584) (U := 107616) (j := (j : ℕ)) (by decide) firstRows
      (by decide +kernel) hs' (by decide +kernel)
  have hl :
    ∀ i : Fin 6,
      (∑ r ∈ firstRows, (r.moment i).1) =
        (![3632109162383, 1502930423717, 621897574326, 257334997112, 106482649292, 44061456172] :
            Fin 6 → ℤ)
          i := by
    decide +kernel
  have hu :
    ∀ i : Fin 6,
      (∑ r ∈ firstRows, (r.moment i).2) =
        (![3632109165059, 1502930455786, 621897600409, 257335013207, 106482658148, 44061460745] :
            Fin 6 → ℤ)
          i := by
    decide +kernel
  rw [hl j, hu j] at h
  fin_cases j <;> exact h

private def squareRows : Finset MomentRow663 :=
  {⟨331, 2, 8, 17, 5802118373283, 5802118377306, 11604236746320, 11604236754844, 1056315354090544⟩,
    ⟨109567, 1, 17, 17, 11604291508834, 11604291517358, 11604291508834, 11604291517358,
      1056350062550901⟩,
    ⟨109579, 1, 17, 17, 11604401024863, 11604401033387, 11604401024863, 11604401033387,
      1056419477190894⟩,
    ⟨109583, 1, 17, 17, 11604437527541, 11604437536065, 11604437527541, 11604437536065,
      1056442614728519⟩}

set_option maxRecDepth 8192 in
-- The four row indices are compared against the sieve on this small window.
private theorem square_rows_cover (n : ℕ) :
    n ∈ squareRows.image MomentRow663.index ↔ n ∈ Finset.Ioc 109552 109584 ∧ IsPrimePow n := by
  have hp : quarterSievePrimeIndices663 109552 109584 = [109567, 109579, 109583] := by
    decide +kernel
  have hq : quarterProperPowers663 109552 109584 = [109561] := by decide +kernel
  have hs :
    squareRows.image MomentRow663.index = ([109567, 109579, 109583] ++ [109561]).toFinset := by
    decide +kernel
  rw [hs, List.mem_toFinset, ← hp, ← hq, quarter_power_indices_iff_663 (by decide)]

set_option maxRecDepth 8192 in
-- Validate each Taylor enclosure once before using any slice.
private theorem square_rows_checked : ∀ r ∈ squareRows, r.check = true := by decide +kernel

set_option maxRecDepth 8192 in
-- Kernel reduction checks prime-power support in this small segment and the Taylor bounds.
/-- The 32 integers around the square of 331 have checked moments
in all six degrees, using the two lists of prime and proper-power indices. -/
theorem quarter_square_block_moments_663 (j : Fin 6) :
    quarterMangoldtPrefix663 109584 j - quarterMangoldtPrefix663 109552 j ∈
      Set.Icc
        ((![4290559837298, 1697531218654, 671616864106, 265720726437, 105130634446, 41594236360] :
              Fin 6 → ℝ)
            j /
          10 ^ 8)
        ((![4290559840430, 1697531256468, 671616893540, 265720743810, 105130643587, 41594240876] :
              Fin 6 → ℝ)
            j /
          10 ^ 8) := by
  have h :=
    quarter_checked_row_sum_663 (L := 109552) (U := 109584) (j := (j : ℕ)) (by decide) squareRows
      square_rows_checked square_rows_cover (by decide +kernel)
  have hl :
    ∀ i : Fin 6,
      (∑ r ∈ squareRows, (r.moment i).1) =
        (![4290559837298, 1697531218654, 671616864106, 265720726437, 105130634446, 41594236360] :
            Fin 6 → ℤ)
          i := by
    decide +kernel
  have hu :
    ∀ i : Fin 6,
      (∑ r ∈ squareRows, (r.moment i).2) =
        (![4290559840430, 1697531256468, 671616893540, 265720743810, 105130643587, 41594240876] :
            Fin 6 → ℤ)
          i := by
    decide +kernel
  rw [hl j, hu j] at h
  fin_cases j <;> exact h

set_option maxRecDepth 8192 in
-- Check the fixed-point totals for the selected slice.
/-- A cumulative checkpoint within the square block reuses its checked
rows and exact support, including the contribution of 331 squared. -/
theorem quarter_square_checkpoint_663 (j : Fin 6) :
    quarterMangoldtPrefix663 109568 j - quarterMangoldtPrefix663 109552 j ∈
      Set.Icc
        ((![1838706078515, 727625155568, 287940729328, 113945846050, 45091418354, 17843880126] :
              Fin 6 → ℝ)
            j /
          10 ^ 8)
        ((![1838706079843, 727625171768, 287940741943, 113945853498, 45091422274, 17843882063] :
              Fin 6 → ℝ)
            j /
          10 ^ 8) := by
  let rows := squareRows.filter (fun r ↦ r.index ∈ Finset.Ioc 109552 109568)
  have h :=
    quarter_checked_row_slice_663 (a := 109552) (b := 109568) (j := (j : ℕ)) (L := 109552) (U :=
      109584) le_rfl (by decide) (by decide) squareRows square_rows_checked square_rows_cover
      (by decide +kernel)
  change
    _ ∈
      Set.Icc ((↑(∑ r ∈ rows, (r.moment j).1) : ℝ) / 10 ^ 8)
        ((↑(∑ r ∈ rows, (r.moment j).2) : ℝ) / 10 ^ 8) at h
  have hl :
    ∀ i : Fin 6,
      (∑ r ∈ rows, (r.moment i).1) =
        (![1838706078515, 727625155568, 287940729328, 113945846050, 45091418354, 17843880126] :
            Fin 6 → ℤ)
          i := by
    decide +kernel
  have hu :
    ∀ i : Fin 6,
      (∑ r ∈ rows, (r.moment i).2) =
        (![1838706079843, 727625171768, 287940741943, 113945853498, 45091422274, 17843882063] :
            Fin 6 → ℤ)
          i := by
    decide +kernel
  rw [hl j, hu j] at h
  fin_cases j <;> exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
