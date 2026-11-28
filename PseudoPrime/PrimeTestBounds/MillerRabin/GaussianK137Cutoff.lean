/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformWideWindow

/-! # Gaussian cutoff certificates for the remaining K137 cells -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At and above log 2653/4, the fixed scale for K137 cell 2
gives a squared radius within the Gaussian cutoff. -/
theorem gaussianCutoff_k137_cell2 {L : ℝ} (hL : 2653 / 4 ≤ L) :
    ((1000313174587 / 1000000000000 : ℝ) * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  let E : ℝ :=
    73395590215565816490885120000000000000000000000000000000000000000000 /
      73662908583704404895052364345532806247589340103036241884149957051967
  apply
    gaussianCell_cutoff_of_taylor (a := 2653 / 4) (N := 8) (E := E) (c :=
      (1000313174587 / 1000000000000 : ℝ) ^ 2 / 4) (by norm_num only) hL
  all_goals
    norm_num only [E, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one]

/-- At and above log 1327/2, the fixed scale for K137 cell 3
gives a squared radius within the Gaussian cutoff. -/
theorem gaussianCutoff_k137_cell3 {L : ℝ} (hL : 1327 / 2 ≤ L) :
    ((1000328278743 / 1000000000000 : ℝ) * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  let E : ℝ :=
    31357979218076215541760000000000000000000000000000000000000000000 /
      31472276218934610923439030132271354173224750626177028004231008609
  apply
    gaussianCell_cutoff_of_taylor (a := 1327 / 2) (N := 8) (E := E) (c :=
      (1000328278743 / 1000000000000 : ℝ) ^ 2 / 4) (by norm_num only) hL
  all_goals
    norm_num only [E, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one]

/-- At and above log 2655/4, the fixed scale for K137 cell 4
gives a squared radius within the Gaussian cutoff. -/
theorem gaussianCutoff_k137_cell4 {L : ℝ} (hL : 2655 / 4 ≤ L) :
    ((200068674267 / 200000000000 : ℝ) * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  let E : ℝ :=
    9352881611825347068562925158400000000000000000000000000000 /
      9386997761687231913026085007113348084803132698759186676369
  apply
    gaussianCell_cutoff_of_taylor (a := 2655 / 4) (N := 8) (E := E) (c :=
      (200068674267 / 200000000000 : ℝ) ^ 2 / 4) (by norm_num only) hL
  all_goals
    norm_num only [E, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one]

/-- At and above log 5311/8, the fixed scale for K137 cell 5
gives a squared radius within the Gaussian cutoff. -/
theorem gaussianCutoff_k137_cell5 {L : ℝ} (hL : 5311 / 8 ≤ L) :
    ((1000350913299 / 1000000000000 : ℝ) * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  let E : ℝ :=
    8417593450642812361706632642560000000000000000000000000000000000000000000 /
      8448309572480600242927337653919352350950487048182414182683345558542253441
  apply
    gaussianCell_cutoff_of_taylor (a := 5311 / 8) (N := 8) (E := E) (c :=
      (1000350913299 / 1000000000000 : ℝ) ^ 2 / 4) (by norm_num only) hL
  all_goals
    norm_num only [E, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one]

/-- At and above log 664, the fixed scale for K137 cell 6
gives a squared radius within the Gaussian cutoff. -/
theorem gaussianCutoff_k137_cell6 {L : ℝ} (hL : 664 ≤ L) :
    ((125044806547 / 125000000000 : ℝ) * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  let E : ℝ :=
    108794845417579304012178909033536911010742187500 /
      109191991773913786930950463374143419940241442751
  apply
    gaussianCell_cutoff_of_taylor (a := 664) (N := 8) (E := E) (c :=
      (125044806547 / 125000000000 : ℝ) ^ 2 / 4) (by norm_num only) hL
  all_goals
    norm_num only [E, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one]

/-- For an ordered uniform triple with log at least 663, the first K137
cutoff fits under the Gaussian cutoff and its square stays below the
least prime factor. Both conditions apply at the same fixed scale. -/
theorem k137_first_cutoff_window {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n)
    (hL : 663 ≤ Real.log n) :
    let y := (250074514713 / 250000000000 : ℝ) * Real.log n / 2
    y ^ 2 ≤ gaussianWitnessCutoff (Real.log n) ∧ y ^ 4 < (p : ℝ) := by
  have hl : 465 ≤ Real.log n := (by norm_num only : (465 : ℝ) ≤ 663).trans hL
  exact
    ⟨gaussianCutoff_k137_first hL,
      uniform_scaled_window_lt_prime hn hp hq hr hpq hqr hu hl (by norm_num only)
        (by norm_num only)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
