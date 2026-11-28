/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeBoundary663
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianFirstCutoff
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PsiQuarterBridge
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev boundary checks for the next K137 cells -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Signed tick constraints on a closed real interval with integer endpoints. -/
private structure SignedPsiRow where
  left : ℕ
  right : ℕ
  floor : ℤ
  deriving DecidableEq

/-- Use the largest requested floor at each cursor. The maximum handles
overlapping rows without repeating the prefix walk. -/
private def signedRowFloor (fallback : ℤ) (n : ℕ) : List SignedPsiRow → ℤ
  | [] => fallback
  | r :: rs =>
    let rest := signedRowFloor fallback n rs
    if r.left < n ∧ n ≤ r.right then max r.floor rest else rest

private theorem row_floor_le {fallback : ℤ} {rs : List SignedPsiRow} {r : SignedPsiRow}
    (hr : r ∈ rs) {n : ℕ} (hl : r.left < n) (hu : n ≤ r.right) :
    r.floor ≤ signedRowFloor fallback n rs := by
  induction rs with
  | nil => exact False.elim (List.not_mem_nil hr)
  | cons q qs ih =>
    rw [signedRowFloor]
    rcases List.mem_cons.mp hr with h | h
    · subst q
      rw [ite_eq_left ⟨hl, hu⟩]
      exact le_max_left _ _
    · split
      · exact (ih h).trans (le_max_right _ _)
      · exact ih h

/-- A walk that verifies the maximum of the active rows certifies each
row over its entire closed interval. -/
private theorem signed_row_of_walk {a b k : ℕ} {s : Edge} {fallback : ℤ} {rs : List SignedPsiRow}
    {r : SignedPsiRow} (hr : r ∈ rs) (hs : Valid s) (ha : a ≤ s.n) (hb : s.n + k ≤ b)
    (hu : b ≤ 1000001)
    (hc : signedWalk (gcdStep a b) (fun n ↦ signedRowFloor fallback n rs) k s = true)
    (hstart : s.n ≤ r.left + 1) (hend : r.right < s.n + k) (hlt : r.left < r.right) {x : ℝ}
    (hleft : (r.left : ℝ) ≤ x) (hright : x ≤ r.right) :
    (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x := by
  let n := min (⌊x⌋₊ + 1) r.right
  have hn₁ : r.left + 1 ≤ n := le_min (Nat.succ_le_succ (Nat.le_floor hleft)) hlt
  have hn₂ : n ≤ r.right := min_le_right _ _
  have hl : ((n - 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.sub_le_of_le_add (min_le_left _ _))).trans
      (Nat.floor_le ((Nat.cast_nonneg r.left).trans hleft))
  have hh : x ≤ (n : ℝ) := by
    simpa only [n, Nat.cast_min, Nat.cast_add, Nat.cast_one] using
      le_min (Nat.lt_floor_add_one x).le hright
  have h := signed_walk_sound _ k s hs ha hb hu hc n (hstart.trans hn₁) (hn₂.trans_lt hend) x hl hh
  have hrow := row_floor_le (fallback := fallback) hr (Nat.lt_of_succ_le hn₁) hn₂
  exact (div_le_div_of_nonneg_right (Int.cast_le.mpr hrow) (Nat.cast_nonneg scale)).trans h

private def gaussianPsiRows : List SignedPsiRow :=
  [⟨110130, 110297, -62000000000000⟩, ⟨110303, 110387, -65000000000000⟩,
    ⟨110389, 110556, -97000000000000⟩, ⟨110562, 110729, -78000000000000⟩,
    ⟨110735, 111069, -68000000000000⟩, ⟨111081, 111416, -76000000000000⟩,
    ⟨111428, 111596, -84000000000000⟩, ⟨111602, 111938, -85000000000000⟩,
    ⟨111950, 112286, -77000000000000⟩, ⟨112298, 112635, -75000000000000⟩,
    ⟨112647, 112816, -98000000000000⟩, ⟨112822, 112907, -126000000000000⟩]

set_option maxRecDepth 16384 in
-- This single walk shares the prefix for all rows of the block.
private theorem gaussian_rows_checked :
    signedWalk (gcdStep 106539 112908)
        (fun n ↦ signedRowFloor (-1000000000000000) n gaussianPsiRows) 6369 bridgeStart =
      true := by
  decide +kernel

private theorem gaussian_psi_row {r : SignedPsiRow} (hr : r ∈ gaussianPsiRows)
    (ha : 106539 ≤ r.left + 1) (hb : r.right < 112908) (hlt : r.left < r.right) {x : ℝ}
    (hl : (r.left : ℝ) ≤ x) (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr bridge_start_valid (by decide) (by decide) (by decide) gaussian_rows_checked
    ha hb hlt hl hu

/-- Signed psi floor on the squared-cutoff interval for k137 second. -/
theorem psi_gaussian_k137_second {x : ℝ} (hl : 110130 ≤ x) (hu : x ≤ 110297) :
    -62 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨110130, 110297, -62000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k137 third. -/
theorem psi_gaussian_k137_third {x : ℝ} (hl : 110303 ≤ x) (hu : x ≤ 110387) :
    -65 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨110303, 110387, -65000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 first. -/
theorem psi_gaussian_k197_first {x : ℝ} (hl : 110389 ≤ x) (hu : x ≤ 110556) :
    -97 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨110389, 110556, -97000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell2. -/
theorem psi_gaussian_k197_cell2 {x : ℝ} (hl : 110562 ≤ x) (hu : x ≤ 110729) :
    -78 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨110562, 110729, -78000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell3. -/
theorem psi_gaussian_k197_cell3 {x : ℝ} (hl : 110735 ≤ x) (hu : x ≤ 111069) :
    -68 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨110735, 111069, -68000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell4. -/
theorem psi_gaussian_k197_cell4 {x : ℝ} (hl : 111081 ≤ x) (hu : x ≤ 111416) :
    -76 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨111081, 111416, -76000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell5. -/
theorem psi_gaussian_k197_cell5 {x : ℝ} (hl : 111428 ≤ x) (hu : x ≤ 111596) :
    -84 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨111428, 111596, -84000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell6. -/
theorem psi_gaussian_k197_cell6 {x : ℝ} (hl : 111602 ≤ x) (hu : x ≤ 111938) :
    -85 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨111602, 111938, -85000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell7. -/
theorem psi_gaussian_k197_cell7 {x : ℝ} (hl : 111950 ≤ x) (hu : x ≤ 112286) :
    -77 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨111950, 112286, -77000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell8. -/
theorem psi_gaussian_k197_cell8 {x : ℝ} (hl : 112298 ≤ x) (hu : x ≤ 112635) :
    -75 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨112298, 112635, -75000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell9. -/
theorem psi_gaussian_k197_cell9 {x : ℝ} (hl : 112647 ≤ x) (hu : x ≤ 112816) :
    -98 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨112647, 112816, -98000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared-cutoff interval for k197 cell10. -/
theorem psi_gaussian_k197_cell10 {x : ℝ} (hl : 112822 ≤ x) (hu : x ≤ 112907) :
    -126 ≤ Chebyshev.psi x - x := by
  have h :=
    gaussian_psi_row (r := ⟨112822, 112907, -126000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem k137_scaled_square_mem {s a b L : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hL : L ∈ Set.Icc a b) : (s * L / 2) ^ 2 ∈ Set.Icc ((s * a / 2) ^ 2) ((s * b / 2) ^ 2) := by
  have h₁ : s * a / 2 ≤ s * L / 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL.1 hs) (by norm_num only)
  have h₂ : s * L / 2 ≤ s * b / 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL.2 hs) (by norm_num only)
  have h₀ : 0 ≤ s * a / 2 := div_nonneg (mul_nonneg hs ha) (by norm_num only)
  exact ⟨pow_le_pow_left₀ h₀ h₁ 2, pow_le_pow_left₀ (h₀.trans h₁) h₂ 2⟩

/-- Transfer the signed second-cell Chebyshev estimate to its Abel boundary. -/
theorem gaussian_second_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1327 / 2) 664) :
    let y := (1000328278743 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.070 := by
  intro y
  have hsq :=
    k137_scaled_square_mem (s := 1000328278743 / 1000000000000) (by norm_num only)
      (by norm_num only) hL
  have hlo : (110130 : ℝ) ≤ ((1000328278743 / 1000000000000) * (1327 / 2) / 2) ^ 2 := by
    norm_num only
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k137_second (hlo.trans hsq.1)
      (hsq.2.trans (by norm_num only))
  have hy : (663 / 2 : ℝ) ≤ y := by
    dsimp only [y]; linarith only [hL.1]
  have h :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy
      (by norm_num only : (0 : ℝ) ≤ 62) hψ
  linarith only [h]

/-- Transfer the signed third-cell Chebyshev estimate to its Abel boundary. -/
theorem gaussian_third_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 664 (2657 / 4)) :
    let y := (125044806547 / 125000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.074 := by
  intro y
  have hsq :=
    k137_scaled_square_mem (s := 125044806547 / 125000000000) (by norm_num only) (by norm_num only)
      hL
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k137_third
      ((by norm_num only : (110303 : ℝ) ≤ ((125044806547 / 125000000000) * 664 / 2) ^ 2).trans
        hsq.1)
      (hsq.2.trans (by norm_num only))
  have hy : (663 / 2 : ℝ) ≤ y := by
    dsimp only [y]; linarith only [hL.1]
  have h :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy
      (by norm_num only : (0 : ℝ) ≤ 65) hψ
  linarith only [h]

/-- Under RH, the signed boundary and principal Abel integral for the
second K137 cell together cost at most 0.123. -/
theorem gaussian_second_abel_le (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (1327 / 2) 664) :
    let y := (1000328278743 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) -
        4 *
          (∫ t in y ^ 2..y ^ 2 * Real.exp (21 / 8),
            (Chebyshev.psi t - t) * deriv (quarterWeight656 (y ^ 2)) t) ≤
      0.123 := by
  intro y
  have hy : y ∈ Set.Icc (663 / 2) (1329 / 4) :=
    ⟨by
      dsimp only [y]; linarith only [hL.1], by
      dsimp only [y]; linarith only [hL.2]⟩
  have hb := gaussian_second_boundary_le hL
  change -4 * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.070 at hb
  linarith only [hb, gaussian_first_integral_le hRH hy]

/-- Under RH, the signed boundary and principal Abel integral for the
third K137 cell together cost at most 0.127. -/
theorem gaussian_third_abel_le (hRH : RiemannHypothesis) {L : ℝ} (hL : L ∈ Set.Icc 664 (2657 / 4)) :
    let y := (125044806547 / 125000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) -
        4 *
          (∫ t in y ^ 2..y ^ 2 * Real.exp (21 / 8),
            (Chebyshev.psi t - t) * deriv (quarterWeight656 (y ^ 2)) t) ≤
      0.127 := by
  intro y
  have hy : y ∈ Set.Icc (663 / 2) (1329 / 4) :=
    ⟨by
      dsimp only [y]; linarith only [hL.1], by
      dsimp only [y]; linarith only [hL.2]⟩
  have hb := gaussian_third_boundary_le hL
  change -4 * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.074 at hb
  linarith only [hb, gaussian_first_integral_le hRH hy]

/-- Transfer the first K197 cell's signed psi bound to the Abel boundary. -/
theorem gaussian_k197_first_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2657 / 4) (2659 / 4)) :
    let y := (500186760939 / 500000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.110 := by
  intro y
  have hsq :=
    k137_scaled_square_mem (s := 500186760939 / 500000000000) (by norm_num only) (by norm_num only)
      hL
  have hlo : (110389 : ℝ) ≤ ((500186760939 / 500000000000) * (2657 / 4) / 2) ^ 2 := by norm_num only
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_first (hlo.trans hsq.1)
      (hsq.2.trans (by norm_num only))
  have hy : (663 / 2 : ℝ) ≤ y := by
    dsimp only [y]
    linarith only [hL.1]
  have h :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy
      (by norm_num only : (0 : ℝ) ≤ 97) hψ
  linarith only [h]

/-- Abel boundary cost on compressed K197 cell 2. -/
theorem gaussian_k197_cell2_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2659 / 4) (2661 / 4)) :
    let y := (12505045329 / 12500000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.089 := by
  intro y
  have hsq :=
    k137_scaled_square_mem (s := 12505045329 / 12500000000) (by norm_num only) (by norm_num only) hL
  have hlo : (110562 : ℝ) ≤ ((12505045329 / 12500000000) * (2659 / 4) / 2) ^ 2 := by norm_num only
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell2 (hlo.trans hsq.1)
      (hsq.2.trans (by norm_num only))
  have hy : (663 / 2 : ℝ) ≤ y := by
    dsimp only [y]
    linarith only [hL.1]
  have h :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy
      (by norm_num only : (0 : ℝ) ≤ 78) hψ
  linarith only [h]

/-- Abel boundary cost on compressed K197 cell 3. -/
theorem gaussian_k197_cell3_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2661 / 4) (2665 / 4)) :
    let y := (1000433684769 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.077 := by
  intro y
  have hsq :=
    k137_scaled_square_mem (s := 1000433684769 / 1000000000000) (by norm_num only)
      (by norm_num only) hL
  have hlo : (110735 : ℝ) ≤ ((1000433684769 / 1000000000000) * (2661 / 4) / 2) ^ 2 := by
    norm_num only
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell3 (hlo.trans hsq.1)
      (hsq.2.trans (by norm_num only))
  have hy : (663 / 2 : ℝ) ≤ y := by
    dsimp only [y]
    linarith only [hL.1]
  have h :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy
      (by norm_num only : (0 : ℝ) ≤ 68) hψ
  linarith only [h]

/-- Abel boundary cost on compressed K197 cell 4. -/
theorem gaussian_k197_cell4_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2665 / 4) (2669 / 4)) :
    let y := (500246832053 / 500000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.086 := by
  intro y
  have hsq :=
    k137_scaled_square_mem (s := 500246832053 / 500000000000) (by norm_num only) (by norm_num only)
      hL
  have hlo : (111081 : ℝ) ≤ ((500246832053 / 500000000000) * (2665 / 4) / 2) ^ 2 := by norm_num only
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell4 (hlo.trans hsq.1)
      (hsq.2.trans (by norm_num only))
  have hy : (663 / 2 : ℝ) ≤ y := by
    dsimp only [y]
    linarith only [hL.1]
  have h :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy
      (by norm_num only : (0 : ℝ) ≤ 76) hψ
  linarith only [h]

/-- Abel boundary cost on compressed K197 cell 5. -/
theorem gaussian_k197_cell5_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2669 / 4) (2671 / 4)) :
    let y := (1000553460733 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.095 := by
  intro y
  have hsq :=
    k137_scaled_square_mem (s := 1000553460733 / 1000000000000) (by norm_num only)
      (by norm_num only) hL
  have hlo : (111428 : ℝ) ≤ ((1000553460733 / 1000000000000) * (2669 / 4) / 2) ^ 2 := by
    norm_num only
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell5 (hlo.trans hsq.1)
      (hsq.2.trans (by norm_num only))
  have hy : (663 / 2 : ℝ) ≤ y := by
    dsimp only [y]
    linarith only [hL.1]
  have h :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy
      (by norm_num only : (0 : ℝ) ≤ 84) hψ
  linarith only [h]

private theorem k197_boundary_from_row {s a b A B e C L : ℝ} (hs : 1 ≤ s) (ha : (663 : ℝ) ≤ a)
    (hL : L ∈ Set.Icc a b) (hlo : A ≤ (s * a / 2) ^ 2) (hhi : (s * b / 2) ^ 2 ≤ B) (he : 0 ≤ e)
    (hψ : ∀ x : ℝ, A ≤ x → x ≤ B → -e ≤ Chebyshev.psi x - x)
    (hC : 4 * (9319732 / 100000000 : ℝ) * e / (663 / 2) ≤ C) :
    let y := s * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ C := by
  intro y
  have hL0 : 0 ≤ L := ((by norm_num only : (0 : ℝ) ≤ 663).trans ha).trans hL.1
  have hsq :=
    k137_scaled_square_mem (zero_le_one.trans hs) ((by norm_num only : (0 : ℝ) ≤ 663).trans ha) hL
  have hy : (663 / 2 : ℝ) ≤ y := by
    dsimp only [y]
    linarith only [ha, hL.1, mul_le_mul_of_nonneg_right hs hL0]
  have h :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy he
      (hψ ((s * L / 2) ^ 2) (hlo.trans hsq.1) (hsq.2.trans hhi))
  linarith only [h, hC]

/-- Abel boundary cost on compressed K197 cell 6. -/
theorem gaussian_k197_cell6_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2671 / 4) (2675 / 4)) :
    let y := (1000583290791 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.096 := by
  apply
    k197_boundary_from_row (s := 1000583290791 / 1000000000000) (A := 111602) (B := 111938) (e :=
      85) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell6 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 7. -/
theorem gaussian_k197_cell7_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2675 / 4) (2679 / 4)) :
    let y := (1000642814919 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.087 := by
  apply
    k197_boundary_from_row (s := 1000642814919 / 1000000000000) (A := 111950) (B := 112286) (e :=
      77) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell7 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 8. -/
theorem gaussian_k197_cell8_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2679 / 4) (2683 / 4)) :
    let y := (1000702158417 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.085 := by
  apply
    k197_boundary_from_row (s := 1000702158417 / 1000000000000) (A := 112298) (B := 112635) (e :=
      75) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell8 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 9. -/
theorem gaussian_k197_cell9_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2683 / 4) (2685 / 4)) :
    let y := (1000761322111 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.111 := by
  apply
    k197_boundary_from_row (s := 1000761322111 / 1000000000000) (A := 112647) (B := 112816) (e :=
      98) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell9 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 10. -/
theorem gaussian_k197_cell10_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2685 / 4) (2686 / 4)) :
    let y := (1000790836787 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.142 := by
  apply
    k197_boundary_from_row (s := 1000790836787 / 1000000000000) (A := 112822) (B := 112907) (e :=
      126) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell10 hl hu)
      (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
