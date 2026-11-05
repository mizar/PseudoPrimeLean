/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanCofactorWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.DualMeanScalar
/-! # Two-cell mean-counting witness at the shortened dual-scale entrance -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- Under RH, an odd product with a sufficiently large prime cofactor and logarithm
between 81000 and 5000000 has a rejecting prime below coefficient 4187/10000.
The floored radius satisfies two existing theta cells and their certified scalar gaps. -/
theorem dualMean_cofactor (hRH : RiemannHypothesis) {n m q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (hL : (81000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 5000000) (hqL : (647 / 1000 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧ (r : ℝ) ≤ (4187 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hLUbig : Real.log n ≤ 40000000000 := by linarith only [hLU]
  let L := Real.log n
  let α : ℝ := 647 / 1000
  let b := ⌊α * L⌋₊
  have hL0 : 0 < L := by linarith only [hL]
  have hτ0 : 0 ≤ α * L := mul_nonneg (by norm_num only [α]) hL0.le
  have hbhi : (b : ℝ) ≤ α * L := Nat.floor_le hτ0
  have hfloor : α * L ≤ (b : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hb : 52000 ≤ b := by
    apply (Nat.le_floor_iff hτ0).mpr
    norm_num only [Nat.cast_ofNat, α]
    linarith only [hL]
  have hbU : b ≤ 26138000000 := by
    have hbr : (b : ℝ) ≤ 26138000000 := by
      dsimp only [α] at hbhi
      linarith only [hbhi, hLU]
    exact_mod_cast hbr
  have hτ : 50000 ≤ α * L := by
    dsimp only [α]; linarith only [hL]
  have ⟨hul, huU⟩ := mean_log_radius_bounds hb hbU
  have hu0 : 0 < Real.log (b ^ 2 : ℕ) := by linarith only [hul]
  have hex : ∃ r : ℕ, r.Prime ∧ r ≤ b ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    by_cases hA : L < 1010000
    · have hbpow : b ≤ 2 ^ 20 := by
        have hx : (b : ℝ) ≤ 2 ^ 20 := by
          norm_num only
          dsimp only [α] at hbhi
          linarith only [hbhi, hA]
        exact_mod_cast hx
      have hu28 : Real.log (b ^ 2 : ℕ) ≤ 28 :=
        mean_log_radius_of_pow (Nat.zero_lt_of_lt (by linarith only [hb] : 1 < b)) hbpow
          (by norm_num only [Nat.cast_ofNat]; linarith only [Real.log_two_lt_d9])
      have hB := Nat.pow_le_pow_left hb 2
      obtain ⟨hθB, hθ, hupper⟩ := mean_theta_cell_one hRH hB
      have hgap := dualMean_gap_one hu0 hu28 hL
      exact
        large_cofactor_of_mean_cells hn ho hm hq hq2 hprod (α := α) (P := 10029 / 10000) (a :=
          9968 / 10000) (η := 993 / 1000) (by norm_num only [α]) (by norm_num only [α])
          (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
          (by norm_num only) (by norm_num only) hb hL0 hLUbig hfloor hτ hqL hul huU
          (by simpa only [Nat.cast_pow] using hθB) (by simpa only [Nat.cast_pow] using hθ)
          (by simpa only [Nat.cast_pow] using hupper) hgap
    · have hL1 : 1010000 ≤ L := le_of_not_gt hA
      have hb2 : 650000 ≤ b := by
        apply (Nat.le_floor_iff hτ0).mpr
        norm_num only [Nat.cast_ofNat, α]
        linarith only [hL1]
      have hbpow : b ≤ 2 ^ 22 := by
        have hx : (b : ℝ) ≤ 2 ^ 22 := by
          norm_num only
          dsimp only [α] at hbhi
          linarith only [hbhi, hLU]
        exact_mod_cast hx
      have hu31 : Real.log (b ^ 2 : ℕ) ≤ 31 :=
        mean_log_radius_of_pow (Nat.zero_lt_of_lt (by linarith only [hb] : 1 < b)) hbpow
          (by norm_num only [Nat.cast_ofNat]; linarith only [Real.log_two_lt_d9])
      obtain ⟨hθB, hθ, hupper⟩ := mean_theta_cell_two hRH (Nat.pow_le_pow_left hb2 2)
      have hgap := dualMean_gap_two hu0 hu31 hL1
      exact
        large_cofactor_of_mean_cells hn ho hm hq hq2 hprod (α := α) (P := 10008 / 10000) (a :=
          9991 / 10000) (η := 9983 / 10000) (by norm_num only [α]) (by norm_num only [α])
          (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
          (by norm_num only) (by norm_num only) hb hL0 hLUbig hfloor hτ hqL hul huU
          (by simpa only [Nat.cast_pow] using hθB) (by simpa only [Nat.cast_pow] using hθ)
          (by simpa only [Nat.cast_pow] using hupper) hgap
  obtain ⟨r, hr, hrb, hrnot⟩ := hex
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg b) hbhi 2
  have hrreal : (r : ℝ) ≤ (b : ℝ) ^ 2 := by exact_mod_cast hrb
  have hcoeff : α ^ 2 ≤ (4187 / 10000 : ℝ) := by norm_num only [α]
  have hcoeffL := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg L)
  have he : (α * L) ^ 2 = α ^ 2 * L ^ 2 := mul_pow α L 2
  refine ⟨r, hr, ?_, hrnot⟩
  change (r : ℝ) ≤ (4187 / 10000 : ℝ) * L ^ 2
  rw [he] at hsquare
  exact hrreal.trans (hsquare.trans hcoeffL)
end PseudoPrime.PrimeTestBounds.MillerRabin
