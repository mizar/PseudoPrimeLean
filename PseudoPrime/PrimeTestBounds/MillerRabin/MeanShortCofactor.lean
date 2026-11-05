/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanCofactorWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanShortScalar

/-! # Short-interval mean-counting witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, an odd product `n = m * q` with an odd prime cofactor larger than
`(3251 / 5000) * log n` in logarithmic scale has a rejecting prime below
`(1057 / 2500) * log n ^ 2`, when `80000 ≤ log n ≤ 2 * 10 ^ 8`.
The three rational scalar cells discharge the generic mean-counting criterion. -/
theorem large_cofactor_witness_04228 (hRH : RiemannHypothesis) {n m q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 200000000) (hqL : (3251 / 5000 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1057 / 2500 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hLUbig : Real.log n ≤ 40000000000 := by linarith only [hLU]
  let L := Real.log n
  let α : ℝ := 3251 / 5000
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
    by_cases hA : L < 1000000
    · have hbpow : b ≤ 2 ^ 20 := by
        have hx : (b : ℝ) ≤ 2 ^ 20 := by
          norm_num only
          dsimp only [α] at hbhi
          linarith only [hbhi, hA]
        exact_mod_cast hx
      have hu28 : Real.log (b ^ 2 : ℕ) ≤ 28 :=
        mean_log_radius_of_pow (Nat.zero_lt_of_lt (by linarith only [hb] : 1 < b)) hbpow
          (by
            norm_num only [Nat.cast_ofNat]; linarith only [Real.log_two_lt_d9])
      have hB := Nat.pow_le_pow_left hb 2
      obtain ⟨hθB, hθ, hupper⟩ := mean_theta_cell_one hRH hB
      have hgap := short_scalar_gap_one hu0 hu28 hL
      exact
        large_cofactor_of_mean_cells hn ho hm hq hq2 hprod (α := α) (P := 10029 / 10000) (a :=
          9968 / 10000) (η := 993 / 1000) (by norm_num only [α]) (by norm_num only [α])
          (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
          (by norm_num only) (by norm_num only) hb hL0 hLUbig hfloor hτ hqL hul huU
          (by simpa only [Nat.cast_pow] using hθB) (by simpa only [Nat.cast_pow] using hθ)
          (by simpa only [Nat.cast_pow] using hupper) hgap
    · have hL1 : 1000000 ≤ L := le_of_not_gt hA
      by_cases hB : L < 100000000
      · have hb2 : 650000 ≤ b := by
          apply (Nat.le_floor_iff hτ0).mpr
          norm_num only [Nat.cast_ofNat, α]
          linarith only [hL1]
        have hbpow : b ≤ 2 ^ 26 := by
          have hx : (b : ℝ) ≤ 2 ^ 26 := by
            norm_num only
            dsimp only [α] at hbhi
            linarith only [hbhi, hB]
          exact_mod_cast hx
        have hu38 : Real.log (b ^ 2 : ℕ) ≤ 38 :=
          mean_log_radius_of_pow (Nat.zero_lt_of_lt (by linarith only [hb] : 1 < b)) hbpow
            (by
              norm_num only [Nat.cast_ofNat]; linarith only [Real.log_two_lt_d9])
        obtain ⟨hθB, hθ, hupper⟩ := mean_theta_cell_two hRH (Nat.pow_le_pow_left hb2 2)
        have hgap := short_scalar_gap_two hu0 hu38 hL1
        exact
          large_cofactor_of_mean_cells hn ho hm hq hq2 hprod (α := α) (P := 10008 / 10000) (a :=
            9991 / 10000) (η := 9983 / 10000) (by norm_num only [α]) (by norm_num only [α])
            (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
            (by norm_num only) (by norm_num only) hb hL0 hLUbig hfloor hτ hqL hul huU
            (by simpa only [Nat.cast_pow] using hθB) (by simpa only [Nat.cast_pow] using hθ)
            (by simpa only [Nat.cast_pow] using hupper) hgap
      · have hL2 : 100000000 ≤ L := le_of_not_gt hB
        have hb3 : 65000000 ≤ b := by
          apply (Nat.le_floor_iff hτ0).mpr
          norm_num only [Nat.cast_ofNat, α]
          linarith only [hL2]
        obtain ⟨hθB, hθ, hupper⟩ := mean_theta_cell_three hRH (Nat.pow_le_pow_left hb3 2)
        have hbpow : b ≤ 2 ^ 27 := by
          have hx : (b : ℝ) ≤ 2 ^ 27 := by
            norm_num only
            dsimp only [α] at hbhi
            linarith only [hbhi, hLU]
          exact_mod_cast hx
        have hu38 : Real.log (b ^ 2 : ℕ) ≤ 38 :=
          mean_log_radius_of_pow (Nat.zero_lt_of_lt (by linarith only [hb] : 1 < b)) hbpow
            (by
              norm_num only [Nat.cast_ofNat]; linarith only [Real.log_two_lt_d9])
        have hgap := short_scalar_gap_three hu0 hu38 hL2
        exact
          large_cofactor_of_mean_cells hn ho hm hq hq2 hprod (α := α) (P := 100008 / 100000) (a :=
            99992 / 100000) (η := 99984 / 100000) (by norm_num only [α]) (by norm_num only [α])
            (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
            (by norm_num only) (by norm_num only) hb hL0 hLUbig hfloor hτ hqL hul huU
            (by simpa only [Nat.cast_pow] using hθB) (by simpa only [Nat.cast_pow] using hθ)
            (by simpa only [Nat.cast_pow] using hupper) hgap
  obtain ⟨r, hr, hrb, hrnot⟩ := hex
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg b) hbhi 2
  have hrreal : (r : ℝ) ≤ (b : ℝ) ^ 2 := by exact_mod_cast hrb
  have hcoeff : α ^ 2 ≤ (1057 / 2500 : ℝ) := by norm_num only [α]
  have hcoeffL := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg L)
  have he : (α * L) ^ 2 = α ^ 2 * L ^ 2 := mul_pow α L 2
  refine ⟨r, hr, ?_, hrnot⟩
  change (r : ℝ) ≤ (1057 / 2500 : ℝ) * L ^ 2
  rw [he] at hsquare
  exact hrreal.trans (hsquare.trans hcoeffL)



end PseudoPrime.PrimeTestBounds.MillerRabin
