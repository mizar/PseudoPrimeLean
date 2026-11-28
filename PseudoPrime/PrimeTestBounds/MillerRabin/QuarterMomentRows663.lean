/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentAtom663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLogWalk
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentAtom663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663

/-! # Fixed-point row checks for the section 137 Mangoldt moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-power row stores the base and exponent, logarithm bounds at
scale 10^12, the two Taylor shifts, and the lower fifth-root endpoint at
the same scale. The adjacent integer is the upper root endpoint. -/
structure MomentRow663 where
  base : ℕ
  exponent : ℕ
  baseShift : ℕ
  indexShift : ℕ
  baseLo : ℤ
  baseHi : ℤ
  indexLo : ℤ
  indexHi : ℤ
  rootLo : ℕ
  deriving DecidableEq

/-- The integer whose Mangoldt term the row encloses. -/
def MomentRow663.index (r : MomentRow663) : ℕ :=
  r.base ^ r.exponent

private def fixedEndpoint (d : ℤ) : ℚ :=
  (d : ℚ) / 10 ^ 12

private def baseBox (r : MomentRow663) : ℚ × ℚ :=
  (fixedEndpoint r.baseLo, fixedEndpoint r.baseHi)

private def indexBox (r : MomentRow663) : ℚ × ℚ :=
  (fixedEndpoint r.indexLo, fixedEndpoint r.indexHi)

private def rootBox (r : MomentRow663) : ℚ × ℚ :=
  (fixedEndpoint r.rootLo, fixedEndpoint (r.rootLo + 1))

private def checkMomentRoot (n root : ℕ) : Bool :=
  let target := n ^ 3 * (10 ^ 12) ^ 5
  decide (0 < n ∧ root ^ 5 ≤ target ∧ target ≤ (root + 1) ^ 5)

private theorem checked_moment_root {r : MomentRow663}
    (h : checkMomentRoot r.index r.rootLo = true) :
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.index : ℚ)⁻¹ (rootBox r).1
        (rootBox r).2 3 5 =
      true := by
  have h' :
    0 < r.index ∧
      r.rootLo ^ 5 ≤ r.index ^ 3 * (10 ^ 12) ^ 5 ∧
      r.index ^ 3 * (10 ^ 12) ^ 5 ≤ (r.rootLo + 1) ^ 5 :=
    of_decide_eq_true h
  have hn : (0 : ℚ) < r.index := Nat.cast_pos.mpr h'.1
  have hd : (0 : ℚ) < (10 ^ 12) ^ 5 * (r.index : ℚ) ^ 3 := mul_pos (by norm_num only) (pow_pos hn _)
  unfold AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck
  apply decide_eq_true
  refine
    ⟨inv_pos.mpr hn, by
      dsimp only [rootBox, fixedEndpoint]; positivity, by
      dsimp only [rootBox, fixedEndpoint]; positivity, by decide, ?_, ?_⟩
  · simp only [rootBox, fixedEndpoint, Int.cast_natCast, div_pow, inv_pow, ← div_eq_mul_inv,
      div_div]
    apply (div_le_iff₀ hd).mpr
    rw [one_mul, mul_comm]
    exact_mod_cast h'.2.1
  · simp only [rootBox, fixedEndpoint, Int.cast_natCast, Int.cast_add, Int.cast_one, div_pow,
      inv_pow, ← div_eq_mul_inv, div_div]
    apply (le_div_iff₀ hd).mpr
    rw [one_mul, mul_comm]
    exact_mod_cast h'.2.2

/-- Check that a row represents a prime power and that its logarithms and
fifth root are enclosed by the stored integer endpoints. -/
def MomentRow663.check (r : MomentRow663) : Bool :=
  (@decide r.base.Prime (Nat.decidablePrime' r.base) && decide (r.exponent ≠ 0)) &&
    Analysis.rationalLogIntervalCheck r.base r.baseShift 22 (baseBox r).1 (baseBox r).2 &&
    Analysis.rationalLogIntervalCheck r.index r.indexShift 22 (indexBox r).1 (indexBox r).2 &&
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.index : ℚ)⁻¹ (rootBox r).1
      (rootBox r).2 3 5

/-- The lower and upper signed moments of the row, rounded outward to
integers in units of 10^-8 for prefix accumulation. -/
private def MomentRow663.rationalMoment (r : MomentRow663) (j : ℕ) : ℤ × ℤ :=
  let b :=
    momentMulBox (momentMulBox (rootBox r) (baseBox r))
      (momentPowBox (12 - (indexBox r).2, 12 - (indexBox r).1) j)
  (⌊10 ^ 8 * b.1⌋, ⌈10 ^ 8 * b.2⌉)

private def momentNumerators (r : MomentRow663) (j : ℕ) : ℤ × ℤ :=
  momentMulBox (momentMulBox ((r.rootLo : ℤ), (r.rootLo : ℤ) + 1) (r.baseLo, r.baseHi))
    (momentPowBox (12 * 10 ^ 12 - r.indexHi, 12 * 10 ^ 12 - r.indexLo) j)

/-- Compute the outward-rounded, signed moment endpoints by multiplying
integer numerators and dividing by their shared denominator at the end. -/
def MomentRow663.moment (r : MomentRow663) (j : ℕ) : ℤ × ℤ :=
  let b := momentNumerators r j
  let d := ((10 ^ 12 : ℕ) * (10 ^ 12 : ℕ)) * (10 ^ 12 : ℕ) ^ j
  (10 ^ 8 * b.1 / (d : ℤ), -((-(10 ^ 8 * b.2)) / (d : ℤ)))

private theorem moment_center (x : ℤ) :
    12 - fixedEndpoint x = ((12 * 10 ^ 12 - x : ℤ) : ℚ) / (10 ^ 12 : ℕ) := by
  simp only [fixedEndpoint, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow,
    Nat.cast_ofNat, sub_div]
  rw [mul_div_cancel_right₀ _ (by norm_num only : (10 : ℚ) ^ 12 ≠ 0)]

private theorem MomentRow663.moment_eq_rational (r : MomentRow663) (j : ℕ) :
    r.moment j = r.rationalMoment j := by
  have hb : baseBox r = momentScaledBox (r.baseLo, r.baseHi) (10 ^ 12) := by rfl
  have hr : rootBox r = momentScaledBox ((r.rootLo : ℤ), (r.rootLo : ℤ) + 1) (10 ^ 12) := by rfl
  have hc :
    (12 - (indexBox r).2, 12 - (indexBox r).1) =
      momentScaledBox (12 * 10 ^ 12 - r.indexHi, 12 * 10 ^ 12 - r.indexLo) (10 ^ 12) := by
    exact Prod.ext (moment_center r.indexHi) (moment_center r.indexLo)
  have hs : (10 : ℚ) ^ 8 = ((10 ^ 8 : ℤ) : ℚ) := by norm_num only
  rw [MomentRow663.rationalMoment, hb, hr, hc, moment_mul_scaled_box, moment_pow_scaled_box,
    moment_mul_scaled_box]
  simp only [MomentRow663.moment, momentNumerators, momentScaledBox, hs, ← mul_div_assoc,
    ← Int.cast_mul, Rat.floor_intCast_div_natCast, Rat.ceil_intCast_div_natCast]

/-- Certified logarithm intervals and a checked root bound give the real
centered moment enclosure after the rounding used in the cumulative sum. -/
private theorem MomentRow663.sound_from_logs {r : MomentRow663} (hp : r.base.Prime)
    (hk : r.exponent ≠ 0)
    (hP : Real.log (r.base : ℝ) ∈ Set.Icc ((baseBox r).1 : ℝ) ((baseBox r).2 : ℝ))
    (hL : Real.log (r.index : ℝ) ∈ Set.Icc ((indexBox r).1 : ℝ) ((indexBox r).2 : ℝ))
    (hV :
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.index : ℚ)⁻¹ (rootBox r).1
          (rootBox r).2 3 5 =
        true)
    (j : ℕ) :
    (r.index : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt r.index *
        (12 - Real.log r.index) ^ j ∈
      Set.Icc ((r.moment j).1 / (10 ^ 8 : ℝ)) ((r.moment j).2 / (10 ^ 8 : ℝ)) := by
  rw [r.moment_eq_rational]
  have hA :=
    quarter_moment_from_logs_663 hp hk rfl (baseBox r) (indexBox r) (rootBox r) hP hL hV (j := j)
  let b :=
    momentMulBox (momentMulBox (rootBox r) (baseBox r))
      (momentPowBox (12 - (indexBox r).2, 12 - (indexBox r).1) j)
  have hlo := Int.floor_le (10 ^ 8 * b.1)
  have hhi := Int.le_ceil (10 ^ 8 * b.2)
  have hloR := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR := (Rat.cast_le (K := ℝ)).mpr hhi
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast] at hloR hhiR
  change _ ∈ Set.Icc (b.1 : ℝ) (b.2 : ℝ) at hA
  have hpos : (0 : ℝ) < 10 ^ 8 := by norm_num only
  have hl : ((r.rationalMoment j).1 : ℝ) / 10 ^ 8 ≤ (b.1 : ℝ) := by
    change (⌊10 ^ 8 * b.1⌋ : ℝ) / 10 ^ 8 ≤ (b.1 : ℝ)
    exact (div_le_iff₀ hpos).mpr (hloR.trans_eq (mul_comm _ _))
  have hu : (b.2 : ℝ) ≤ ((r.rationalMoment j).2 : ℝ) / 10 ^ 8 := by
    change (b.2 : ℝ) ≤ (⌈10 ^ 8 * b.2⌉ : ℝ) / 10 ^ 8
    exact (le_div_iff₀ hpos).mpr ((mul_comm _ _).le.trans hhiR)
  exact ⟨hl.trans hA.1, hA.2.trans hu⟩

/-- A checked row gives the stated bounds on the real centered moment,
including the fixed-point rounding used in the cumulative sum. -/
theorem MomentRow663.sound {r : MomentRow663} (h : r.check = true) (j : ℕ) :
    (r.index : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt r.index *
        (12 - Real.log r.index) ^ j ∈
      Set.Icc ((r.moment j).1 / (10 ^ 8 : ℝ)) ((r.moment j).2 / (10 ^ 8 : ℝ)) := by
  have hc := Bool.and_eq_true_iff.mp h
  have hL := Bool.and_eq_true_iff.mp hc.1
  have hP := Bool.and_eq_true_iff.mp hL.1
  have hb := Bool.and_eq_true_iff.mp hP.1
  have hp := @of_decide_eq_true r.base.Prime (Nat.decidablePrime' r.base) hb.1
  have hp' := Analysis.rationalLogIntervalCheck_sound hP.2
  have hn' := Analysis.rationalLogIntervalCheck_sound hL.2
  simp only [Rat.cast_natCast] at hp' hn'
  exact MomentRow663.sound_from_logs hp (of_decide_eq_true hb.2) hp' hn' hc.2 j

/-- Check only integer comparisons against the walked log interval. The two
base comparisons account for division by the prime-power exponent. -/
private def MomentRow663.checkWalkEnd (r : MomentRow663) (a : ℕ) (b : ℕ × ℕ) : Bool :=
  (@decide r.base.Prime (Nat.decidablePrime' r.base) && decide (0 < r.exponent)) &&
    decide (a ≤ r.index) &&
    decide (r.indexLo ≤ (b.1 : ℤ) ∧ (b.2 : ℤ) ≤ r.indexHi) &&
    decide (r.baseLo * r.exponent ≤ (b.1 : ℤ) ∧ (b.2 : ℤ) ≤ r.baseHi * r.exponent) &&
    checkMomentRoot r.index r.rootLo

/-- Advance from the anchor and validate the new logarithm and root bounds. -/
def MomentRow663.checkWalk (r : MomentRow663) (a lo hi : ℕ) : Bool :=
  r.checkWalkEnd a (Analysis.logWalk (10 ^ 12) a lo hi (r.index - a))

private theorem fixed_log_box {l u : ℤ} {x : ℝ} (hl : (l : ℝ) ≤ (10 : ℝ) ^ 12 * x)
    (hu : (10 : ℝ) ^ 12 * x ≤ u) : x ∈ Set.Icc (fixedEndpoint l : ℝ) (fixedEndpoint u : ℝ) := by
  have hpos : (0 : ℝ) < 10 ^ 12 := by norm_num only
  simp only [fixedEndpoint, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
  exact
    ⟨(div_le_iff₀ hpos).mpr ((mul_comm _ _).le.trans' hl),
      (le_div_iff₀ hpos).mpr ((mul_comm _ _).ge.trans hu)⟩

/-- Starting with certified scaled logarithm bounds at a positive anchor,
the outward integer walk certifies the row's rounded moment interval. -/
theorem MomentRow663.sound_walk {r : MomentRow663} {a lo hi : ℕ} (ha : 0 < a)
    (hlo : (lo : ℝ) ≤ (10 ^ 12 : ℕ) * Real.log a) (hhi : ((10 ^ 12 : ℕ) : ℝ) * Real.log a ≤ hi)
    (h : r.checkWalk a lo hi = true) (j : ℕ) :
    (r.index : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt r.index *
        (12 - Real.log r.index) ^ j ∈
      Set.Icc ((r.moment j).1 / (10 ^ 8 : ℝ)) ((r.moment j).2 / (10 ^ 8 : ℝ)) := by
  have hc := Bool.and_eq_true_iff.mp h
  have hB := Bool.and_eq_true_iff.mp hc.1
  have hN := Bool.and_eq_true_iff.mp hB.1
  have hA := Bool.and_eq_true_iff.mp hN.1
  have hK := Bool.and_eq_true_iff.mp hA.1
  have hp := @of_decide_eq_true r.base.Prime (Nat.decidablePrime' r.base) hK.1
  have hk : 0 < r.exponent := of_decide_eq_true hK.2
  have he := Nat.add_sub_of_le (of_decide_eq_true hA.2 : a ≤ r.index)
  let b := Analysis.logWalk (10 ^ 12) a lo hi (r.index - a)
  have hN' : r.indexLo ≤ (b.1 : ℤ) ∧ (b.2 : ℤ) ≤ r.indexHi := of_decide_eq_true hN.2
  have hB' : r.baseLo * r.exponent ≤ (b.1 : ℤ) ∧ (b.2 : ℤ) ≤ r.baseHi * r.exponent :=
    of_decide_eq_true hB.2
  have hn := Analysis.logWalk_bounds (10 ^ 12) a lo hi (r.index - a) ha hlo hhi
  rw [he] at hn
  have hb := quarter_log_walk_power ha hk he hlo hhi
  have hkR : (0 : ℝ) < r.exponent := Nat.cast_pos.mpr hk
  have hbl : (r.baseLo : ℝ) ≤ (b.1 : ℝ) / r.exponent :=
    (le_div_iff₀ hkR).mpr (by exact_mod_cast hB'.1)
  have hbu : (b.2 : ℝ) / r.exponent ≤ r.baseHi := (div_le_iff₀ hkR).mpr (by exact_mod_cast hB'.2)
  have hP :
    Real.log (r.base : ℝ) ∈ Set.Icc (fixedEndpoint r.baseLo : ℝ) (fixedEndpoint r.baseHi : ℝ) := by
    apply fixed_log_box <;> simp only [Nat.cast_pow, Nat.cast_ofNat] at hb
    · exact hbl.trans hb.1
    · exact hb.2.trans hbu
  have hL :
    Real.log (r.index : ℝ) ∈
      Set.Icc (fixedEndpoint r.indexLo : ℝ) (fixedEndpoint r.indexHi : ℝ) := by
    apply fixed_log_box <;> simp only [Nat.cast_pow, Nat.cast_ofNat] at hn
    · exact (by exact_mod_cast hN'.1 : (r.indexLo : ℝ) ≤ (b.1 : ℝ)).trans hn.1
    · exact hn.2.trans (by exact_mod_cast hN'.2 : (b.2 : ℝ) ≤ (r.indexHi : ℝ))
  exact MomentRow663.sound_from_logs hp hk.ne' hP hL (checked_moment_root hc.2) j

/-- Validate the ordered rows by advancing from the previous row's index
and carrying its newly computed logarithm interval into the next step. -/
def checkMomentWalk663 : List MomentRow663 → ℕ → ℕ → ℕ → Bool
  | [], _, _, _ => true
  | r :: rs, a, lo, hi =>
    let b := Analysis.logWalk (10 ^ 12) a lo hi (r.index - a)
    r.checkWalkEnd a b && checkMomentWalk663 rs r.index b.1 b.2

private theorem moment_walk_next {r : MomentRow663} {a lo hi : ℕ} (ha : 0 < a)
    (hlo : (lo : ℝ) ≤ (10 ^ 12 : ℕ) * Real.log a) (hhi : ((10 ^ 12 : ℕ) : ℝ) * Real.log a ≤ hi)
    (h : r.checkWalk a lo hi = true) :
    let b := Analysis.logWalk (10 ^ 12) a lo hi (r.index - a)
    0 < r.index ∧
      (b.1 : ℝ) ≤ (10 ^ 12 : ℕ) * Real.log r.index ∧
      ((10 ^ 12 : ℕ) : ℝ) * Real.log r.index ≤ b.2 := by
  have hc := Bool.and_eq_true_iff.mp h
  have hB := Bool.and_eq_true_iff.mp hc.1
  have hN := Bool.and_eq_true_iff.mp hB.1
  have hA := Bool.and_eq_true_iff.mp hN.1
  have hle : a ≤ r.index := of_decide_eq_true hA.2
  have hb := Analysis.logWalk_bounds (10 ^ 12) a lo hi (r.index - a) ha hlo hhi
  rw [Nat.add_sub_of_le hle] at hb
  exact ⟨ha.trans_le hle, hb⟩

private theorem moment_walk_sound {rs : List MomentRow663} {a lo hi : ℕ} (ha : 0 < a)
    (hlo : (lo : ℝ) ≤ (10 ^ 12 : ℕ) * Real.log a) (hhi : ((10 ^ 12 : ℕ) : ℝ) * Real.log a ≤ hi)
    (h : checkMomentWalk663 rs a lo hi = true) (j : ℕ) (r : MomentRow663) (hr : r ∈ rs) :
    (r.index : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt r.index *
        (12 - Real.log r.index) ^ j ∈
      Set.Icc ((r.moment j).1 / (10 ^ 8 : ℝ)) ((r.moment j).2 / (10 ^ 8 : ℝ)) := by
  induction rs generalizing a lo hi with
  | nil => exact (List.not_mem_nil hr).elim
  | cons head tail ih =>
    let b := Analysis.logWalk (10 ^ 12) a lo hi (head.index - a)
    change (head.checkWalk a lo hi && checkMomentWalk663 tail head.index b.1 b.2) = true at h
    have hc := Bool.and_eq_true_iff.mp h
    rcases List.mem_cons.mp hr with he | he
    · exact he ▸ MomentRow663.sound_walk ha hlo hhi hc.1 j
    · have hn := moment_walk_next ha hlo hhi hc.1
      exact ih hn.1 hn.2.1 hn.2.2 hc.2 he

/-- Distinct rows with certified intervals that cover the prime powers
enclose the full moment between the sums of their endpoints. -/
private theorem quarter_row_sum_663 {L U j : ℕ} (hLU : L ≤ U) (rows : Finset MomentRow663)
    (hc :
      ∀ r ∈ rows,
        (r.index : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt r.index *
            (12 - Real.log r.index) ^ j ∈
          Set.Icc ((r.moment j).1 / (10 ^ 8 : ℝ)) ((r.moment j).2 / (10 ^ 8 : ℝ)))
    (hs : ∀ n, n ∈ rows.image MomentRow663.index ↔ n ∈ Finset.Ioc L U ∧ IsPrimePow n)
    (hi : (rows.image MomentRow663.index).card = rows.card) :
    quarterMangoldtPrefix663 U j - quarterMangoldtPrefix663 L j ∈
      Set.Icc ((↑(∑ r ∈ rows, (r.moment j).1) : ℝ) / 10 ^ 8)
        ((↑(∑ r ∈ rows, (r.moment j).2) : ℝ) / 10 ^ 8) := by
  let f := fun n : ℕ ↦
    (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j
  have hsub : rows.image MomentRow663.index ⊆ Finset.Ioc L U := fun n hn ↦ ((hs n).mp hn).1
  have hzero (n : ℕ) (hn : n ∈ Finset.Ioc L U) (hn' : n ∉ rows.image MomentRow663.index) :
    f n = 0 := by
    have hnp : ¬IsPrimePow n := by
      intro hp
      exact hn' ((hs n).mpr ⟨hn, hp⟩)
    simp only [f, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp, mul_zero, zero_mul]
  have hsum := Finset.sum_subset hsub hzero
  have hinj := Finset.injOn_of_card_image_eq hi
  rw [Finset.sum_image (fun _ ha _ hb h ↦ hinj ha hb h)] at hsum
  rw [← mangoldt_moment_window hLU j, ← hsum]
  simp only [Int.cast_sum, Finset.sum_div]
  exact ⟨Finset.sum_le_sum fun r hr ↦ (hc r hr).1, Finset.sum_le_sum fun r hr ↦ (hc r hr).2⟩

/-- Checked, distinct rows that cover the prime powers enclose the full moment. -/
theorem quarter_checked_row_sum_663 {L U j : ℕ} (hLU : L ≤ U) (rows : Finset MomentRow663)
    (hc : ∀ r ∈ rows, r.check = true)
    (hs : ∀ n, n ∈ rows.image MomentRow663.index ↔ n ∈ Finset.Ioc L U ∧ IsPrimePow n)
    (hi : (rows.image MomentRow663.index).card = rows.card) :
    quarterMangoldtPrefix663 U j - quarterMangoldtPrefix663 L j ∈
      Set.Icc ((↑(∑ r ∈ rows, (r.moment j).1) : ℝ) / 10 ^ 8)
        ((↑(∑ r ∈ rows, (r.moment j).2) : ℝ) / 10 ^ 8) := by
  exact quarter_row_sum_663 hLU rows (fun r hr ↦ MomentRow663.sound (hc r hr) j) hs hi

/-- Match each part of the row support against the computed prime and
proper-power index lists before summing the fixed-point intervals. -/
theorem quarter_sieved_row_sum_663 {L U j : ℕ} (hLU : L ≤ U) (hU : U ≤ 1517026)
    (rows : Finset MomentRow663) (hc : ∀ r ∈ rows, r.check = true) (P Q : List ℕ)
    (hp : quarterSievePrimeIndices663 L U = P) (hq : quarterProperPowers663 L U = Q)
    (hs : rows.image MomentRow663.index = (P ++ Q).toFinset)
    (hi : (rows.image MomentRow663.index).card = rows.card) :
    quarterMangoldtPrefix663 U j - quarterMangoldtPrefix663 L j ∈
      Set.Icc ((↑(∑ r ∈ rows, (r.moment j).1) : ℝ) / 10 ^ 8)
        ((↑(∑ r ∈ rows, (r.moment j).2) : ℝ) / 10 ^ 8) := by
  refine quarter_checked_row_sum_663 hLU rows hc (fun n ↦ ?_) hi
  rw [hs, List.mem_toFinset, ← hp, ← hq, quarter_power_indices_iff_663 hU]

/-- Insert one proper prime power into the ordered prime-power indices.
The recursion exposes each comparison to closed kernel evaluation. -/
@[expose]
def insertQuarterPower (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: tail => if a ≤ b then a :: b :: tail else b :: insertQuarterPower a tail

private theorem insert_quarter_power_eq (a : ℕ) (P : List ℕ) :
    insertQuarterPower a P = List.orderedInsert (· ≤ ·) a P := by
  induction P with
  | nil => simp only [insertQuarterPower, List.orderedInsert_nil]
  | cons b tail ih => rw [insertQuarterPower, List.orderedInsert_cons, ih]

private theorem mem_insert_powers {n : ℕ} (P Q : List ℕ) :
    n ∈ Q.foldr insertQuarterPower P ↔ n ∈ P ++ Q := by
  induction Q with
  | nil => simp only [List.foldr_nil, List.append_nil]
  | cons a tail
    ih =>
    rw [List.foldr_cons, insert_quarter_power_eq, (List.perm_orderedInsert (· ≤ ·) _ _).mem_iff,
      List.mem_cons, ih, List.mem_append, List.mem_append, List.mem_cons]
    exact or_left_comm

/-- Certify a finite moment sum by sweeping the sorted prime-power rows
once and matching their support against the sieve and proper powers. -/
theorem quarter_moment_walk_sum_663 {L U lo hi j : ℕ} (hLU : L ≤ U) (hU : U ≤ 1517026) (ha : 0 < L)
    (hlo : (lo : ℝ) ≤ (10 ^ 12 : ℕ) * Real.log L) (hhi : ((10 ^ 12 : ℕ) : ℝ) * Real.log L ≤ hi)
    (rs : List MomentRow663) (hc : checkMomentWalk663 rs L lo hi = true)
    (hn : (rs.map MomentRow663.index).IsChain (· < ·)) (P Q : List ℕ)
    (hp : quarterSievePrimeIndices663 L U = P) (hq : quarterProperPowers663 L U = Q)
    (hs : rs.map MomentRow663.index = Q.foldr insertQuarterPower P) :
    quarterMangoldtPrefix663 U j - quarterMangoldtPrefix663 L j ∈
      Set.Icc ((((rs.map (fun r ↦ (r.moment j).1)).sum : ℤ) : ℝ) / 10 ^ 8)
        ((((rs.map (fun r ↦ (r.moment j).2)).sum : ℤ) : ℝ) / 10 ^ 8) := by
  have hn' := hn.sortedLT.nodup
  have hr := List.Nodup.of_map MomentRow663.index hn'
  have hi' : (rs.toFinset.image MomentRow663.index).card = rs.toFinset.card := by
    rw [← List.toFinset_map, List.toFinset_card_of_nodup hn', List.toFinset_card_of_nodup hr,
      List.length_map]
  rw [← List.sum_toFinset (fun r ↦ (r.moment j).1) hr, ←
    List.sum_toFinset (fun r ↦ (r.moment j).2) hr]
  refine
    quarter_row_sum_663 hLU rs.toFinset
      (fun r hr ↦ moment_walk_sound ha hlo hhi hc j r (List.mem_toFinset.mp hr)) (fun n ↦ ?_) hi'
  rw [← List.toFinset_map, List.mem_toFinset, hs, mem_insert_powers, ← hp, ← hq,
    quarter_power_indices_iff_663 hU]

/-- Adjacent certified windows combine by adding their integer endpoints.
The intermediate cumulative moment cancels, even for signed odd moments. -/
theorem quarter_moment_join_663 {L M U j : ℕ} {a b c d : ℤ}
    (h₁ :
      quarterMangoldtPrefix663 M j - quarterMangoldtPrefix663 L j ∈
        Set.Icc ((a : ℝ) / 10 ^ 8) ((b : ℝ) / 10 ^ 8))
    (h₂ :
      quarterMangoldtPrefix663 U j - quarterMangoldtPrefix663 M j ∈
        Set.Icc ((c : ℝ) / 10 ^ 8) ((d : ℝ) / 10 ^ 8)) :
    quarterMangoldtPrefix663 U j - quarterMangoldtPrefix663 L j ∈
      Set.Icc (((a + c : ℤ) : ℝ) / 10 ^ 8) (((b + d : ℤ) : ℝ) / 10 ^ 8) := by
  simp only [Set.mem_Icc, Int.cast_add, add_div]
  exact ⟨by linarith only [h₁.1, h₂.1], by linarith only [h₁.2, h₂.2]⟩

/-- A bounded portion of a checked block reuses the row enclosures and
inherits exact prime-power coverage by filtering the integer indices. -/
theorem quarter_checked_row_slice_663 {L U a b j : ℕ} (hLa : L ≤ a) (hab : a ≤ b) (hbU : b ≤ U)
    (rows : Finset MomentRow663) (hc : ∀ r ∈ rows, r.check = true)
    (hs : ∀ n, n ∈ rows.image MomentRow663.index ↔ n ∈ Finset.Ioc L U ∧ IsPrimePow n)
    (hi : (rows.image MomentRow663.index).card = rows.card) :
    let slice := rows.filter (fun r ↦ r.index ∈ Finset.Ioc a b)
    quarterMangoldtPrefix663 b j - quarterMangoldtPrefix663 a j ∈
      Set.Icc ((↑(∑ r ∈ slice, (r.moment j).1) : ℝ) / 10 ^ 8)
        ((↑(∑ r ∈ slice, (r.moment j).2) : ℝ) / 10 ^ 8) := by
  intro slice
  have h₀ : slice ⊆ rows := Finset.filter_subset _ _
  have hinj := (Finset.injOn_of_card_image_eq hi).mono (Finset.coe_subset.mpr h₀)
  refine
    quarter_checked_row_sum_663 hab slice (fun r hr ↦ hc r (h₀ hr)) ?_
      (Finset.card_image_of_injOn hinj)
  intro n
  constructor
  · intro hn
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨(Finset.mem_filter.mp hr).2, ((hs r.index).mp (Finset.mem_image.mpr ⟨r, h₀ hr, rfl⟩)).2⟩
  · intro hn
    have hmem := Finset.Ioc_subset_Ioc hLa hbU hn.1
    obtain ⟨r, hr, hrn⟩ := Finset.mem_image.mp ((hs n).mpr ⟨hmem, hn.2⟩)
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hrn ▸ hn.1⟩, hrn⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
