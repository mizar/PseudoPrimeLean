/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import PseudoPrime.Analysis.LogPowerIntegralBounds

/-!
# Integer series for quadratic decay and logarithmic height errors

A shifted p-series controls logarithmic quadratic weights. Finite tail estimates and
integer-bin denominator comparisons support uniform bounds for sums indexed by heights.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For x >= 0, a logarithmic quadratic-decay weight is bounded by ten times the
shifted three-halves power weight. Bound the logarithm by a square root and compare the
quadratic denominators. This explicit majorant proves summability of logarithmic height errors. -/
theorem logWeighted_quadratic_le_rpow {x : ℝ} (hx : 0 ≤ x) :
    (Real.log (4 + x) + 1) / (1 + x ^ 2) ≤ 10 / (1 + x) ^ (3 / 2 : ℝ) := by
  have hy : 0 < 1 + x := by linarith only [hx]
  have hd : 0 < 1 + x ^ 2 := by nlinarith only [sq_nonneg x]
  have hsq := Real.sq_sqrt hy.le
  have hsq4 := Real.sq_sqrt (show 0 ≤ 4 + x by linarith only [hx])
  have hs0 := Real.sqrt_nonneg (1 + x)
  have ht0 := Real.sqrt_nonneg (4 + x)
  have hs1 : 1 ≤ Real.sqrt (1 + x) := by nlinarith only [hsq, hs0, hx]
  have hroot : Real.sqrt (4 + x) ≤ 2 * Real.sqrt (1 + x) := by
    nlinarith only [hsq, hsq4, hs0, ht0, hx]
  have hl :=
    Real.log_le_rpow_div (show 0 ≤ 4 + x by linarith only [hx])
      (show (0 : ℝ) < 1 / 2 by norm_num only)
  rw [← Real.sqrt_eq_rpow] at hl
  have hn : Real.log (4 + x) + 1 ≤ 5 * Real.sqrt (1 + x) := by linarith only [hl, hroot, hs1]
  have hden : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith only [sq_nonneg (x - 1)]
  have hp : 0 < (1 + x) ^ 2 := pow_pos hy 2
  have hr : Real.sqrt (1 + x) / (1 + x) ^ 2 = 1 / (1 + x) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub hy,
      show (1 / 2 : ℝ) - 2 = -(3 / 2 : ℝ) by norm_num only, Real.rpow_neg hy.le, one_div]
  calc
    _ ≤ (5 * Real.sqrt (1 + x)) / (1 + x ^ 2) := div_le_div_of_nonneg_right hn hd.le
    _ ≤ (10 * Real.sqrt (1 + x)) / (1 + x) ^ 2 := by
      rw [div_le_div_iff₀ hd hp]
      have hm := mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5) hs0)
      nlinarith only [hm]
    _ = _ := by rw [mul_div_assoc, hr, ← mul_div_assoc, mul_one]

/-- For p > 1, the shifted absolute p-series over integers converges.
Split into nonnegative and negative integer indices and apply the shifted natural p-series.
This provides a positive majorant without a singular term at zero. -/
theorem summable_int_shifted_abs_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℤ ↦ 1 / (1 + |(k : ℝ)|) ^ p) := by
  have hn := (Real.summable_one_div_nat_add_rpow 1 p).mpr hp
  have hnat : Summable (fun n : ℕ ↦ 1 / (1 + (n : ℝ)) ^ p) :=
    hn.congr
      (fun n ↦ by
        rw [abs_of_nonneg
            (show 0 ≤ (n : ℝ) + 1 by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]),
          add_comm])
  have hnabs : ∀ n : ℕ, |(n : ℝ)| = (n : ℝ) := fun n ↦ abs_of_nonneg (Nat.cast_nonneg n)
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa only [Int.cast_natCast, hnabs] using hnat
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, hnabs] using hnat

/-- The integer series with numerator log(4+|k|)+1 and denominator 1+k^2 is summable.
The explicit three-halves power majorant and positivity give absolute convergence.
Its total sum supplies a conductor-independent error in zero-mass tail bounds. -/
theorem summable_int_logWeighted_quadratic :
    Summable (fun k : ℤ ↦ (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)) := by
  apply
    Summable.of_norm_bounded
      ((summable_int_shifted_abs_rpow (show (1 : ℝ) < 3 / 2 by norm_num only)).mul_left 10)
  intro k
  have hl0 : 0 ≤ Real.log (4 + |(k : ℝ)|) :=
    Real.log_nonneg (show 1 ≤ 4 + |(k : ℝ)| by linarith only [abs_nonneg (k : ℝ)])
  have hn : 0 ≤ (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2) :=
    div_nonneg (by linarith only [hl0]) (by nlinarith only [sq_nonneg (k : ℝ)])
  rw [Real.norm_eq_abs, abs_of_nonneg hn, ← sq_abs]
  simpa only [← mul_div_assoc, mul_one] using logWeighted_quadratic_le_rpow (abs_nonneg (k : ℝ))

/-- The integer inverse-quadratic series is summable.
Compare it with the nonnegative summable logarithmic quadratic weight.
This is the conductor coefficient in finite height-bin estimates. -/
theorem summable_int_quadratic : Summable (fun k : ℤ ↦ 1 / (1 + (k : ℝ) ^ 2)) := by
  apply
    Summable.of_nonneg_of_le
      (fun k ↦ div_nonneg zero_le_one (by nlinarith only [sq_nonneg (k : ℝ)])) (fun k ↦ ?_)
      summable_int_logWeighted_quadratic
  have hl : 0 ≤ Real.log (4 + |(k : ℝ)|) := Real.log_nonneg (by linarith only [abs_nonneg (k : ℝ)])
  exact div_le_div_of_nonneg_right (by linarith only [hl]) (by nlinarith only [sq_nonneg (k : ℝ)])

/-- The natural inverse-quadratic tail is bounded by its improper integral.
Compare the decreasing function x^(-2) with the shifted natural sum. This gives the
conductor coefficient needed for a quantitative integer-height tail. -/
theorem tsum_nat_inverse_quadratic_tail_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-(2 : ℝ))) (Set.Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNr.trans_le hx) hxy (by norm_num only)
  have hi := integrableOn_Ioi_rpow_of_lt (a := -(2 : ℝ)) (by norm_num only : (-(2 : ℝ)) < -1) hNr
  have htail :=
    hanti.tsum_comp_add_le_integral N hi
      (fun x hx ↦ Real.rpow_nonneg (le_of_lt (hNr.trans (Set.mem_Ioi.mp hx))) (-(2 : ℝ)))
  rw [integral_Ioi_rpow_of_lt (a := -(2 : ℝ)) (by norm_num only : (-(2 : ℝ)) < -1) hNr] at htail
  norm_num only at htail
  calc
    _ ≤ -(N : ℝ) ^ (-(1 : ℝ)) / -1 := htail
    _ = 1 / N := by
      rw [Real.rpow_neg_one]
      field_simp [ne_of_gt hNr]

/-- Above x >= 4, shift the logarithm by four and replace the quadratic denominator
with a constant multiple of the shifted inverse-square kernel. This prepares the explicit
logarithmic tail estimate for positive and negative integer heights. -/
theorem logWeighted_quadratic_le_shifted_rpow {x : ℝ} (hx : 2 ≤ x) :
    (Real.log (4 + x) + 1) / (1 + x ^ 2) ≤ 8 * ((Real.log (4 + x) + 1) * (4 + x) ^ (-(2 : ℝ))) := by
  have hnum : 0 ≤ Real.log (4 + x) + 1 := by
    linarith only [Real.log_nonneg (show 1 ≤ 4 + x by linarith only [hx])]
  have hden : 0 < 1 + x ^ 2 := by nlinarith only [sq_nonneg x]
  have hshift : 0 < 4 + x := by linarith only [hx]
  have hcmp : (4 + x) ^ 2 ≤ 8 * (1 + x ^ 2) := by nlinarith only [sq_nonneg (x - 2), hx]
  have hfrac : 1 / (1 + x ^ 2) ≤ 8 / (4 + x) ^ 2 := by
    rw [div_le_div_iff₀ hden (pow_pos hshift 2)]
    nlinarith only [hcmp]
  have hrpow : (4 + x) ^ (-(2 : ℝ)) = 1 / (4 + x) ^ 2 := by
    calc
      (4 + x) ^ (-(2 : ℝ)) = ((4 + x) ^ (2 : ℝ))⁻¹ := Real.rpow_neg (le_of_lt hshift) (2 : ℝ)
      _ = ((4 + x) ^ (2 : ℕ))⁻¹ := congrArg (fun z : ℝ ↦ z⁻¹) (Real.rpow_natCast (4 + x) 2)
      _ = 1 / (4 + x) ^ 2 := by rw [one_div]
  calc
    _ = (Real.log (4 + x) + 1) * (1 / (1 + x ^ 2)) := by ring
    _ ≤ (Real.log (4 + x) + 1) * (8 / (4 + x) ^ 2) := mul_le_mul_of_nonneg_left hfrac hnum
    _ = 8 * ((Real.log (4 + x) + 1) * (4 + x) ^ (-(2 : ℝ))) := by
      rw [hrpow]
      ring

/-- The natural logarithmic quadratic tail is bounded by a shifted integral envelope.
Compare each term with the logarithmic inverse-square kernel and apply its explicit
integral tail estimate. This controls one side of the integer-height tail. -/
theorem tsum_nat_logWeighted_quadratic_tail_le (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : ℕ, (Real.log (4 + ((n + N : ℕ) : ℝ)) + 1) / (1 + ((n + N : ℕ) : ℝ) ^ 2)) ≤
      8 * (Real.log ((N + 3 : ℕ) : ℝ) + 2) / (N + 3) := by
  let f : ℕ → ℝ := fun n ↦ (Real.log (4 + ((n + N : ℕ) : ℝ)) + 1) / (1 + ((n + N : ℕ) : ℝ) ^ 2)
  let g : ℕ → ℝ := fun n ↦
    (Real.log (4 + ((n + N : ℕ) : ℝ)) + 1) * (4 + ((n + N : ℕ) : ℝ)) ^ (-(2 : ℝ))
  have hbase := summable_logPower_envelope (r := (1 : ℝ)) (by norm_num only)
  have hshift := (summable_nat_add_iff (N + 4)).2 hbase
  have hsumg : Summable g := by
    convert hshift using 1
    ext n
    have heq : 4 + ((n + N : ℕ) : ℝ) = ((n + (N + 4) : ℕ) : ℝ) := by
      push_cast
      ring
    unfold g
    rw [heq, show (-(1 : ℝ) - 1) = -(2 : ℝ) by norm_num only]
  have hpoint : ∀ n : ℕ, f n ≤ 8 * g n := by
    intro n
    change
      (Real.log (4 + ((n + N : ℕ) : ℝ)) + 1) / (1 + ((n + N : ℕ) : ℝ) ^ 2) ≤
        8 * ((Real.log (4 + ((n + N : ℕ) : ℝ)) + 1) * (4 + ((n + N : ℕ) : ℝ)) ^ (-(2 : ℝ)))
    have hn : (2 : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast le_trans hN (Nat.le_add_left N n)
    exact logWeighted_quadratic_le_shifted_rpow hn
  have hsumf : Summable f := by
    apply Summable.of_nonneg_of_le
    · intro n
      have hn0 : (0 : ℝ) ≤ ((n + N : ℕ) : ℝ) := Nat.cast_nonneg (n + N)
      have hlog := Real.log_nonneg (show 1 ≤ 4 + ((n + N : ℕ) : ℝ) by linarith only [hn0])
      have hden : 0 < 1 + ((n + N : ℕ) : ℝ) ^ 2 := by nlinarith only [sq_nonneg ((n + N : ℕ) : ℝ)]
      exact div_nonneg (by linarith only [hlog]) hden.le
    · exact hpoint
    · exact hsumg.mul_left 8
  have hle := Summable.tsum_le_tsum hpoint hsumf (hsumg.mul_left 8)
  have htail := tsum_logPower_envelope_tail_le (N + 3) (by omega)
  have htailg : (∑' n : ℕ, g n) ≤ (Real.log ((N + 3 : ℕ) : ℝ) + 2) / (N + 3) := by
    calc
      ∑' n : ℕ, g n =
          ∑' n : ℕ,
            (Real.log ((n + (N + 3) + 1 : ℕ) : ℝ) + 1) * ((n + (N + 3) + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) :=
        by
        apply tsum_congr
        intro n
        have heq : 4 + ((n + N : ℕ) : ℝ) = ((n + (N + 3) + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        unfold g
        rw [heq]
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_ofNat] using htail
  calc
    ∑' n : ℕ, f n ≤ ∑' n : ℕ, 8 * g n := hle
    _ = 8 * (∑' n : ℕ, g n) := tsum_mul_left
    _ ≤ 8 * ((Real.log ((N + 3 : ℕ) : ℝ) + 2) / (N + 3)) :=
      mul_le_mul_of_nonneg_left htailg (by norm_num only)
    _ = _ := by ring_nf

/-- The two-sided integer logarithmic quadratic tail has an explicit integral bound.
Split the integer series into its nonnegative and negative indices, use evenness, and
remove the initial segment below the cutoff. This supplies the logarithmic part of the
quantitative height-bin tail. -/
theorem tsum_int_logWeighted_quadratic_tail_le (H : ℕ) (hH : 2 ≤ H) :
    (∑' k : ℤ, if H ≤ k.natAbs then (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2) else 0) ≤
      16 * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := by
  let w : ℤ → ℝ := fun k ↦ (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)
  let tail : ℤ → ℝ := fun k ↦ if H ≤ k.natAbs then w k else 0
  have hwn : ∀ k : ℤ, 0 ≤ w k := by
    intro k
    dsimp only [w]
    have hlog := Real.log_nonneg (show 1 ≤ 4 + |(k : ℝ)| by linarith only [abs_nonneg (k : ℝ)])
    exact div_nonneg (by linarith only [hlog]) (by nlinarith only [sq_nonneg (k : ℝ)])
  have hw : Summable w := summable_int_logWeighted_quadratic
  have htail : Summable tail := by
    apply Summable.of_nonneg_of_le
    · intro k
      dsimp only [tail]
      split_ifs
      · exact hwn k
      · exact le_rfl
    · intro k
      dsimp only [tail]
      split_ifs
      · exact le_rfl
      · exact hwn k
    · exact hw
  have heven : Function.Even tail := by
    intro k
    simp only [tail, Int.natAbs_neg]
    have hwneg : w (-k) = w k := by
      dsimp only [w]
      simp only [Int.cast_neg, abs_neg, neg_sq]
    rw [hwneg]
  have hnat : Summable (fun n : ℕ ↦ tail n) := htail.comp_injective Nat.cast_injective
  have hzero : tail 0 = 0 := by
    dsimp only [tail]
    have hnot : ¬H ≤ (0 : ℤ).natAbs := by
      norm_num only [Int.natAbs_zero]; omega
    change (if H ≤ (0 : ℤ).natAbs then w 0 else 0) = 0
    rw [ite_eq_right hnot]
  have hsumSplit := hnat.sum_add_tsum_nat_add H
  have hfin : (∑ i ∈ Finset.range H, tail i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    dsimp only [tail]
    have hnot : ¬H ≤ (i : ℤ).natAbs := by
      simpa only [Int.natAbs_natCast] using (show ¬H ≤ i by omega)
    change (if H ≤ (i : ℤ).natAbs then w i else 0) = 0
    rw [ite_eq_right hnot]
  have hshift :
    (∑' n : ℕ, tail (n + H)) =
      (∑' n : ℕ, (Real.log (4 + ((n + H : ℕ) : ℝ)) + 1) / (1 + ((n + H : ℕ) : ℝ) ^ 2)) := by
    apply tsum_congr
    intro n
    have hn : H ≤ n + H := Nat.le_add_left H n
    have hcast : (n : ℤ) + H = (n + H : ℕ) := (Nat.cast_add n H).symm
    rw [hcast]
    have hn' : H ≤ ((n + H : ℕ) : ℤ).natAbs := by simpa only [Int.natAbs_natCast] using hn
    change (if H ≤ ((n + H : ℕ) : ℤ).natAbs then w ((n + H : ℕ) : ℤ) else 0) = _
    rw [ite_eq_left hn']
    have hreal : (0 : ℝ) ≤ ((n + H : ℕ) : ℝ) := Nat.cast_nonneg (n + H)
    dsimp only [w]
    rw [Int.cast_natCast, abs_of_nonneg hreal]
  have htailNat := tsum_nat_logWeighted_quadratic_tail_le H hH
  have hnatBound : (∑' n : ℕ, tail n) ≤ 8 * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := by
    calc
      ∑' n : ℕ, tail n = ∑' n : ℕ, tail (n + H) := by
        rw [hfin, zero_add] at hsumSplit
        exact hsumSplit.symm
      _ = ∑' n : ℕ, (Real.log (4 + ((n + H : ℕ) : ℝ)) + 1) / (1 + ((n + H : ℕ) : ℝ) ^ 2) := hshift
      _ ≤ _ := htailNat
  have hshift1 := hnat.sum_add_tsum_nat_add 1
  have hnatShift : (∑' n : ℕ, tail (n + 1)) = ∑' n : ℕ, tail n := by
    have hzeroNat : tail (0 : ℕ) = 0 := hzero
    have hfin1 : (∑ i ∈ Finset.range 1, tail i) = 0 := by
      simpa only [Finset.sum_range_one] using hzeroNat
    rw [hfin1, zero_add] at hshift1
    exact hshift1
  have hneg : Summable (fun n : ℕ ↦ tail (Int.negSucc n)) :=
    htail.comp_injective (fun _ _ h ↦ Int.negSucc.inj h)
  have hIntEq : (∑' k : ℤ, tail k) = 2 * (∑' n : ℕ, tail n) := by
    rw [← tsum_nat_add_neg_add_one htail]
    calc
      (∑' n : ℕ, (tail n + tail (Int.negSucc n))) =
          (∑' n : ℕ, tail n) + (∑' n : ℕ, tail (Int.negSucc n)) :=
        hnat.tsum_add hneg
      _ = (∑' n : ℕ, tail n) + (∑' n : ℕ, tail (n + 1)) := by
        apply congrArg (fun x : ℝ ↦ (∑' n : ℕ, tail n) + x)
        apply tsum_congr
        intro n
        change tail (-(n + 1 : ℤ)) = tail (n + 1 : ℤ)
        exact heven (n + 1 : ℤ)
      _ = 2 * (∑' n : ℕ, tail n) := by
        rw [hnatShift]; ring
  change (∑' k : ℤ, tail k) ≤ _
  rw [hIntEq]
  calc
    2 * (∑' n : ℕ, tail n) ≤ 2 * (8 * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3)) :=
      mul_le_mul_of_nonneg_left hnatBound (by norm_num only)
    _ = _ := by ring_nf

/-- The one-sided natural inverse-quadratic tail starting at height H is bounded by
the integral tail 1/(H-1). Shift the existing integral comparison by one index and use
1/(1+x^2) <= 1/x^2. This supplies the conductor part of the completed-zero tail. -/
theorem tsum_nat_inverse_quadratic_shift_tail_le (H : ℕ) (hH : 2 ≤ H) :
    (∑' n : ℕ, 1 / (1 + ((n + H : ℕ) : ℝ) ^ 2)) ≤ 1 / ((H - 1 : ℕ) : ℝ) := by
  have hshiftBase :=
    (Real.summable_one_div_nat_add_rpow (H : ℝ) 2).mpr (by norm_num only : (1 : ℝ) < 2)
  have hshiftSummable : Summable (fun n : ℕ ↦ 1 / (((n + H : ℕ) : ℝ) ^ (2 : ℕ))) := by
    apply hshiftBase.congr
    intro n
    have hx : (0 : ℝ) ≤ (n : ℝ) + H := by positivity
    rw [abs_of_nonneg hx]
    push_cast
    exact congrArg (fun z : ℝ => 1 / z) (Real.rpow_natCast ((n : ℝ) + H) 2)
  have hpoint : ∀ n : ℕ, 1 / (1 + ((n + H : ℕ) : ℝ) ^ 2) ≤ 1 / (((n + H : ℕ) : ℝ) ^ (2 : ℕ)) := by
    intro n
    have hx : 0 < ((n + H : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity) (pow_pos hx 2)]
    nlinarith only [sq_nonneg ((n + H : ℕ) : ℝ)]
  have hsum :=
    Summable.tsum_le_tsum hpoint
      (Summable.of_nonneg_of_le (fun n ↦ div_nonneg zero_le_one (by positivity)) hpoint
        hshiftSummable)
      hshiftSummable
  have htail := tsum_nat_inverse_quadratic_tail_le (H - 1) (by omega)
  have htail' : (∑' n : ℕ, 1 / (((n + H : ℕ) : ℝ) ^ (2 : ℕ))) ≤ 1 / ((H - 1 : ℕ) : ℝ) := by
    have heq :
      ∀ n : ℕ, 1 / (((n + H : ℕ) : ℝ) ^ (2 : ℕ)) = ((n + (H - 1) + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
      intro n
      have hn : n + H = n + (H - 1) + 1 := by omega
      rw [hn]
      have hx : (0 : ℝ) < ((n + (H - 1) + 1 : ℕ) : ℝ) := by positivity
      rw [Real.rpow_neg (le_of_lt hx) (2 : ℝ)]
      rw [one_div]
      exact (congrArg Inv.inv (Real.rpow_natCast _ 2)).symm
    calc
      (∑' n : ℕ, 1 / (((n + H : ℕ) : ℝ) ^ (2 : ℕ))) =
          ∑' n : ℕ, ((n + (H - 1) + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) :=
        tsum_congr heq
      _ ≤ 1 / ((H - 1 : ℕ) : ℝ) := htail
  calc
    ∑' n : ℕ, 1 / (1 + ((n + H : ℕ) : ℝ) ^ 2) ≤ ∑' n : ℕ, 1 / (((n + H : ℕ) : ℝ) ^ (2 : ℕ)) := hsum
    _ ≤ _ := htail'

/-- The two-sided integer inverse-quadratic tail is at most 2/(H-1). Split into
nonnegative and negative indices, use evenness, and shift away the zero initial segment.
Together with the logarithmic tail this gives the explicit integer height-bin majorant. -/
theorem tsum_int_inverse_quadratic_tail_le (H : ℕ) (hH : 2 ≤ H) :
    (∑' k : ℤ, if H ≤ k.natAbs then 1 / (1 + (k : ℝ) ^ 2) else 0) ≤ 2 / ((H - 1 : ℕ) : ℝ) := by
  let w : ℤ → ℝ := fun k ↦ 1 / (1 + (k : ℝ) ^ 2)
  let tail : ℤ → ℝ := fun k ↦ if H ≤ k.natAbs then w k else 0
  have hwn : ∀ k : ℤ, 0 ≤ w k := by
    intro k
    dsimp only [w]
    exact div_nonneg zero_le_one (by nlinarith only [sq_nonneg (k : ℝ)])
  have hw : Summable w := summable_int_quadratic
  have htail : Summable tail := by
    apply Summable.of_nonneg_of_le
    · intro k
      dsimp only [tail]
      split_ifs
      · exact hwn k
      · exact le_rfl
    · intro k
      dsimp only [tail]
      split_ifs
      · exact le_rfl
      · exact hwn k
    · exact hw
  have heven : Function.Even tail := by
    intro k
    simp only [tail, Int.natAbs_neg]
    have hwneg : w (-k) = w k := by
      dsimp only [w]
      simp only [Int.cast_neg, neg_sq]
    rw [hwneg]
  have hnat : Summable (fun n : ℕ ↦ tail n) := htail.comp_injective Nat.cast_injective
  have hzero : tail 0 = 0 := by
    dsimp only [tail]
    have hnot : ¬H ≤ (0 : ℤ).natAbs := by
      norm_num only [Int.natAbs_zero]; omega
    change (if H ≤ (0 : ℤ).natAbs then w 0 else 0) = 0
    rw [ite_eq_right hnot]
  have hsumSplit := hnat.sum_add_tsum_nat_add H
  have hfin : (∑ i ∈ Finset.range H, tail i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    dsimp only [tail]
    have hnot : ¬H ≤ (i : ℤ).natAbs := by
      simpa only [Int.natAbs_natCast] using (show ¬H ≤ i by omega)
    change (if H ≤ (i : ℤ).natAbs then w i else 0) = 0
    rw [ite_eq_right hnot]
  have hnatShiftBound : (∑' n : ℕ, 1 / (1 + ((n + H : ℕ) : ℝ) ^ 2)) ≤ 1 / ((H - 1 : ℕ) : ℝ) :=
    tsum_nat_inverse_quadratic_shift_tail_le H hH
  have hshift : ∑' n : ℕ, tail (n + H) = ∑' n : ℕ, 1 / (1 + ((n + H : ℕ) : ℝ) ^ 2) := by
    apply tsum_congr
    intro n
    have hn : H ≤ n + H := Nat.le_add_left H n
    have hcast : (n : ℤ) + H = (n + H : ℕ) := (Nat.cast_add n H).symm
    rw [hcast]
    have hn' : H ≤ ((n + H : ℕ) : ℤ).natAbs := by simpa only [Int.natAbs_natCast] using hn
    change (if H ≤ ((n + H : ℕ) : ℤ).natAbs then w ((n + H : ℕ) : ℤ) else 0) = _
    rw [ite_eq_left hn']
    dsimp only [w]
    rw [Int.cast_natCast]
  have hnatBound : (∑' n : ℕ, tail n) ≤ 1 / ((H - 1 : ℕ) : ℝ) := by
    calc
      ∑' n : ℕ, tail n = ∑' n : ℕ, tail (n + H) := by
        rw [hfin, zero_add] at hsumSplit
        exact hsumSplit.symm
      _ = _ := hshift
      _ ≤ _ := hnatShiftBound
  have hshift1 := hnat.sum_add_tsum_nat_add 1
  have hnatShift : (∑' n : ℕ, tail (n + 1)) = ∑' n : ℕ, tail n := by
    have hzeroNat : tail (0 : ℕ) = 0 := hzero
    have hfin1 : (∑ i ∈ Finset.range 1, tail i) = 0 := by
      simpa only [Finset.sum_range_one] using hzeroNat
    rw [hfin1, zero_add] at hshift1
    exact hshift1
  have hneg : Summable (fun n : ℕ ↦ tail (Int.negSucc n)) :=
    htail.comp_injective (fun _ _ h ↦ Int.negSucc.inj h)
  have hpointNeg : ∀ n : ℕ, tail (Int.negSucc n) = tail (n + 1 : ℤ) := by
    intro n
    change tail (-(n + 1 : ℤ)) = tail (n + 1 : ℤ)
    exact heven (n + 1 : ℤ)
  have hIntEq : (∑' k : ℤ, tail k) = 2 * (∑' n : ℕ, tail n) := by
    rw [← tsum_nat_add_neg_add_one htail]
    calc
      (∑' n : ℕ, (tail n + tail (Int.negSucc n))) =
          (∑' n : ℕ, tail n) + (∑' n : ℕ, tail (Int.negSucc n)) :=
        hnat.tsum_add hneg
      _ = (∑' n : ℕ, tail n) + (∑' n : ℕ, tail (n + 1)) := by
        apply congrArg (fun x : ℝ ↦ (∑' n : ℕ, tail n) + x)
        exact tsum_congr hpointNeg
      _ = 2 * (∑' n : ℕ, tail n) := by
        rw [hnatShift]; ring
  change (∑' k : ℤ, tail k) ≤ _
  rw [hIntEq]
  calc
    2 * (∑' n : ℕ, tail n) ≤ 2 * (1 / ((H - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hnatBound (by norm_num only)
    _ = _ := by ring

/-- Any finite set of integer heights outside the cutoff obeys the same inverse-quadratic
tail bound. Filter the summable majorant at H and compare the finite sum with its tsum.
This lets finite zero collections use the integer tail without first reindexing their zeros. -/
theorem sum_inverse_quadratic_le_of_forall_ge (H : ℕ) (hH : 2 ≤ H) (J : Finset ℤ)
    (hJ : ∀ k ∈ J, H ≤ k.natAbs) : (∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2)) ≤ 2 / ((H - 1 : ℕ) : ℝ) := by
  let w : ℤ → ℝ := fun k ↦ 1 / (1 + (k : ℝ) ^ 2)
  let f : ℤ → ℝ := fun k ↦ if H ≤ k.natAbs then w k else 0
  have hwn : ∀ k, 0 ≤ w k := by
    intro k
    dsimp only [w]
    exact div_nonneg zero_le_one (by nlinarith only [sq_nonneg (k : ℝ)])
  have hw : Summable w := summable_int_quadratic
  have hsum : Summable f := by
    apply Summable.of_nonneg_of_le
    · intro k
      dsimp only [f]
      split_ifs
      · exact hwn k
      · exact le_rfl
    · intro k
      dsimp only [f, w]
      split_ifs
      · exact le_rfl
      · exact div_nonneg zero_le_one (by nlinarith only [sq_nonneg (k : ℝ)])
    · exact hw
  have hfin : (∑ k ∈ J, w k) = ∑ k ∈ J, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [ite_eq_left (hJ k hk)]
  have htail := tsum_int_inverse_quadratic_tail_le H hH
  calc
    (∑ k ∈ J, w k) = ∑ k ∈ J, f k := hfin
    _ ≤ ∑' k : ℤ, f k :=
      hsum.sum_le_tsum J
        (fun k _ ↦ by
          dsimp only [f]
          split_ifs
          · exact hwn k
          · exact le_rfl)
    _ ≤ 2 / ((H - 1 : ℕ) : ℝ) := htail

/-- Any finite set of integer heights outside the cutoff obeys the logarithmic quadratic
tail bound. Filter the summable logarithmic majorant and compare the finite sum with its
tsum. This complements the inverse-quadratic finite-set estimate. -/
theorem sum_logWeighted_quadratic_le_of_forall_ge (H : ℕ) (hH : 2 ≤ H) (J : Finset ℤ)
    (hJ : ∀ k ∈ J, H ≤ k.natAbs) :
    (∑ k ∈ J, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)) ≤
      16 * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := by
  let w : ℤ → ℝ := fun k ↦ (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)
  let f : ℤ → ℝ := fun k ↦ if H ≤ k.natAbs then w k else 0
  have hwn : ∀ k, 0 ≤ w k := by
    intro k
    dsimp only [w]
    have hlog := Real.log_nonneg (show 1 ≤ 4 + |(k : ℝ)| by linarith only [abs_nonneg (k : ℝ)])
    exact div_nonneg (by linarith only [hlog]) (by nlinarith only [sq_nonneg (k : ℝ)])
  have hw : Summable w := summable_int_logWeighted_quadratic
  have hsum : Summable f := by
    apply Summable.of_nonneg_of_le
    · intro k
      dsimp only [f]
      split_ifs
      · exact hwn k
      · exact le_rfl
    · intro k
      dsimp only [f]
      split_ifs
      · exact le_rfl
      · exact hwn k
    · exact hw
  have hfin : (∑ k ∈ J, w k) = ∑ k ∈ J, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [ite_eq_left (hJ k hk)]
  have htail := tsum_int_logWeighted_quadratic_tail_le H hH
  calc
    (∑ k ∈ J, w k) = ∑ k ∈ J, f k := hfin
    _ ≤ ∑' k : ℤ, f k :=
      hsum.sum_le_tsum J
        (fun k _ ↦ by
          dsimp only [f]
          split_ifs
          · exact hwn k
          · exact le_rfl)
    _ ≤ 16 * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := htail

/-- For every epsilon > 0, a finite integer set contains all but an epsilon-sized part
of the inverse-quadratic series, uniformly over finite sets disjoint from it.
Use the norm vanishing-tail criterion and nonnegativity of finite sums.
This selects a height cutoff for conductor-uniform kernel zero tails. -/
theorem exists_int_quadratic_finite_tail_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ I : Finset ℤ, ∀ J : Finset ℤ, Disjoint J I → ∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2) < ε := by
  obtain ⟨I, hI⟩ := summable_iff_vanishing_norm.mp summable_int_quadratic ε hε
  refine ⟨I, fun J hJ ↦ ?_⟩
  have hn : 0 ≤ ∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2) :=
    Finset.sum_nonneg (fun k _ ↦ div_nonneg zero_le_one (by nlinarith only [sq_nonneg (k : ℝ)]))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hI J hJ

/-- Two real arguments at distance at most one have quadratic denominators comparable
with factor three. Bound the squared difference and expand a nonnegative square.
This transfers quadratic kernel decay to the integer height bin containing each zero. -/
theorem quadraticDenominator_le_of_dist_le_one {t u : ℝ} (h : |t - u| ≤ 1) :
    1 + u ^ 2 ≤ 3 * (1 + t ^ 2) := by
  have hu := (abs_le.mp h).2
  have hl := (abs_le.mp h).1
  have hs : (t - u) ^ 2 ≤ 1 := by nlinarith only [hu, hl]
  nlinarith only [hs, sq_nonneg (2 * t - u), sq_nonneg t]

/-- Every real number has distance at most one from its integer floor.
The lower and strict upper floor bounds give the absolute-value estimate.
This places each height bin inside a window where local zero counts apply. -/
theorem abs_sub_int_floor_le_one (t : ℝ) : |t - (⌊t⌋ : ℝ)| ≤ 1 := by
  have hl := Int.floor_le t
  have hu := Int.lt_floor_add_one t
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩

end PseudoPrime.Analysis
