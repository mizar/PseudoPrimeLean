/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Weighted reflected residue bound for section 107 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The dual weight at the shift 14/5 has the unshifted fifth-power
logarithmic density after extracting the common exponential. -/
theorem weighted_dual_density_base {X : ℝ} (hx : 0 < X) (hy : 1 ≤ X * Real.exp (-(14 / 5)))
    (n : ℕ) :
    twoShiftDualWeight (X * Real.exp (-(14 / 5))) n =
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * Real.log X)) *
        (ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity (Real.log X) n) := by
  let y := X * Real.exp (-(14 / 5))
  have hyp : 0 < y := zero_lt_one.trans_le hy
  have hr : 1 ≤ Real.sqrt y :=
    (Real.le_sqrt zero_le_one hyp.le).mpr (by simpa only [one_pow] using hy)
  have h := reflected_kernel_term_570 hr n
  rw [Real.sq_sqrt hyp.le, Real.rpow_def_of_pos (Real.sqrt_pos.mpr hyp), Real.log_sqrt hyp.le] at h
  have hl : Real.log y = Real.log X - 14 / 5 := by
    rw [show y = X * Real.exp (-(14 / 5)) from rfl, Real.log_mul hx.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  rw [hl] at h
  change twoShiftDualWeight y n = _
  unfold twoShiftDualWeight
  rw [h]
  unfold reflectedWeight570 twoShiftReflectedDensity
  have he :
    Real.exp (-(51 / 50 : ℝ) * (14 / 5)) * Real.exp ((Real.log X - 14 / 5) / 2 * -(2 * (51 / 50))) =
      Real.exp (-(51 / 50) * Real.log X) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination (norm := ring)
    ((51 / 50 : ℝ) ^ 5 / 120 * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(38 / 25 : ℝ)) *
        (Real.log n + (Real.log X)) ^ 5) *
      he

private theorem dual_weight_compare {X : ℝ} (hx : 1 ≤ X) (ht : 1 ≤ X * Real.exp (-3)) (k : ℕ) :
    Real.exp (-(51 / 50) * (1 / 5)) * twoShiftDualWeight (X * Real.exp (-3)) k ≤
      twoShiftDualWeight (X * Real.exp (-(14 / 5))) k := by
  have hx0 := zero_lt_one.trans_le hx
  have hb :=
    ht.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only : (-3 : ℝ) ≤ -(14 / 5)))
        hx0.le)
  rw [twoShift_dual_density hx0 ht, weighted_dual_density_base hx0 hb]
  have hExp : Real.exp (-(51 / 50 : ℝ) * (1 / 5)) * Real.exp ((51 / 50 : ℝ) * (1 / 5)) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  have hpow : (Real.log k + (Real.log X - 1 / 5)) ^ 5 ≤ (Real.log k + Real.log X) ^ 5 := by
    apply (Odd.strictMono_pow (by decide : Odd 5)).monotone
    linarith only
  unfold twoShiftReflectedDensity
  have h :=
    mul_le_mul_of_nonneg_left hpow
      (show
        0 ≤
          (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * Real.log X) *
            (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(38 / 25 : ℝ)))
        by positivity)
  have he :
    Real.exp (-(51 / 50) * (1 / 5)) *
        ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) *
          Real.exp (-(51 / 50) * Real.log X) *
          (ArithmeticFunction.vonMangoldt k *
            ((k : ℝ) ^ (-(38 / 25 : ℝ)) * (Real.log k + (Real.log X - 1 / 5)) ^ 5))) =
      (Real.exp (-(51 / 50) * (1 / 5)) * Real.exp ((51 / 50) * (1 / 5))) *
        ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * Real.log X) *
          (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(38 / 25 : ℝ))) *
          (Real.log k + (Real.log X - 1 / 5)) ^ 5) := by
    ring
  rw [he, hExp, one_mul]
  exact h.trans_eq (by ring)

private theorem reflected_difference_compare {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X : ℝ}
    (hx : 1 ≤ X) (ht : 1 ≤ X * Real.exp (-3)) (hpass : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → χ k = 1) :
    let D := fun y ↦ reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y - reflectedIntegral570 χ y
    Real.exp (-(51 / 50) * (1 / 5)) * D (X * Real.exp (-3)) ≤ D (X * Real.exp (-(14 / 5))) := by
  intro D
  have hp := zero_lt_one.trans_le hx
  have hb :=
    ht.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only : (-3 : ℝ) ≤ -(14 / 5)))
        hp.le)
  dsimp only [D]
  rw [twoShift_reflected_tail_eq χ hp.le (zero_lt_one.trans_le ht) hpass,
    twoShift_reflected_tail_eq χ hp.le (zero_lt_one.trans_le hb) hpass, ← tsum_mul_left]
  have H {y : ℝ} (hy : 0 < y) :=
    ((dual_weight_hasSum hy).summable.sub (reflected_hasSum_570 χ hy).summable).subtype
      (fun k ↦ ⌊X⌋₊ < k)
  have H' {y : ℝ} (hy : 0 < y) :
    Summable (fun k : { n : ℕ // ⌊X⌋₊ < n } ↦ (1 - (χ k.val).re) * twoShiftDualWeight y k.val) :=
    (H hy).congr
      (fun k ↦ by
        change twoShiftDualWeight y k.val - (χ k.val).re * twoShiftDualWeight y k.val = _
        ring)
  apply ((H' (zero_lt_one.trans_le ht)).mul_left _).tsum_le_tsum _ (H' (zero_lt_one.trans_le hb))
  intro k
  have hχ := sub_nonneg.mpr ((Complex.re_le_norm _).trans (χ.norm_le_one k.val))
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (dual_weight_compare hx ht k.val) hχ

/-- The section 107 weighted reflected differences retain the recovery from
the larger scale. The net cost is four times the shared tail times the
coefficient v-u exp(-a/5), for u=11/25 and v=91/200. -/
theorem weighted_reflected_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hx : 1 ≤ X) (ht : 1 ≤ X * Real.exp (-3))
    (htrace : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (ha : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → a k = 1) (hb : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → b k = 1)
    (hc : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → c k = 1) :
    let D := fun y ↦
      3 * reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y -
        (reflectedIntegral570 a y + reflectedIntegral570 b y + reflectedIntegral570 c y)
    let E := Real.exp (-(51 / 50) * (1 / 5))
    let C := (51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5))
    ((-4 : ℝ) * (91 / 200 - (11 / 25) * E) * C * twoShiftReflectedTail X) ≤
      (11 / 25) * D (X * Real.exp (-(14 / 5))) - (91 / 200) * D (X * Real.exp (-3)) := by
  intro D E C
  have hx0 := zero_lt_one.trans_le hx
  have hf :
    (∑' k : { n : ℕ // ⌊X⌋₊ < n }, twoShiftDualWeight (X * Real.exp (-3)) k.val) =
      C * twoShiftReflectedTail X := by
    rw [tsum_congr (fun k : { n : ℕ // ⌊X⌋₊ < n } ↦ twoShift_dual_density hx0 ht k.val),
      tsum_mul_left, mul_assoc]
    rfl
  have hbound :=
    (twoShift_reflected_three_tail a b c hx0.le (zero_lt_one.trans_le ht) htrace ha hb hc).2
  dsimp only at hbound
  rw [hf] at hbound
  have hD : D (X * Real.exp (-3)) ≤ 4 * (C * twoShiftReflectedTail X) := by
    dsimp only [D]
    linarith only [hbound]
  have hE : E ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  have hν : 0 ≤ 91 / 200 - (11 / 25) * E := by linarith only [hE]
  have hcost := mul_le_mul_of_nonneg_left hD hν
  have hcompare : E * D (X * Real.exp (-3)) ≤ D (X * Real.exp (-(14 / 5))) := by
    dsimp only [D, E]
    linarith only [reflected_difference_compare a hx ht ha, reflected_difference_compare b hx ht hb,
      reflected_difference_compare c hx ht hc]
  linarith only [hcost, hcompare]

/-- The three residues separate into the real main contribution, the common
oscillating zeta term, and the reflected difference controlled above. -/
theorem weighted_residue_decompose {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) {y : ℝ} (hy : 0 < y) :
    twoShiftResidueValue a y + twoShiftResidueValue b y + twoShiftResidueValue c y =
      twoShiftRealMain n y + 3 * (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm y ρ).re +
        (3 * reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y -
          (reflectedIntegral570 a y + reflectedIntegral570 b y + reflectedIntegral570 c y)) := by
  rw [← twoShift_triple_main_eq n hy]
  simp only [twoShiftResidueValue, twoShiftTripleMain, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re, Complex.norm_natCast]
  linear_combination (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) y⁻¹) * pair_level_log_sum hn

end PseudoPrime.PrimeTestBounds.MillerRabin
