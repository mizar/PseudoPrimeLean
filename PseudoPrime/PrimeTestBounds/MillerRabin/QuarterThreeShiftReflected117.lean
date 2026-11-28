/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedReflected
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftReflected
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Reflected Euler density at the section 117 shifts -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Extract the shifted logarithmic factor and the common exponential from
the dual weight at an arbitrary displacement h from the base shift 14/5. -/
theorem three_shift_dual_density {X h : ℝ} (hx : 0 < X) (hy : 1 ≤ X * Real.exp (-(14 / 5 + h)))
    (n : ℕ) :
    twoShiftDualWeight (X * Real.exp (-(14 / 5 + h))) n =
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (Real.log X - h))) *
        (ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity (Real.log X - h) n) := by
  let y := X * Real.exp (-(14 / 5 + h))
  have hyp : 0 < y := zero_lt_one.trans_le hy
  have hr : 1 ≤ Real.sqrt y :=
    (Real.le_sqrt zero_le_one hyp.le).mpr (by simpa only [one_pow] using hy)
  have hk := reflected_kernel_term_570 hr n
  rw [Real.sq_sqrt hyp.le, Real.rpow_def_of_pos (Real.sqrt_pos.mpr hyp), Real.log_sqrt hyp.le] at hk
  have hl : Real.log y = Real.log X - (14 / 5 + h) := by
    rw [show y = X * Real.exp (-(14 / 5 + h)) from rfl, Real.log_mul hx.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  rw [hl] at hk
  change twoShiftDualWeight y n = _
  unfold twoShiftDualWeight
  rw [hk]
  unfold reflectedWeight570 twoShiftReflectedDensity
  have he :
    Real.exp (-(51 / 50 : ℝ) * (14 / 5)) *
        Real.exp ((Real.log X - (14 / 5 + h)) / 2 * -(2 * (51 / 50))) =
      Real.exp (-(51 / 50) * (Real.log X - h)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination (norm := ring)
    ((51 / 50 : ℝ) ^ 5 / 120 * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(38 / 25 : ℝ)) *
        (Real.log n + (Real.log X - h)) ^ 5) *
      he

private theorem three_shift_dual_le {X h : ℝ} (hx : 0 < X) (hh : 0 ≤ h)
    (hy : 1 ≤ X * Real.exp (-(14 / 5 + h))) (k : ℕ) :
    Real.exp (-(51 / 50) * h) * twoShiftDualWeight (X * Real.exp (-(14 / 5 + h))) k ≤
      twoShiftDualWeight (X * Real.exp (-(14 / 5))) k := by
  have hb :=
    hy.trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (show -(14 / 5 + h) ≤ -(14 / 5) by linarith only [hh])) hx.le)
  rw [three_shift_dual_density hx hy, weighted_dual_density_base hx hb]
  have hE :
    Real.exp (-(51 / 50) * h) * Real.exp (-(51 / 50) * (Real.log X - h)) =
      Real.exp (-(51 / 50) * Real.log X) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow : (Real.log k + (Real.log X - h)) ^ 5 ≤ (Real.log k + Real.log X) ^ 5 := by
    apply (Odd.strictMono_pow (by decide : Odd 5)).monotone
    linarith only [hh]
  have hm :=
    mul_le_mul_of_nonneg_left hpow
      (show
        0 ≤
          (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * Real.log X) *
            (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(38 / 25 : ℝ)))
        by positivity)
  unfold twoShiftReflectedDensity
  linear_combination
    hm +
      ((51 / 50 : ℝ) ^ 5 / 120 * ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(38 / 25 : ℝ)) *
          (Real.log k + (Real.log X - h)) ^ 5) *
        hE

/-- Under prime-prefix triviality, a positive displacement loses at most
its exponential factor in the reflected character difference. -/
theorem three_shift_reflected_compare {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X h : ℝ}
    (hx : 1 ≤ X) (hh : 0 ≤ h) (ht : 1 ≤ X * Real.exp (-(14 / 5 + h)))
    (hpass : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → χ k = 1) :
    let D := fun y ↦ reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y - reflectedIntegral570 χ y
    Real.exp (-(51 / 50) * h) * D (X * Real.exp (-(14 / 5 + h))) ≤
      D (X * Real.exp (-(14 / 5))) := by
  intro D
  have hp := zero_lt_one.trans_le hx
  have hb :=
    ht.trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (show -(14 / 5 + h) ≤ -(14 / 5) by linarith only [hh])) hp.le)
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
  exact mul_le_mul_of_nonneg_left (three_shift_dual_le hp hh ht k.val) hχ

/-- The closed reflected cap at base cutoff X and displacement h multiplies
the logarithmic main, boundary, and error moments by the common scale. -/
noncomputable def threeShiftReflectedCap (X h : ℝ) : ℝ :=
  let z := Real.log X - h
  ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z)) *
    ((∑ k ∈ Finset.range 6,
        (Nat.choose 5 k : ℝ) * z ^ (5 - k) * eulerMomentValue570 (13 / 25) k X) +
      Real.sqrt X * (Real.log X ^ 2 / 24) * twoShiftReflectedDensity z X +
      ∑ k ∈ Finset.range 6, twoShiftSlopeCoeff z k * eulerMomentValue570 (51 / 50) (k + 2) X)

/-- Under RH, the reflected difference of three passing characters at a shifted
cutoff is bounded above by four times its common reflected Euler cap. -/
theorem three_shift_reflected_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X h : ℝ}
    (hx : 101 ≤ X) (hy : 1 ≤ X * Real.exp (-(14 / 5 + h))) (hz : 4 ≤ Real.log X - h)
    (hl : 5 ≤ Real.log X + (Real.log X - h)) (hRH : RiemannHypothesis)
    (htrace : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (ha : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → a k = 1) (hb : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → b k = 1)
    (hc : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → c k = 1) :
    let y := X * Real.exp (-(14 / 5 + h))
    3 * reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y -
        (reflectedIntegral570 a y + reflectedIntegral570 b y + reflectedIntegral570 c y) ≤
      4 * threeShiftReflectedCap X h := by
  intro y
  have hx0 : 0 < X := by linarith only [hx]
  have hbound :=
    (twoShift_reflected_three_tail a b c hx0.le (zero_lt_one.trans_le hy) htrace ha hb hc).2
  dsimp only at hbound
  rw [tsum_congr (fun k : { n : ℕ // ⌊X⌋₊ < n } ↦ three_shift_dual_density hx0 hy k.val),
    tsum_mul_left] at hbound
  have hm := twoShiftReflected_tail_subtype hRH hx hz hl
  unfold threeShiftReflectedCap
  have hp : 0 ≤ (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (Real.log X - h)) := by positivity
  linarith only [hbound, mul_le_mul_of_nonneg_left hm hp]

/-- The positive base residue pays part of the displacement-1/50 cost.
The displacement-11/10 reflected cost retains its full coefficient. -/
theorem three_shift_reflected_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hx : 101 ≤ X) (hy : 1 ≤ X * Real.exp (-(39 / 10))) (hl : 6 ≤ Real.log X)
    (hRH : RiemannHypothesis) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (ha : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → a k = 1) (hb : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → b k = 1)
    (hc : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → c k = 1) :
    let D := fun y ↦
      3 * reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y -
        (reflectedIntegral570 a y + reflectedIntegral570 b y + reflectedIntegral570 c y)
    let v := 3.124 - 3.143 * Real.exp (-(51 / 50) * (1 / 50))
    (-4 : ℝ) * v * threeShiftReflectedCap X (1 / 50) -
        4 * 0.0374 * threeShiftReflectedCap X (11 / 10) ≤
      3.143 * D (X * Real.exp (-(14 / 5))) - 3.124 * D (X * Real.exp (-(141 / 50))) -
        0.0374 * D (X * Real.exp (-(39 / 10))) := by
  intro D v
  have hx0 : 0 ≤ X := by linarith only [hx]
  have hx1 : 1 ≤ X := by linarith only [hx]
  have hy₁ : 1 ≤ X * Real.exp (-(14 / 5 + 1 / 50)) :=
    hy.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only)) hx0)
  have hy₂ : 1 ≤ X * Real.exp (-(14 / 5 + 11 / 10)) := by
    convert hy using 2; norm_num only
  have h₁ :=
    three_shift_reflected_upper a b c hx hy₁ (by linarith only [hl]) (by linarith only [hl]) hRH ht
      ha hb hc
  have h₂ :=
    three_shift_reflected_upper a b c hx hy₂ (by linarith only [hl]) (by linarith only [hl]) hRH ht
      ha hb hc
  let step {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :=
    three_shift_reflected_compare χ hx1 (by norm_num only : (0 : ℝ) ≤ 1 / 50) hy₁
  have hcompare :
    Real.exp (-(51 / 50) * (1 / 50)) * D (X * Real.exp (-(14 / 5 + 1 / 50))) ≤
      D (X * Real.exp (-(14 / 5))) := by
    dsimp only [D]
    linarith only [step a ha, step b hb, step c hc]
  have hE : Real.exp (-(51 / 50 : ℝ) * (1 / 50)) ≤ (1 + (51 / 50) * (1 / 50))⁻¹ := by
    rw [neg_mul, Real.exp_neg, add_comm 1]
    have hp : 0 < (51 / 50 : ℝ) * (1 / 50) + 1 := by norm_num only
    exact (inv_le_inv₀ (Real.exp_pos _) hp).2 (Real.add_one_le_exp _)
  have hv : 0 ≤ v := by
    dsimp only [v]; linarith only [hE]
  dsimp only at h₁ h₂
  change D _ ≤ _ at h₁ h₂
  rw [show (14 / 5 : ℝ) + 1 / 50 = 141 / 50 by norm_num only] at h₁ hcompare
  rw [show (14 / 5 : ℝ) + 11 / 10 = 39 / 10 by norm_num only] at h₂
  have hcost := mul_le_mul_of_nonneg_left h₁ hv
  dsimp only [v] at hcost ⊢
  linarith only [hcompare, hcost, h₂]

end PseudoPrime.PrimeTestBounds.MillerRabin
