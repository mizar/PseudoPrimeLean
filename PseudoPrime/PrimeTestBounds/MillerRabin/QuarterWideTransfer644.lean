/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEuler644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWindow576
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass644
import PseudoPrime.Analysis.ExponentialFixedPointBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWindow576

/-! # Quadratic weight transfer for the section 122 wide window -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The even profile polynomial at pole magnitude 107/100.
Its argument is the nonnegative logarithm of the prime. -/
noncomputable def quarterWidePoly644 (v : ℝ) : ℝ :=
  3 / 8 + (3 * (107 / 100) / 8) * v + ((107 / 100) ^ 2 / 8) * v ^ 2

/-- The common lower polynomial for the ratio at a nonnegative shift.
Its coefficients come from the logarithmic endpoint 11.55. -/
noncomputable def quarterWideRatio644 (x : ℝ) : ℝ :=
  1 + (39542920 / 257077363) * x + (4579600 / 771232089) * x ^ 2

/-- Evaluate the ratio using the upper endpoint for the base logarithm.
Cross-multiplication gives a sum of nonnegative products. -/
theorem quarter_wide_poly_lower_644 {v x : ℝ} (hv : v ∈ Set.Icc 0 (231 / 20)) (hx : 0 ≤ x) :
    quarterWidePoly644 v * quarterWideRatio644 x ≤ quarterWidePoly644 (v + x) := by
  let V : ℝ := 231 / 20
  let b : ℝ := 3 * (107 / 100) / 8
  let c : ℝ := (107 / 100) ^ 2 / 8
  let A : ℝ := 39542920 / 257077363
  let B : ℝ := 4579600 / 771232089
  have hV : 0 ≤ V - v := sub_nonneg.mpr hv.2
  have h₁ : 0 ≤ A * c * v + (A * c * V + A * b - 2 * c) :=
    add_nonneg (mul_nonneg (by norm_num only [A, c]) hv.1) (by norm_num only [A, b, c, V])
  have h₂ : 0 ≤ B * (b + c * (V + v)) :=
    mul_nonneg (by norm_num only [B])
      (add_nonneg (by norm_num only [b])
        (mul_nonneg (by norm_num only [c]) (add_nonneg (by norm_num only [V]) hv.1)))
  have he :
    quarterWidePoly644 (v + x) - quarterWidePoly644 v * quarterWideRatio644 x =
      (V - v) *
        ((A * c * v + (A * c * V + A * b - 2 * c)) * x + (B * (b + c * (V + v))) * x ^ 2) := by
    dsimp only [quarterWidePoly644, quarterWideRatio644, V, A, B, b, c]
    ring
  apply sub_nonneg.mp
  rw [he]
  exact mul_nonneg hV (add_nonneg (mul_nonneg h₁ hx) (mul_nonneg h₂ (sq_nonneg x)))

/-- In the left half of the triangular window the exponential alone
clears the required transfer constant, even at the right endpoint. -/
theorem quarter_wide_ratio_left_644 {x : ℝ} (hx : x ∈ Set.Icc 0 (5 / 2)) :
    0.0584 * (x / (5 / 2)) ≤ Real.exp (-(107 / 100) * x) * quarterWideRatio644 x := by
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (107 / 40 : ℝ)) (n := 20) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at he
  have h₀ : (0.0584 : ℝ) ≤ Real.exp (-(107 / 40 : ℝ)) := by
    rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
    linarith only [he]
  have h₁ :=
    h₀.trans (Real.exp_le_exp.mpr (show -(107 / 40 : ℝ) ≤ -(107 / 100) * x by linarith only [hx.2]))
  have h₂ : 1 ≤ quarterWideRatio644 x := by
    unfold quarterWideRatio644
    linarith only [mul_nonneg (by norm_num only : (0 : ℝ) ≤ 39542920 / 257077363) hx.1,
      mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4579600 / 771232089) (sq_nonneg x)]
  have h₃ : (0.0584 : ℝ) * (x / (5 / 2)) ≤ 0.0584 := by linarith only [hx.2]
  exact h₃.trans (h₁.trans (le_mul_of_one_le_right (Real.exp_pos _).le h₂))

/-- The physical exponential-polynomial weight dominates the left half of
the section 122 triangular window after normalization at the base logarithm. -/
theorem quarter_wide_left_644 {v x : ℝ} (hv : v ∈ Set.Icc 0 (231 / 20))
    (hx : x ∈ Set.Icc 0 (5 / 2)) :
    quarterWidePoly644 v * (0.0584 * (x / (5 / 2))) ≤
      Real.exp (-(107 / 100) * x) * quarterWidePoly644 (v + x) := by
  have hq : 0 ≤ quarterWidePoly644 v := by
    unfold quarterWidePoly644
    exact
      add_nonneg (add_nonneg (by norm_num only) (mul_nonneg (by norm_num only) hv.1))
        (mul_nonneg (by norm_num only) (sq_nonneg v))
  exact
    (mul_le_mul_of_nonneg_left (quarter_wide_ratio_left_644 hx) hq).trans
      (by
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left (quarter_wide_poly_lower_644 hv hx.1) (Real.exp_pos _).le)

/-- The Taylor polynomial for the exponential dominates the right triangular
branch. Three Bernstein expansions certify positivity on the closed half-window. -/
private theorem wide_right_polynomial {y : ℝ} (hy : y ∈ Set.Icc 0 (5 / 2)) :
    (0.0584 : ℝ) * (y / (5 / 2)) * 210.61 ≤
      quarterWideRatio644 (5 - y) *
        ∑ k ∈ Finset.range 7, ((107 / 100 : ℝ) * y) ^ k / (k.factorial : ℝ) := by
  let F :=
    quarterWideRatio644 (5 - y) *
        (∑ k ∈ Finset.range 7, ((107 / 100 : ℝ) * y) ^ k / (k.factorial : ℝ)) -
      0.0584 * (y / (5 / 2)) * 210.61
  apply sub_nonneg.mp
  change 0 ≤ F
  have step0 (hL : (0 / 1 : ℝ) ≤ y) (hU : y ≤ (5 / 8 : ℝ)) : 0 ≤ F := by
    have hL := sub_nonneg.mpr hL
    have hU := sub_nonneg.mpr hU
    have he :
      F =
        (24811252454785024 / 301262534765625 : ℝ) * (y - (0 / 1 : ℝ)) ^ 0 * ((5 / 8 : ℝ) - y) ^ 8 +
          (904019926267559149568 / 1569075701904296875 : ℝ) * (y - (0 / 1 : ℝ)) ^ 1 *
            ((5 / 8 : ℝ) - y) ^ 7 +
          (2732879407889999486976 / 1569075701904296875 : ℝ) * (y - (0 / 1 : ℝ)) ^ 2 *
            ((5 / 8 : ℝ) - y) ^ 6 +
          (41886102074952740292352 / 14121681317138671875 : ℝ) * (y - (0 / 1 : ℝ)) ^ 3 *
            ((5 / 8 : ℝ) - y) ^ 5 +
          (974491632604039572186 / 313815140380859375 : ℝ) * (y - (0 / 1 : ℝ)) ^ 4 *
            ((5 / 8 : ℝ) - y) ^ 4 +
          (51252836319711637649827 / 25105211230468750000 : ℝ) * (y - (0 / 1 : ℝ)) ^ 5 *
            ((5 / 8 : ℝ) - y) ^ 3 +
          (178080530227977447288843721 / 216909025031250000000000 : ℝ) * (y - (0 / 1 : ℝ)) ^ 6 *
            ((5 / 8 : ℝ) - y) ^ 2 +
          (39979547349013368781638727 / 216909025031250000000000 : ℝ) * (y - (0 / 1 : ℝ)) ^ 7 *
            ((5 / 8 : ℝ) - y) ^ 1 +
          (15359202065763783387828169 / 867636100125000000000000 : ℝ) * (y - (0 / 1 : ℝ)) ^ 8 *
            ((5 / 8 : ℝ) - y) ^ 0 := by
      dsimp only [F, quarterWideRatio644]
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
        Nat.cast_one, Nat.cast_zero]
      ring
    rw [he]
    have h0 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (24811252454785024 / 301262534765625 : ℝ))
          (pow_nonneg hL 0))
        (pow_nonneg hU 8)
    have h1 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (904019926267559149568 / 1569075701904296875 : ℝ))
          (pow_nonneg hL 1))
        (pow_nonneg hU 7)
    have h2 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (2732879407889999486976 / 1569075701904296875 : ℝ))
          (pow_nonneg hL 2))
        (pow_nonneg hU 6)
    have h3 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (41886102074952740292352 / 14121681317138671875 : ℝ))
          (pow_nonneg hL 3))
        (pow_nonneg hU 5)
    have h4 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (974491632604039572186 / 313815140380859375 : ℝ))
          (pow_nonneg hL 4))
        (pow_nonneg hU 4)
    have h5 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (51252836319711637649827 / 25105211230468750000 : ℝ))
          (pow_nonneg hL 5))
        (pow_nonneg hU 3)
    have h6 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (178080530227977447288843721 / 216909025031250000000000 : ℝ))
          (pow_nonneg hL 6))
        (pow_nonneg hU 2)
    have h7 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (39979547349013368781638727 / 216909025031250000000000 : ℝ))
          (pow_nonneg hL 7))
        (pow_nonneg hU 1)
    have h8 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (15359202065763783387828169 / 867636100125000000000000 : ℝ))
          (pow_nonneg hL 8))
        (pow_nonneg hU 0)
    linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have step1 (hL : (5 / 8 : ℝ) ≤ y) (hU : y ≤ (5 / 4 : ℝ)) : 0 ≤ F := by
    have hL := sub_nonneg.mpr hL
    have hU := sub_nonneg.mpr hU
    have he :
      F =
        (15359202065763783387828169 / 867636100125000000000000 : ℝ) * (y - (5 / 8 : ℝ)) ^ 0 *
            ((5 / 4 : ℝ) - y) ^ 8 +
          (7152420304680588256557983 / 72303008343750000000000 : ℝ) * (y - (5 / 8 : ℝ)) ^ 1 *
            ((5 / 4 : ℝ) - y) ^ 7 +
          (645660335775682922734537 / 2892120333750000000000 : ℝ) * (y - (5 / 8 : ℝ)) ^ 2 *
            ((5 / 4 : ℝ) - y) ^ 6 +
          (3505656936365098746920077 / 13556814064453125000000 : ℝ) * (y - (5 / 8 : ℝ)) ^ 3 *
            ((5 / 4 : ℝ) - y) ^ 5 +
          (202548293342164368964319 / 1205050139062500000000 : ℝ) * (y - (5 / 8 : ℝ)) ^ 4 *
            ((5 / 4 : ℝ) - y) ^ 4 +
          (363729545307524206943659 / 4518938021484375000000 : ℝ) * (y - (5 / 8 : ℝ)) ^ 5 *
            ((5 / 4 : ℝ) - y) ^ 3 +
          (703148407253448816461533 / 13556814064453125000000 : ℝ) * (y - (5 / 8 : ℝ)) ^ 6 *
            ((5 / 4 : ℝ) - y) ^ 2 +
          (136886062042745650873 / 4518938021484375000 : ℝ) * (y - (5 / 8 : ℝ)) ^ 7 *
            ((5 / 4 : ℝ) - y) ^ 1 +
          (2088451453255561658803 / 282433626342773437500 : ℝ) * (y - (5 / 8 : ℝ)) ^ 8 *
            ((5 / 4 : ℝ) - y) ^ 0 := by
      dsimp only [F, quarterWideRatio644]
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
        Nat.cast_one, Nat.cast_zero]
      ring
    rw [he]
    have h0 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (15359202065763783387828169 / 867636100125000000000000 : ℝ))
          (pow_nonneg hL 0))
        (pow_nonneg hU 8)
    have h1 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (7152420304680588256557983 / 72303008343750000000000 : ℝ))
          (pow_nonneg hL 1))
        (pow_nonneg hU 7)
    have h2 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (645660335775682922734537 / 2892120333750000000000 : ℝ))
          (pow_nonneg hL 2))
        (pow_nonneg hU 6)
    have h3 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (3505656936365098746920077 / 13556814064453125000000 : ℝ))
          (pow_nonneg hL 3))
        (pow_nonneg hU 5)
    have h4 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (202548293342164368964319 / 1205050139062500000000 : ℝ))
          (pow_nonneg hL 4))
        (pow_nonneg hU 4)
    have h5 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (363729545307524206943659 / 4518938021484375000000 : ℝ))
          (pow_nonneg hL 5))
        (pow_nonneg hU 3)
    have h6 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (703148407253448816461533 / 13556814064453125000000 : ℝ))
          (pow_nonneg hL 6))
        (pow_nonneg hU 2)
    have h7 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (136886062042745650873 / 4518938021484375000 : ℝ))
          (pow_nonneg hL 7))
        (pow_nonneg hU 1)
    have h8 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (2088451453255561658803 / 282433626342773437500 : ℝ))
          (pow_nonneg hL 8))
        (pow_nonneg hU 0)
    linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have step2 (hL : (5 / 4 : ℝ) ≤ y) (hU : y ≤ (5 / 2 : ℝ)) : 0 ≤ F := by
    have hL := sub_nonneg.mpr hL
    have hU := sub_nonneg.mpr hU
    have he :
      F =
        (2088451453255561658803 / 72303008343750000000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 0 *
            ((5 / 2 : ℝ) - y) ^ 8 +
          (33012077122790273452147 / 72303008343750000000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 1 *
            ((5 / 2 : ℝ) - y) ^ 7 +
          (541342929510355854036461 / 173527220025000000000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 2 *
            ((5 / 2 : ℝ) - y) ^ 6 +
          (796663219788954347455981 / 72303008343750000000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 3 *
            ((5 / 2 : ℝ) - y) ^ 5 +
          (35863505621948635839353 / 1606733518750000000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 4 *
            ((5 / 2 : ℝ) - y) ^ 4 +
          (735774938709111709483931 / 27113628128906250000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 5 *
            ((5 / 2 : ℝ) - y) ^ 3 +
          (355256684606944439763301 / 18075752085937500000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 6 *
            ((5 / 2 : ℝ) - y) ^ 2 +
          (7086684317698893575521 / 903787604296875000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 7 *
            ((5 / 2 : ℝ) - y) ^ 1 +
          (18027176926728585381361 / 13556814064453125000000 : ℝ) * (y - (5 / 4 : ℝ)) ^ 8 *
            ((5 / 2 : ℝ) - y) ^ 0 := by
      dsimp only [F, quarterWideRatio644]
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
        Nat.cast_one, Nat.cast_zero]
      ring
    rw [he]
    have h0 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (2088451453255561658803 / 72303008343750000000000 : ℝ))
          (pow_nonneg hL 0))
        (pow_nonneg hU 8)
    have h1 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (33012077122790273452147 / 72303008343750000000000 : ℝ))
          (pow_nonneg hL 1))
        (pow_nonneg hU 7)
    have h2 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (541342929510355854036461 / 173527220025000000000000 : ℝ))
          (pow_nonneg hL 2))
        (pow_nonneg hU 6)
    have h3 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (796663219788954347455981 / 72303008343750000000000 : ℝ))
          (pow_nonneg hL 3))
        (pow_nonneg hU 5)
    have h4 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (35863505621948635839353 / 1606733518750000000000 : ℝ))
          (pow_nonneg hL 4))
        (pow_nonneg hU 4)
    have h5 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (735774938709111709483931 / 27113628128906250000000 : ℝ))
          (pow_nonneg hL 5))
        (pow_nonneg hU 3)
    have h6 :=
      mul_nonneg
        (mul_nonneg
          (by norm_num only : 0 ≤ (355256684606944439763301 / 18075752085937500000000 : ℝ))
          (pow_nonneg hL 6))
        (pow_nonneg hU 2)
    have h7 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (7086684317698893575521 / 903787604296875000000 : ℝ))
          (pow_nonneg hL 7))
        (pow_nonneg hU 1)
    have h8 :=
      mul_nonneg
        (mul_nonneg (by norm_num only : 0 ≤ (18027176926728585381361 / 13556814064453125000000 : ℝ))
          (pow_nonneg hL 8))
        (pow_nonneg hU 0)
    linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  by_cases h₁ : y ≤ 5 / 8
  · exact step0 (by simpa only [zero_div] using hy.1) h₁
  by_cases h₂ : y ≤ 5 / 4
  · exact step1 (le_of_not_ge h₁) h₂
  exact step2 (le_of_not_ge h₂) hy.2

/-- The normalized weight on the right half of the wide triangle retains
the same 0.0584 transfer coefficient, including the closed right endpoint. -/
theorem quarter_wide_ratio_right_644 {x : ℝ} (hx : x ∈ Set.Icc (5 / 2) 5) :
    0.0584 * ((5 - x) / (5 / 2)) ≤ Real.exp (-(107 / 100) * x) * quarterWideRatio644 x := by
  let y := 5 - x
  have hy : y ∈ Set.Icc 0 (5 / 2) :=
    ⟨sub_nonneg.mpr hx.2, by
      dsimp only [y]
      linarith only [hx.1]⟩
  have hxy : 5 - y = x := by
    dsimp only [y]; ring
  have hp := wide_right_polynomial hy
  rw [hxy] at hp
  have hq : 0 ≤ quarterWideRatio644 x := by
    have hx₀ : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 5 / 2).trans hx.1
    unfold quarterWideRatio644
    positivity
  have ht :=
    mul_le_mul_of_nonneg_left
      (Real.sum_le_exp_of_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 107 / 100) hy.1) 7) hq
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (107 / 20 : ℝ)) (n := 27) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at he
  have hE : Real.exp (107 / 20 : ℝ) ≤ 210.61 := by linarith only [he]
  have hb : 0 ≤ (0.0584 : ℝ) * (y / (5 / 2)) :=
    mul_nonneg (by norm_num only) (div_nonneg hy.1 (by norm_num only))
  have h := (mul_le_mul_of_nonneg_left hE hb).trans (hp.trans ht)
  rw [show (107 / 100 : ℝ) * y = -(107 / 100) * x + 107 / 20
      by
      dsimp only [y]
      ring,
    Real.exp_add] at h
  apply le_of_mul_le_mul_right _ (Real.exp_pos (107 / 20 : ℝ))
  rw [show
      Real.exp (-(107 / 100) * x) * quarterWideRatio644 x * Real.exp (107 / 20) =
        quarterWideRatio644 x * (Real.exp (-(107 / 100) * x) * Real.exp (107 / 20))
      by ring]
  exact h

/-- Across the entire closed triangle, the shifted physical weight is
at least 0.0584 times the triangular profile at the base logarithm. -/
theorem quarter_wide_transfer_644 {v x : ℝ} (hv : v ∈ Set.Icc 0 (231 / 20)) (hx : x ∈ Set.Icc 0 5) :
    quarterWidePoly644 v * (0.0584 * min (x / (5 / 2)) ((5 - x) / (5 / 2))) ≤
      Real.exp (-(107 / 100) * x) * quarterWidePoly644 (v + x) := by
  have hq : 0 ≤ quarterWidePoly644 v := by
    unfold quarterWidePoly644
    exact
      add_nonneg (add_nonneg (by norm_num only) (mul_nonneg (by norm_num only) hv.1))
        (mul_nonneg (by norm_num only) (sq_nonneg v))
  have ht :
    0.0584 * min (x / (5 / 2)) ((5 - x) / (5 / 2)) ≤
      Real.exp (-(107 / 100) * x) * quarterWideRatio644 x := by
    rcases le_or_gt x (5 / 2) with h | h
    · exact
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num only)).trans
          (quarter_wide_ratio_left_644 ⟨hx.1, h⟩)
    · exact
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num only)).trans
          (quarter_wide_ratio_right_644 ⟨h.le, hx.2⟩)
  exact
    (mul_le_mul_of_nonneg_left ht hq).trans
      (by
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left (quarter_wide_poly_lower_644 hv hx.1) (Real.exp_pos _).le)

/-- On its supporting interval the existing triangular weight equals the
minimum of its two affine branches. -/
private theorem wide_triangle_eq {x : ℝ} (hx : x ∈ Set.Icc 0 5) :
    shiftedTriangle (5 / 2) x = min (x / (5 / 2)) ((5 - x) / (5 / 2)) := by
  unfold shiftedTriangle
  rcases le_or_gt x (5 / 2) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left (by linarith only [h]),
      max_eq_right (by linarith only [hx.1])]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h.le), min_eq_right (by linarith only [h]),
      max_eq_right (by linarith only [hx.2])]
    ring

/-- For a positive index in the wide window, transfer its triangular
weight to the section 122 Euler weight. The common factor depends only on v. -/
theorem quarter_wide_euler_point_644 {v : ℝ} (hv : v ∈ Set.Icc 0 (231 / 20)) {n : ℕ} (hn : 0 < n)
    (hx : Real.log n - v ∈ Set.Icc 0 5) :
    (0.0584 * quarterWidePoly644 v * Real.exp (-(107 / 100) * v)) *
        (shiftedTriangle (5 / 2) (Real.log n - v) / Real.sqrt n) ≤
      quarterEulerWeight644 n := by
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hz := quarter_wide_transfer_644 hv hx
  rw [← wide_triangle_eq hx, add_sub_cancel] at hz
  have he := mul_le_mul_of_nonneg_left hz (Real.exp_pos (-(107 / 100) * v)).le
  have ht :
    Real.exp (-(107 / 100) * v) * Real.exp (-(107 / 100) * (Real.log n - v)) =
      Real.exp (-(107 / 100) * Real.log n) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← mul_assoc (Real.exp (-(107 / 100) * v)) (Real.exp (-(107 / 100) * (Real.log n - v))),
    ht] at he
  have he' := div_le_div_of_nonneg_right he (Real.sqrt_nonneg (n : ℝ))
  have hweight :
    Real.exp (-(107 / 100) * Real.log n) * quarterWidePoly644 (Real.log n) / Real.sqrt n =
      quarterEulerWeight644 n := by
    have hx' : Real.exp (-(107 / 100) * Real.log n) = ((n : ℝ) ^ (107 / 100 : ℝ))⁻¹ := by
      rw [neg_mul, Real.exp_neg, Real.rpow_def_of_pos hp, mul_comm]
    rw [hx', Real.sqrt_eq_rpow, div_eq_mul_inv, mul_right_comm, ← mul_inv, ← Real.rpow_add hp,
      show (107 / 100 + 1 / 2 : ℝ) = 157 / 100 by norm_num only]
    unfold quarterEulerWeight644 quarterWidePoly644
    ring
  calc
    _ =
        (Real.exp (-(107 / 100) * v) *
            (quarterWidePoly644 v * (0.0584 * shiftedTriangle (5 / 2) (Real.log n - v)))) /
          Real.sqrt n :=
      by ring
    _ ≤ _ := he'.trans_eq hweight

/-- Sum the pointwise transfer over any finite subset of the positive
wide window. A certified triangular mass then supplies a lower Euler mass. -/
theorem quarter_wide_euler_sum_644 {v M : ℝ} (hv : v ∈ Set.Icc 0 (231 / 20)) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ Real.log n - v ∈ Set.Icc 0 5)
    (hM : M ≤ ∑ n ∈ s, Real.log n * (shiftedTriangle (5 / 2) (Real.log n - v) / Real.sqrt n)) :
    4 * (0.0584 * quarterWidePoly644 v * Real.exp (-(107 / 100) * v)) * M ≤
      4 * ∑ n ∈ s, Real.log n * quarterEulerWeight644 n := by
  let C := 0.0584 * quarterWidePoly644 v * Real.exp (-(107 / 100) * v)
  have hq : 0 ≤ quarterWidePoly644 v := by
    unfold quarterWidePoly644
    exact
      add_nonneg (add_nonneg (by norm_num only) (mul_nonneg (by norm_num only) hv.1))
        (mul_nonneg (by norm_num only) (sq_nonneg v))
  have hC : 0 ≤ C := by
    dsimp only [C]; positivity
  have h := mul_le_mul_of_nonneg_left hM hC
  rw [Finset.mul_sum] at h
  apply (show 4 * C * M = 4 * (C * M) by ring).le.trans
  apply mul_le_mul_of_nonneg_left (h.trans _) (by norm_num only)
  apply Finset.sum_le_sum
  intro n hn
  have hlog := Real.log_nonneg (show 1 ≤ (n : ℝ) from Nat.one_le_cast.mpr (hs n hn).1)
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (quarter_wide_euler_point_644 hv (hs n hn).1 (hs n hn).2) hlog

/-- On radii 316 through 322, a triangle mass of at least 73/50 times
the radius supplies an Euler credit of at least 0.0113. -/
theorem quarter_wide_euler_credit_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ Real.log n - 2 * Real.log r ∈ Set.Icc 0 5)
    (hM :
      73 / 50 * r ≤
        ∑ n ∈ s,
          Real.log n * (shiftedTriangle (5 / 2) (Real.log n - 2 * Real.log r) / Real.sqrt n)) :
    (0.0113 : ℝ) ≤ 4 * ∑ n ∈ s, Real.log n * quarterEulerWeight644 n := by
  have hp : 0 < r := by linarith only [hr.1]
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 316 9 27 (57557 / 10000) 6 = true by
          decide +kernel)).1
  have hU :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 322 9 27 (5774 / 1000) (5775 / 1000) = true by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL hU
  have hl := hL.trans (Real.log_le_log (by norm_num only) hr.1)
  have hu := (Real.log_le_log hp hr.2).trans hU
  have hv : 2 * Real.log r ∈ Set.Icc 0 (231 / 20) := ⟨by linarith only [hl], by linarith only [hu]⟩
  have hq : quarterWidePoly644 (115114 / 10000) ≤ quarterWidePoly644 (2 * Real.log r) := by
    unfold quarterWidePoly644
    have hh : (115114 / 10000 : ℝ) ≤ 2 * Real.log r := by linarith only [hl]
    linarith only [hh, pow_le_pow_left₀ (by norm_num only : 0 ≤ (115114 / 10000 : ℝ)) hh 2]
  have hP :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 322) (p := 57) (d := 50)
        (lo := 1383 / 1000000) (hi := 1) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at hP
  have hpow :=
    hP.trans (Real.rpow_le_rpow_of_nonpos hp hr.2 (by norm_num only : (-(57 / 50) : ℝ) ≤ 0))
  have hm :=
    mul_le_mul hq hpow (by norm_num only : (0 : ℝ) ≤ 1383 / 1000000)
      (le_trans (by norm_num only [quarterWidePoly644]) hq)
  have h := quarter_wide_euler_sum_644 hv s hs hM
  have he : Real.exp (-(107 / 100) * (2 * Real.log r)) * r = r ^ (-(57 / 50) : ℝ) := by
    calc
      _ = Real.exp (-(107 / 100) * (2 * Real.log r)) * Real.exp (Real.log r) := by
        rw [Real.exp_log hp]
      _ = _ := by
        rw [← Real.exp_add, Real.rpow_def_of_pos hp]
        congr 1
        ring
  calc
    (0.0113 : ℝ) ≤
        (4 * 0.0584 * (73 / 50)) * (quarterWidePoly644 (115114 / 10000) * (1383 / 1000000)) :=
      by norm_num only [quarterWidePoly644]
    _ ≤ (4 * 0.0584 * (73 / 50)) * (quarterWidePoly644 (2 * Real.log r) * r ^ (-(57 / 50) : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num only)
    _ = _ := by
      rw [← he]; ring
    _ ≤ _ := h

/-- On section 122 radii, a wide window of trace-three primes with the
required triangular mass improves the even zero-mass upper bound by 0.0113. -/
theorem quarter_wide_mass_upper_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c.Even) {r : ℝ} (hr : r ∈ Set.Icc 316 322)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) (T : Finset ℕ)
    (hT :
      ∀ n ∈ T,
        n.Prime ∧ r ^ 2 < n ∧ (a n).re + (b n).re + (c n).re = 3 ∧ Real.log n - 2 * Real.log r ≤ 5)
    (hM :
      73 / 50 * r ≤
        ∑ n ∈ T,
          Real.log n * (shiftedTriangle (5 / 2) (Real.log n - 2 * Real.log r) / Real.sqrt n)) :
    quarterMass644 a + quarterMass644 b + quarterMass644 c ≤
      3 / 4 * r - 11.7421197 + 4 * positiveTail644 (r ^ 2) - 0.0113 := by
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hX := (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 316) hr.1 2)
  have hY := pow_le_pow_left₀ hr₀.le hr.2 2
  have h :=
    quarter_even_extra_mass_644 hp hq hs hG ha hb hc hlog
      ((by norm_num only : (2701 : ℝ) ≤ 316 ^ 2).trans hX) (hY.trans (by norm_num only)) ht hA hB hC
      T (fun n hn ↦ ⟨(hT n hn).1, (hT n hn).2.1, (hT n hn).2.2.1⟩)
  have hcredit :=
    quarter_wide_euler_credit_644 hr T
      (fun n hn ↦ by
        obtain ⟨hp', hx, _, hu⟩ := hT n hn
        have hl := Real.log_le_log (pow_pos hr₀ 2) hx.le
        rw [Real.log_pow, Nat.cast_ofNat] at hl
        exact ⟨hp'.pos, by linarith only [hl], hu⟩)
      hM
  linarith only [h, hcredit]

end PseudoPrime.PrimeTestBounds.MillerRabin
