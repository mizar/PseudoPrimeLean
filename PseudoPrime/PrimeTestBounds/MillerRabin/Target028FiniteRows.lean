/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteWeight
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPsi
public import PseudoPrime.Analysis.ExponentialFixedPointConversions

/-! # Rational row bounds for the finite principal sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At a positive cutoff, any finite set of checked prime-power rows and
nonnegative rational lower weights gives a lower bound for the principal sum.
This permits later cells to use tables extending beyond the original prefix. -/
theorem target028_principal_checked_rows {X : ℝ} (hX : 0 < X) (s : Finset ℕ)
    (data : ℕ → RefinedEulerAtom) (w : ℕ → ℚ)
    (hc : ∀ n ∈ s, IsPrimePow n → refinedEulerAtomCheck 24 n (data n) = true)
    (ht : s ⊆ Finset.Ioc 0 ⌊X⌋₊) (hw0 : ∀ n ∈ s, 0 ≤ w n)
    (hw : ∀ n ∈ s, (w n : ℝ) ≤ refinedScaledWeight X n) :
    ((∑ n ∈ s, refinedPsiLower n (data n) * w n : ℚ) : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re := by
  rw [Rat.cast_sum]
  calc
    _ ≤ ∑ n ∈ s, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Rat.cast_mul,
        refined_principal_summand_eq hX (Nat.ne_of_gt (Finset.mem_Ioc.mp (ht hn)).1)]
      exact
        mul_le_mul (refined_psi_row_lower (hc n hn)) (hw n hn) (Rat.cast_nonneg.mpr (hw0 n hn))
          ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ :=
      Finset.sum_le_sum_of_subset_of_nonneg ht
        (fun n hn _ ↦
          LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg refinedSixPoleKernel hX n)

-- Applying the checked prime-power prefix reduces its 193-row definition.
set_option maxRecDepth 1000000 in
/-- For a positive cutoff, rational lower weights on a subset of the checked
prime-power rows give a rational lower bound for the finite principal sum.
Each row uses the certified logarithm bound, while the omitted summands are
nonnegative. This transfers finite cell certificates to the analytic criterion. -/
theorem target028_principal_rows_lower {X : ℝ} (hX : 0 < X) (s : Finset ℕ) (w : ℕ → ℚ)
    (hs : s ⊆ refinedEulerPrefixSet) (ht : s ⊆ Finset.Ioc 0 ⌊X⌋₊) (hw0 : ∀ n ∈ s, 0 ≤ w n)
    (hw : ∀ n ∈ s, (w n : ℝ) ≤ refinedScaledWeight X n) :
    ((∑ n ∈ s, refinedPsiLower n (refinedEulerData n) * w n : ℚ) : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re := by
  exact
    target028_principal_checked_rows hX s refinedEulerData w
      (fun n hn ↦ refined_euler_prefix_check n (hs hn)) ht hw0 hw

/-- At the first cutoff, the scaled weight at an index in the support has a
single square-root denominator. The square roots of the scale cancel after
substitution of the explicit kernel formula. -/
theorem target028_weight252_eq {b : ℝ} (hb : 0 < b) (hb' : b ≤ 252) :
    refinedScaledWeight 252 b =
      refinedCoord (b / 252) ^ 5 * Real.exp (-refinedCoord (b / 252)) / (120 * Real.sqrt b) := by
  have hu : 0 < b / 252 := by linarith only [hb]
  have hl : Real.log (b / 252) ≤ 21 / 8 :=
    (Real.log_nonpos hu.le (by linarith only [hb'])).trans (by norm_num only)
  dsimp only [refinedScaledWeight, refinedKernelWeight]
  rw [refinedKernelWeight_eq hu hl, refinedWeight, Real.sqrt_div hb.le]
  have hs : Real.sqrt (252 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num only)).ne'
  have ht : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp

/-- At scale 252, the weight decreases from index 1 to index 252. This transfers
one certified endpoint lower bound to every prime-power row in its interval. -/
theorem target028_weight252_antitone {n b : ℝ} (hn : 1 ≤ n) (hnb : n ≤ b) (hb : b ≤ 252) :
    refinedScaledWeight 252 b ≤ refinedScaledWeight 252 n := by
  have hn0 : 0 < n / 252 := by linarith only [hn]
  have hb0 : 0 < b / 252 := by linarith only [hn, hnb]
  have hn1 : n / 252 ≤ 1 := by linarith only [hnb, hb]
  have hb1 : b / 252 ≤ 1 := by linarith only [hb]
  have hln : Real.log (n / 252) ≤ 21 / 8 := (Real.log_nonpos hn0.le hn1).trans (by norm_num only)
  have hlb : Real.log (b / 252) ≤ 21 / 8 := (Real.log_nonpos hb0.le hb1).trans (by norm_num only)
  have hm :=
    target028_weight_antitone_first
      (show n / 252 ∈ Set.Icc (1 / 252 : ℝ) 1 by constructor <;> linarith only [hn, hn1])
      (show b / 252 ∈ Set.Icc (1 / 252 : ℝ) 1 by constructor <;> linarith only [hn, hnb, hb1])
      (show n / 252 ≤ b / 252 by linarith only [hnb])
  dsimp only [refinedScaledWeight, refinedKernelWeight]
  rw [refinedKernelWeight_eq hn0 hln, refinedKernelWeight_eq hb0 hlb]
  exact div_le_div_of_nonneg_right hm (Real.sqrt_nonneg _)

/-- Bounds for the coordinate, exponential, and square root give an explicit
lower bound for the endpoint weight at scale 252. Positivity permits separate
comparison of the numerator and denominator. -/
theorem target028_weight252_lower {b L E R : ℝ} (hb : 0 < b) (hb' : b ≤ 252) (hL0 : 0 ≤ L)
    (hL : L ≤ refinedCoord (b / 252)) (hE0 : 0 ≤ E) (hE : E ≤ Real.exp (-refinedCoord (b / 252)))
    (hR : Real.sqrt b ≤ R) : L ^ 5 * E / (120 * R) ≤ refinedScaledWeight 252 b := by
  rw [target028_weight252_eq hb hb']
  have hc0 : 0 ≤ refinedCoord (b / 252) := le_trans hL0 hL
  have hm : L ^ 5 * E ≤ refinedCoord (b / 252) ^ 5 * Real.exp (-refinedCoord (b / 252)) :=
    mul_le_mul (pow_le_pow_left₀ hL0 hL 5) hE hE0 (pow_nonneg hc0 5)
  exact
    div_le_div₀ (mul_nonneg (pow_nonneg hc0 5) (Real.exp_pos _).le) hm
      (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hb))
      (mul_le_mul_of_nonneg_left hR (by norm_num only))

/-- Logarithm bounds at the reciprocal endpoint bound the coordinate from
both sides. The reciprocal identity converts the checked positive logarithm
to the negative logarithm in the weight. -/
theorem target028_coord252_bounds {b lo hi : ℝ} (hb : 0 < b) (hlo : lo ≤ Real.log (252 / b))
    (hhi : Real.log (252 / b) ≤ hi) :
    567 / 200 + (27 / 25) * lo ≤ refinedCoord (b / 252) ∧
      refinedCoord (b / 252) ≤ 567 / 200 + (27 / 25) * hi := by
  have heq : Real.log (b / 252) = -Real.log (252 / b) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  dsimp only [refinedCoord]
  rw [heq]
  constructor <;> linarith only [hlo, hhi]

/-- A fixed-point exponential lower bound remains valid when the coordinate is
at most `u / 1000`, for `u ≤ 16000`. Monotonicity transfers the checked Taylor
bound at the rational endpoint to the actual coordinate. -/
theorem target028_exp_lower (u : ℕ) (hu : u ≤ 16000) {c : ℝ} (hc : c ≤ (u : ℝ) / 1000) :
    (Analysis.expFixedPointSignedLower (-(u : ℤ)) 1000 1000000000 32 : ℝ) / 1000000000 ≤
      Real.exp (-c) := by
  have hur : (u : ℝ) ≤ 16000 := by exact_mod_cast hu
  have hs : (|((-(u : ℤ) : ℤ) : ℝ)| / (1000 : ℝ)) / (32 + 1 : ℕ) ≤ 1 / 2 := by
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ (u : ℝ) from Nat.cast_nonneg u)]
    norm_num only [Nat.cast_add, Nat.cast_ofNat, Nat.reduceAdd]
    linarith only [hur]
  have h :=
    Analysis.exp_fixed_signed_lower_div (-(u : ℤ)) 1000 1000000000 32 (by decide) (by decide) hs
  simp only [Int.cast_neg, Int.cast_natCast, Nat.cast_ofNat, neg_div] at h
  exact h.trans (Real.exp_le_exp.mpr (by linarith only [hc]))

end PseudoPrime.PrimeTestBounds.MillerRabin
