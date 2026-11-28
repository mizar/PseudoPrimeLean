/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleSpectral
import PseudoPrime.Analysis.ExponentialFixedPointUpperBounds
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import Mathlib.Algebra.Polynomial.Taylor

/-! # Fixed-point inverse-height weights shared by both middle kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Real lower endpoints of the certified height-100 brackets. -/
public noncomputable def middleZeroLower (i : Fin 29) : ℝ :=
  (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ)

/-- The abstract bracket hypothesis supplies exactly these lower endpoints. -/
public theorem middle_zero_lower_le (g : Fin 29 → ℝ)
    (h : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g) (i : Fin 29) :
    middleZeroLower i ≤ g i :=
  h i

/-- Every lower endpoint in the shared ledger is positive. -/
private theorem lower_rat_pos (i : Fin 29) :
    0 < AnalyticNumberTheory.RiemannZeta.lowZero100Lower i :=
  (by decide +kernel : ∀ i : Fin 29, 0 < AnalyticNumberTheory.RiemannZeta.lowZero100Lower i) i

/-- Every real lower endpoint in the shared ledger is positive. -/
public theorem middle_zero_lower_pos (i : Fin 29) : 0 < middleZeroLower i :=
  Rat.cast_pos.mpr (lower_rat_pos i)

/-- Natural ceiling quotient, used with positive denominators. -/
private def ceilQuot (a b : ℕ) : ℕ :=
  (a + b - 1) / b

/-- Round up the scaled inverse-height contribution from one positive zero
and its conjugate. The ordinate is given as a positive rational. -/
private def headWeightTicks (q : ℚ) (j : ℕ) : ℕ :=
  ceilQuot (2 * 10 ^ 12 * q.den ^ 2 * (14 * q.den) ^ j) (q.num.natAbs ^ (j + 2))

/-- Round up the scaled inverse-square tail at height 100. -/
private def tailWeightTicks (j : ℕ) : ℕ :=
  ceilQuot (13 * 10 ^ 12 * 14 ^ j) (1000 * 100 ^ j)

/-- Sum the outward-rounded head and tail weights for one degree. -/
private def spectralWeightTicks (j : ℕ) : ℕ :=
  (∑ i : Fin 29, headWeightTicks (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i) j) +
    tailWeightTicks j

/-- A head tick bounds the corresponding scaled real inverse-height term. -/
private theorem head_weight_ticks_le {q : ℚ} (hq : 0 < q) (j : ℕ) :
    (2 * 10 ^ 12 * (14 : ℝ) ^ j) / (q : ℝ) ^ (j + 2) ≤ (headWeightTicks q j : ℝ) := by
  have hqp : 0 < q.num := Rat.num_pos.mpr hq
  have hn : 0 < q.num.natAbs := Int.natAbs_pos.mpr hqp.ne'
  have hd : 0 < q.den := q.den_pos
  have h : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
    rw [Rat.cast_def, Nat.cast_natAbs, abs_of_nonneg hqp.le]
  refine le_trans ?_ (Analysis.div_le_cast_ceilDiv _ _ (pow_pos hn _))
  apply le_of_eq
  push_cast only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [h, div_pow, pow_add (q.den : ℝ), mul_pow, div_div_eq_mul_div]
  ring

/-- A tail tick bounds the corresponding scaled inverse-height term. -/
private theorem tail_weight_ticks_le (j : ℕ) :
    (10 ^ 12 * (14 : ℝ) ^ j) * ((13 / 1000 : ℝ) / 100 ^ j) ≤ (tailWeightTicks j : ℝ) := by
  refine
    le_trans ?_ (Analysis.div_le_cast_ceilDiv _ _ (mul_pos (by decide) (pow_pos (by decide) j)))
  apply le_of_eq
  push_cast only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_div]
  ring

/-- Removing the scale from the integer sum gives a valid real bound. -/
private theorem spectral_weight_ticks_le (j : ℕ) :
    middleSpectralWeight middleZeroLower j ≤ (spectralWeightTicks j : ℝ) / (10 ^ 12 * 14 ^ j) := by
  have hscale : 0 < (10 ^ 12 * 14 ^ j : ℝ) :=
    mul_pos (pow_pos (by norm_num only) _) (pow_pos (by norm_num only) _)
  apply (le_div_iff₀ hscale).2
  have hh :=
    Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ head_weight_ticks_le (lower_rat_pos i) j)
  have ht := tail_weight_ticks_le j
  rw [middleSpectralWeight, spectralWeightTicks, Nat.cast_add, Nat.cast_sum, add_mul]
  refine add_le_add ?_ (by simpa only [mul_comm] using ht)
  rw [mul_assoc, mul_comm (∑ i, _), Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.mul_sum, mul_one_div]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [middleZeroLower]
  ring

/-- Shared integer upper weights through degree 51. The corresponding real
weight is obtained by dividing by `10^12 * 14^j`. -/
@[expose]
public def middleSpectralTicks (j : ℕ) : ℕ :=
  (#[47220926245, 21521901215, 14764910290, 12277292710, 11085432306, 10412426319, 9989828237,
            9701997215, 9491573508, 9327548736, 9192211690, 9075060488, 8969699847, 8872158023,
            8779931398, 8691423333, 8605605955, 8521812228, 8439606123, 8358700563, 8278905085,
            8200092182, 8122175536, 8045095873, 7968811717, 7893293342, 7818518804, 7744471320,
            7671137547, 7598506440, 7526568500, 7455315274, 7384739021, 7314832499, 7245588809,
            7177001311, 7109063545, 7041769197, 6975112067, 6909086052, 6843685129, 6778903349,
            6714734830, 6651173752, 6588214355, 6525850939, 6464077857, 6402889518, 6342280386,
            6282244977, 6222777858, 6163873651] :
          Array ℕ)[j]?.getD
    0

/-- Kernel checks are split by degree so that each verifies an independent block. -/
private theorem weight_block0 (i : Fin 13) : spectralWeightTicks i ≤ middleSpectralTicks i :=
  (by decide +kernel : ∀ j : Fin 13, spectralWeightTicks j ≤ middleSpectralTicks j) i

/-- The second block covers degrees 13 through 25. -/
private theorem weight_block1 (i : Fin 13) :
    spectralWeightTicks (13 + i) ≤ middleSpectralTicks (13 + i) :=
  (by decide +kernel : ∀ j : Fin 13, spectralWeightTicks (13 + j) ≤ middleSpectralTicks (13 + j)) i

/-- The third block covers degrees 26 through 38. -/
private theorem weight_block2 (i : Fin 13) :
    spectralWeightTicks (26 + i) ≤ middleSpectralTicks (26 + i) :=
  (by decide +kernel : ∀ j : Fin 13, spectralWeightTicks (26 + j) ≤ middleSpectralTicks (26 + j)) i

/-- The last block covers degrees 39 through 51. -/
private theorem weight_block3 (i : Fin 13) :
    spectralWeightTicks (39 + i) ≤ middleSpectralTicks (39 + i) :=
  (by decide +kernel : ∀ j : Fin 13, spectralWeightTicks (39 + j) ≤ middleSpectralTicks (39 + j)) i

/-- The verified table bounds the real inverse-height weight on every degree
used by either middle kernel. -/
public theorem middle_spectral_weight_le {j : ℕ} (hj : j < 52) :
    middleSpectralWeight middleZeroLower j ≤ (middleSpectralTicks j : ℝ) / (10 ^ 12 * 14 ^ j) := by
  apply (spectral_weight_ticks_le j).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  by_cases h0 : j < 13
  · exact weight_block0 ⟨j, h0⟩
  by_cases h1 : j < 26
  · have h : j - 13 < 13 := (Nat.sub_lt_iff_lt_add (le_of_not_gt h0)).mpr h1
    simpa only [Nat.add_sub_cancel' (le_of_not_gt h0)] using weight_block1 ⟨j - 13, h⟩
  by_cases h2 : j < 39
  · have h : j - 26 < 13 := (Nat.sub_lt_iff_lt_add (le_of_not_gt h1)).mpr h2
    simpa only [Nat.add_sub_cancel' (le_of_not_gt h1)] using weight_block2 ⟨j - 26, h⟩
  have h : j - 39 < 13 := (Nat.sub_lt_iff_lt_add (le_of_not_gt h2)).mpr hj
  simpa only [Nat.add_sub_cancel' (le_of_not_gt h2)] using weight_block3 ⟨j - 39, h⟩

/-- The grouped moment coefficient is the coefficient of the Taylor-translated
polynomial, so an integer translation certificate can supply the whole row. -/
public theorem middle_spectral_coeff_eq (P : Polynomial ℝ) (b : ℝ) (j : ℕ) :
    principalMomentCoeff P b j = (P.comp (Polynomial.X + Polynomial.C b)).coeff j := by
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply,
    Polynomial.eval_sum, Polynomial.sum_over_range]
  · unfold principalMomentCoeff
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_monomial]
    ring
  · intro i
    rw [mul_zero, Polynomial.monomial_zero_right, Polynomial.eval_zero]

/-- A coefficientwise upper row and the verified inverse-height table bound
the complete head-plus-tail contribution of one polynomial. -/
public theorem middle_spectral_sum_le_ticks (P : Polynomial ℝ) (b : ℝ) {N : ℕ}
    (hN : P.natDegree ≤ N) (hN' : N < 52) (A : ℕ → ℝ)
    (hA : ∀ j ≤ N, |(P.comp (Polynomial.X + Polynomial.C b)).coeff j| ≤ A j) :
    2 * (∑ i, middleSpectralMass P b (middleZeroLower i) / (middleZeroLower i) ^ 2) +
        middleSpectralMass P b 100 * (13 / 1000) ≤
      ∑ j ∈ Finset.range (N + 1),
        A j * (j.factorial : ℝ) * ((middleSpectralTicks j : ℝ) / (10 ^ 12 * 14 ^ j)) := by
  rw [middle_spectral_weighted_mass]
  have hpos (j : ℕ) : 0 ≤ (middleSpectralTicks j : ℝ) / (10 ^ 12 * 14 ^ j) := by
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  refine
    (Finset.sum_le_sum (fun j hj ↦ ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.succ_le_succ hN))
        (fun j hj _ ↦
          mul_nonneg
            (mul_nonneg ((abs_nonneg _).trans (hA j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))
              (Nat.cast_nonneg _))
            (hpos j)))
  have hj' := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hN
  rw [middle_spectral_coeff_eq]
  exact
    mul_le_mul (mul_le_mul_of_nonneg_right (hA j hj') (Nat.cast_nonneg _))
      (middle_spectral_weight_le (hj'.trans_lt hN'))
      (add_nonneg
        (mul_nonneg (by norm_num only)
          (Finset.sum_nonneg
            (fun i _ ↦ div_nonneg zero_le_one (pow_nonneg (middle_zero_lower_pos i).le _))))
        (div_nonneg (by norm_num only) (pow_nonneg (by norm_num only) _)))
      (mul_nonneg ((abs_nonneg _).trans (hA j hj')) (Nat.cast_nonneg _))

/-- Bound the physical zero series by two weighted coefficient rows, using
the same certified inverse-height table for the full and truncated moments. -/
public theorem middle_spectral_le_ticks (B : Polynomial ℝ) (hRH : RiemannHypothesis) {κ d b X : ℝ}
    {N : ℕ} (hκ : 0 ≤ κ) (hd : 0 < d) (hb : 0 < b) (hX : 0 < X) (hB : B.eval 0 = 0)
    (hB' : B.derivative.eval 0 = 0) (hN : B.natDegree ≤ N) (hN' : N < 52) (A G : ℕ → ℝ)
    (hA : ∀ j ≤ N, |B.derivative.coeff j| ≤ A j)
    (hG :
      ∀ j ≤ N,
        |((Polynomial.C d * B - B.derivative).comp (Polynomial.X + Polynomial.C b)).coeff j| ≤
          G j) :
    let e := Real.exp (-(d + 1 / 2) * b)
    |κ * e * ∑' ρ, principalCancelledTerm B d b X ρ| ≤
      ∑ j ∈ Finset.range (N + 1),
        (κ * A j + 4 * κ * e * G j) * (j.factorial : ℝ) *
          ((middleSpectralTicks j : ℝ) / (10 ^ 12 * 14 ^ j)) := by
  intro e
  let C := Polynomial.C d * B - B.derivative
  have hdN := (Polynomial.natDegree_derivative_le B).trans ((Nat.sub_le _ _).trans hN)
  have hcN : C.natDegree ≤ N :=
    (Polynomial.natDegree_sub_le_of_le ((Polynomial.natDegree_C_mul_le d B).trans hN) hdN).trans_eq
      (max_self N)
  have h :=
    middle_spectral_of_lower B hRH hκ hd hb hX middleZeroLower middle_zero_lower_pos
      middle_zero_lower_le hB hB'
  dsimp only at h
  have h₁ :=
    middle_spectral_sum_le_ticks B.derivative 0 hdN hN' A
      (by simpa only [Polynomial.C_0, add_zero, Polynomial.comp_X] using hA)
  have h₂ := middle_spectral_sum_le_ticks C b hcN hN' G hG
  let M := fun (P : Polynomial ℝ) (z : ℝ) ↦
    2 * (∑ i, middleSpectralMass P z (middleZeroLower i) / (middleZeroLower i) ^ 2) +
      middleSpectralMass P z 100 * (13 / 1000)
  have hline :
    |κ * e * ∑' ρ, principalCancelledTerm B d b X ρ| ≤
      κ * M B.derivative 0 + 4 * κ * e * M C b := by
    refine h.trans_eq ?_
    dsimp only [M, C, e]
    simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  refine
    hline.trans
      ((add_le_add (mul_le_mul_of_nonneg_left h₁ hκ)
            (mul_le_mul_of_nonneg_left h₂
              (mul_nonneg (mul_nonneg (by norm_num only) hκ) (Real.exp_nonneg _)))).trans_eq
        ?_)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ ↦ by ring)

end PseudoPrime.PrimeTestBounds.MillerRabin
