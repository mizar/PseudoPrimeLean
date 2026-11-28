/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaCoefficients

/-! # Local gamma bounds for the high Gaussian kernels -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The H34 coefficient bounds sum termwise over all profile derivatives.
The negative parts of the derivatives account for uncertain signs. -/
theorem high_gamma_cell_sum_le (K : HighGaussianKernel) (z : ℝ) (N : ℕ) {g l u : ℕ → ℝ}
    (hg : ∀ j ∈ Finset.range N, l j ≤ g j ∧ g j ≤ u j) :
    let B := fun j ↦ ((Polynomial.derivative^[j]) K.realProfile).eval z
    (∑ j ∈ Finset.range N, g j * B j) ≤
      ∑ j ∈ Finset.range N, (u j * B j + (u j - l j) * max (-B j) 0) := by
  intro B
  exact Finset.sum_le_sum fun j hj ↦ high_gamma_mul_le (hg j hj).1 (hg j hj).2

/-- Bound the finite-cell H33 expression using H34 for the derivative sum
and H35 for the two moment deficits. The remaining trivial-zero sum can
be dropped because its sign is nonnegative. -/
theorem high_gamma_cell_expression_le (K : HighGaussianKernel) {a z s d M C D : ℝ} (haz : a ≤ z)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hM : 0 ≤ M) (hB : ∀ t ∈ Set.Icc a z, -M ≤ K.realProfile.eval t)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (N : ℕ) {g l u : ℕ → ℝ}
    (hg : ∀ j ∈ Finset.range N, l j ≤ g j ∧ g j ≤ u j) :
    let B := fun j ↦ ((Polynomial.derivative^[j]) K.realProfile).eval z
    let I := fun b : ℝ ↦ ∫ t in (0 : ℝ)..b, Real.exp (s * (b - t)) * K.realProfile.eval t
    let J := fun b : ℝ ↦ ∫ t in (0 : ℝ)..b, K.realProfile.eval t * Real.exp (-d * t)
    let R :=
      ∑' k : ℕ, Real.exp (-((1 / 2 : ℝ) + 2 * (k + 2)) * z) * highProfileLaplace K (d - 2 * (k + 2))
    C * ((∑ j ∈ Finset.range N, g j * B j) - I z) - D * J z - R ≤
      C * (∑ j ∈ Finset.range N, (u j * B j + (u j - l j) * max (-B j) 0)) +
        C * (Real.exp (s * (z - a)) * (max (-I a) 0 + (z - a) * M)) +
        D * (max (-J a) 0 + (z - a) * (Real.exp (-d * a) * M)) := by
  intro B I J R
  have hI := (le_max_left (-I z) 0).trans (high_gamma_conv_local K haz hs hM hB)
  have hJ := (le_max_left (-J z) 0).trans (high_gamma_decay_local K haz hd hM hB)
  have hsum := mul_le_mul_of_nonneg_left (high_gamma_cell_sum_le K z N hg) hC
  linarith only [hsum, mul_le_mul_of_nonneg_left hI hC, mul_le_mul_of_nonneg_left hJ hD,
    high_gamma_trivial_tail_nonneg K d z]

/-- For both high-kernel rates, the remaining trivial-zero terms in H33
are summable at every positive height by geometric comparison. -/
theorem high_gamma_trivial_tail_summable (K : HighGaussianKernel) {d z : ℝ} (hd : d ≤ 3)
    (hz : 0 < z) :
    Summable fun k : ℕ ↦
      Real.exp (-((1 / 2 : ℝ) + 2 * (k + 2)) * z) * highProfileLaplace K (d - 2 * (k + 2)) := by
  let A : ℝ := ∑ j ∈ Finset.range (2 * K.degree + 1), |(K.expandedCoeff j : ℝ)|
  have hg : Summable fun k : ℕ ↦ (Real.exp (-z)) ^ k * A :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
          (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hz))).mul_right
      A
  apply
    Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (Real.exp_pos _).le (high_profile_laplace_nonneg K _)) ?_ hg
  intro k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hw : d - 2 * ((k : ℝ) + 2) ≤ -1 := by linarith only [hd, hk]
  have hb : highProfileLaplace K (d - 2 * (k + 2)) ≤ A := by
    unfold highProfileLaplace A
    apply Finset.sum_le_sum
    intro j _
    refine (le_abs_self _).trans ?_
    rw [abs_div, abs_pow, abs_of_nonpos (hw.trans (by norm_num only))]
    exact div_le_self (abs_nonneg _) (one_le_pow₀ (by linarith only [hw]))
  have he : Real.exp (-((1 / 2 : ℝ) + 2 * (k + 2)) * z) ≤ (Real.exp (-z)) ^ k := by
    rw [← Real.exp_natCast_mul]
    apply Real.exp_le_exp.mpr
    have h :=
      mul_le_mul_of_nonneg_right
        (show -((1 / 2 : ℝ) + 2 * (k + 2)) ≤ -(k : ℝ) by linarith only [hk]) hz.le
    simpa only [neg_mul, mul_neg] using h
  exact mul_le_mul he hb (high_profile_laplace_nonneg K _) (pow_nonneg (Real.exp_pos _).le _)

/-- At a positive rate `s = a - c`, the finite convolution is the
exponential residue at `c` minus the signed translated moment at `a`.
This is the cancellation needed for the first trivial zero in H33. -/
theorem high_gamma_first_pole_cancel (K : HighGaussianKernel) {a c z : ℝ} (hs : 0 < a - c)
    (hz : 0 ≤ z) :
    let Q := K.realProfile.comp (Polynomial.X + Polynomial.C z)
    Real.exp (-a * z) * (∫ t in (0 : ℝ)..z, Real.exp ((a - c) * (z - t)) * K.realProfile.eval t) =
      Real.exp (-c * z) * highProfileLaplace K (a - c) -
        Real.exp (-a * z) *
          ∑ k ∈ Finset.range (Q.natDegree + 1),
            Q.coeff k * ((k.factorial : ℝ) / (a - c) ^ (k + 1)) := by
  intro Q
  rw [high_gamma_conv_moment K hs hz, mul_sub, ← mul_assoc, ← Real.exp_add]
  congr 3
  ring

/-- At rate `d = a - c`, the decaying finite moment is the full transform
at `c` minus the signed translated contribution at `a`. -/
theorem high_gamma_decay_pole_cancel (K : HighGaussianKernel) {a c z : ℝ} (hd : 0 < a - c)
    (hz : 0 ≤ z) :
    let Q := K.realProfile.comp (Polynomial.X + Polynomial.C z)
    Real.exp (-c * z) * (∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-(a - c) * t)) =
      Real.exp (-c * z) * highProfileLaplace K (a - c) -
        Real.exp (-a * z) *
          ∑ k ∈ Finset.range (Q.natDegree + 1),
            Q.coeff k * ((k.factorial : ℝ) / (a - c) ^ (k + 1)) := by
  intro Q
  rw [high_profile_finite_laplace K hd hz, mul_sub, ← mul_assoc, ← Real.exp_add]
  congr 3
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
