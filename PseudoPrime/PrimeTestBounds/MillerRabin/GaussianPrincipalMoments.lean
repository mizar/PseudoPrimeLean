/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroVariation
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroCancel
import Mathlib.Tactic.Ring

/-! # Finite moment representation of the principal head -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The finite head is the full reflected Mellin moment minus the unit-interval moment.
The identity holds at every real height, including all rational bracket midpoints. -/
public theorem high_principal_head_moments (K : HighGaussianKernel) (t : ℝ) :
    let s := Complex.I * (t : ℂ) + (K.pole : ℂ)
    highPrincipalHead K t =
      Complex.exp (5 * Complex.I * (t : ℂ)) * complexLogPolyMoment K.realProfile 0 s -
        Complex.exp (-(5 * (K.pole : ℂ))) * complexLogPolyMoment K.realProfile 5 s := by
  intro s
  have hs : 0 < s.re := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, zero_mul, zero_add, Complex.ratCast_re]
    exact (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have h₅ : (0 : ℝ) < 5 := by norm_num only
  let E := Complex.exp (-(5 * (K.pole : ℂ)))
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (K.realProfile.eval (5 - Real.log u))
  have h₀ := complex_log_poly_cutoff K.realProfile 5 hs zero_lt_one
  have h₁ := complex_log_poly_cutoff K.realProfile 5 hs (Real.exp_pos 5)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h₀.1 (h₀.1.symm.trans h₁.1)
  have htop :
    (∫ u in (1 : ℝ)..Real.exp 5, f u) =
      (Real.exp 5 : ℂ) ^ s * complexLogPolyMoment K.realProfile 0 s -
        complexLogPolyMoment K.realProfile 5 s := by
    have h := eq_sub_of_add_eq (add_comm _ _ |>.trans hsplit)
    simp only [Real.log_exp, sub_self] at h₁
    simp only [Real.log_one, sub_zero, Complex.ofReal_one, Complex.one_cpow, one_mul] at h₀
    exact h.trans (congrArg₂ (· - ·) h₁.2 h₀.2)
  have hhead := scaled_principal_head_log K.realProfile (K.pole : ℂ) (Complex.I * (t : ℂ)) h₅
  have hhead' : E * (∫ u in (1 : ℝ)..Real.exp 5, f u) = highPrincipalHead K t := by
    simp only [E, f, s, highPrincipalHead, Complex.ofReal_ratCast, mul_assoc (5 : ℂ),
      add_comm (K.pole : ℂ) (Complex.I * (t : ℂ))]
    simpa only [Complex.ofReal_ofNat, neg_mul] using hhead
  have hpow : E * (Real.exp 5 : ℂ) ^ s = Complex.exp (5 * Complex.I * (t : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
      Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_ofNat, ← Complex.exp_add]
    congr 1
    unfold s
    ring
  rw [← hhead', htop, mul_sub, ← mul_assoc, hpow]

/-- The full moment with its unit phase agrees with the compact square kernel. -/
private theorem high_full_moment_eq (K : HighGaussianKernel) (t : ℝ) :
    let z := Complex.I * (t : ℂ)
    let s := z + (K.pole : ℂ)
    Complex.exp (5 * z) * complexLogPolyMoment K.realProfile 0 s = highHeightKernel K t := by
  intro z s
  have hsre : s.re = (K.pole : ℝ) := by
    simp only [s, z, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add, Complex.ratCast_re]
  have hs : 0 < s.re :=
    hsre.symm ▸ (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hn : s ≠ 0 := fun h ↦ (ne_of_gt hs) (h ▸ Complex.zero_re)
  rw [high_principal_full_moment K hs, high_height_kernel_eq,
    add_comm (K.pole : ℂ) (Complex.I * (t : ℂ)), Finset.mul_sum]
  have h := high_gaussian_kernel_sum K (z := z) hn
  rw [← mul_assoc (5 : ℂ) Complex.I] at h
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_div_assoc, mul_comm (Complex.exp _)]
  dsimp only [s, z]
  rw [mul_assoc]

/-- At any real height the H25 multiplier is a square kernel and two explicit endpoint terms. -/
public theorem high_principal_multiplier_moments (K : HighGaussianKernel) (t : ℝ) :
    let s := Complex.I * (t : ℂ) + (K.pole : ℂ)
    highPrincipalMultiplier K t =
      highHeightKernel K t +
        4 * Complex.exp (-(5 * (K.pole : ℂ))) *
          (((K.realProfile.eval 5 : ℝ) : ℂ) / (1 / 2 + Complex.I * (t : ℂ)) -
            complexLogPolyMoment K.realProfile 5 s) := by
  intro s
  have h := high_principal_head_moments K t
  have hf := high_full_moment_eq K t
  dsimp only at h hf
  rw [← mul_assoc (5 : ℂ) Complex.I] at hf
  rw [hf] at h
  unfold s highPrincipalMultiplier highPrincipalEdge
  rw [h]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_ratCast]
  ring_nf

/-- The coefficient of degree `j` after translating the polynomial by `b`. -/
@[expose]
public noncomputable def principalMomentCoeff (P : Polynomial ℝ) (b : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * ((k.choose j : ℝ) * b ^ (k - j))

/-- In the finite moment, terms with a fixed inverse power can be added before taking norms. -/
public theorem principal_moment_by_power (P : Polynomial ℝ) (b : ℝ) (s : ℂ) :
    complexLogPolyMoment P b s =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (principalMomentCoeff P b j : ℂ) * ((j.factorial : ℂ) / s ^ (j + 1)) := by
  unfold complexLogPolyMoment principalMomentCoeff
  have hrow (k : ℕ) (hk : k ∈ Finset.range (P.natDegree + 1)) :
    (∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℂ) * (b : ℂ) ^ (k - j)) * ((j.factorial : ℂ) / s ^ (j + 1))) =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        ((k.choose j : ℂ) * (b : ℂ) ^ (k - j)) * ((j.factorial : ℂ) / s ^ (j + 1)) := by
    apply Finset.sum_subset (Finset.range_mono (Finset.mem_range.mp hk))
    intro j _ hj
    have hkj := Nat.lt_of_not_ge (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
    simp only [Nat.choose_eq_zero_of_lt hkj, Nat.cast_zero, zero_mul]
  calc
    _ =
        ∑ k ∈ Finset.range (P.natDegree + 1),
          ∑ j ∈ Finset.range (P.natDegree + 1),
            ((P.coeff k : ℂ) * ((k.choose j : ℂ) * (b : ℂ) ^ (k - j))) *
              ((j.factorial : ℂ) / s ^ (j + 1)) :=
      by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hrow k hk, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ (mul_assoc _ _ _).symm)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow,
        Finset.sum_mul]

/-- Center the endpoint polynomial before taking any norms. -/
public theorem high_principal_multiplier_centered (K : HighGaussianKernel) (t : ℝ) :
    let z := Complex.I * (t : ℂ)
    let s := z + (K.pole : ℂ)
    let r := 1 / 2 + z
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    highPrincipalMultiplier K t =
      highHeightKernel K t +
        4 * Complex.exp (-(5 * (K.pole : ℂ))) *
          (complexLogPolyMoment (Polynomial.C d * B - B.derivative) 5 s / r) := by
  intro z s r d B
  have hz : z.re = 0 := by
    simp only [z, Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  have hs : 0 < s.re := by
    simp only [s, Complex.add_re, hz, zero_add, Complex.ratCast_re]
    exact (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hd : (d : ℂ) + r = s := by
    simp only [d, r, s, Complex.ofReal_sub, Complex.ofReal_ratCast, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hr : r ≠ 0 := by
    have hh : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    have hre : r.re = 1 / 2 := by
      unfold r
      rw [← hh, Complex.add_re, Complex.ofReal_re, hz, add_zero]
    exact fun h ↦ (by norm_num only : (1 / 2 : ℝ) ≠ 0) (hre.symm.trans (h ▸ Complex.zero_re))
  have h := complex_moment_reflect B d 5 r (hd ▸ hs)
  dsimp only at h
  rw [hd] at h
  rw [high_principal_multiplier_moments]
  change
    highHeightKernel K t +
        4 * Complex.exp (-(5 * (K.pole : ℂ))) *
          (Complex.ofReal (B.eval 5) / r - complexLogPolyMoment B 5 s) =
      _
  rw [h, sub_div, mul_div_cancel_left₀ _ hr]

/-- A grouped moment divided by its pole has an inverse-square height bound.
The assumption on the pole norm also controls the higher inverse powers. -/
public theorem principal_moment_tail_le (P : Polynomial ℝ) (b T t : ℝ) (s r : ℂ) (hT : 0 < T)
    (ht : T ≤ t) (hs : t ≤ ‖s‖) (hr : t ≤ ‖r‖) :
    ‖complexLogPolyMoment P b s / r‖ ≤
      (∑ j ∈ Finset.range (P.natDegree + 1),
          |principalMomentCoeff P b j| * (j.factorial : ℝ) / T ^ j) /
        t ^ 2 := by
  rw [principal_moment_by_power, Finset.sum_div, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro j _
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_natCast,
    Real.norm_eq_abs, ← mul_div_assoc, div_div]
  have ht0 : 0 < t := hT.trans_le ht
  have hn0 : 0 ≤ ‖s‖ := norm_nonneg _
  have hpow := pow_le_pow_left₀ hT.le (ht.trans hs) j
  have hd : T ^ j * t ^ 2 ≤ ‖s‖ ^ (j + 1) * ‖r‖ := by
    rw [pow_succ ‖s‖ j, pow_two, ← mul_assoc]
    exact
      mul_le_mul (mul_le_mul hpow hs ht0.le (pow_nonneg hn0 _)) hr ht0.le
        (mul_nonneg (pow_nonneg hn0 _) hn0)
  exact
    div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (mul_pos (pow_pos hT _) (pow_pos ht0 _)) hd

end PseudoPrime.PrimeTestBounds.MillerRabin
