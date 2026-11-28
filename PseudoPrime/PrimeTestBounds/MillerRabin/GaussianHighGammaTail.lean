/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighSignCert
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell

/-! # Tail deficits for the high Gaussian gamma bound -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Beyond the certified cutoff (65 for K186 and 80 for K196), the physical
profile is nonnegative. This supplies the sign needed for both H37 moments. -/
private theorem high_profile_nonneg_after_cutoff (K : HighGaussianKernel) {t : ℝ}
    (ht : (profileCorrectionEnd K : ℝ) ≤ t) : 0 ≤ K.realProfile.eval t := by
  exact high_int_profile_sign K _ (high_correction_profile_check K) 0 ht

/-- For either high kernel, the negative parts of the two H37 gamma moments
are bounded by their cutoff deficits. The convolution deficit is multiplied
by the exponential growth from the cutoff, while the decaying moment has
no growth factor. -/
theorem high_gamma_tail_deficits (K : HighGaussianKernel) {s d z : ℝ}
    (hz : (profileCorrectionEnd K : ℝ) ≤ z) :
    let a : ℝ := profileCorrectionEnd K
    let I := fun b : ℝ ↦ ∫ t in (0 : ℝ)..b, Real.exp (s * (b - t)) * K.realProfile.eval t
    let J := fun b : ℝ ↦ ∫ t in (0 : ℝ)..b, K.realProfile.eval t * Real.exp (-d * t)
    max (-I z) 0 ≤ Real.exp (s * (z - a)) * max (-I a) 0 ∧ max (-J z) 0 ≤ max (-J a) 0 := by
  intro a I J
  have hp (t : ℝ) (ht : t ∈ Set.Icc a z) := high_profile_nonneg_after_cutoff K ht.1
  exact
    ⟨high_gamma_conv_neg_le K hz hp,
      high_gamma_moment_neg_le hz
        (K.realProfile.continuous.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
        (fun t ht ↦ mul_nonneg (hp t ht) (Real.exp_pos _).le)⟩

/-- The rational row computes exactly the translated real coefficient sum
appearing in H36. -/
theorem high_gamma_shift_moment_cast (K : HighGaussianKernel) (a s : ℚ) :
    let Q := K.realProfile.comp (Polynomial.X + Polynomial.C (a : ℝ))
    (highGammaShiftMoment K a s : ℝ) =
      ∑ k ∈ Finset.range (Q.natDegree + 1),
        Q.coeff k * ((k.factorial : ℝ) / (s : ℝ) ^ (k + 1)) := by
  intro Q
  let P := K.ratProfile.comp (Polynomial.X + Polynomial.C a)
  have hmap : P.map (Rat.castHom ℝ) = Q := by
    simp only [P, Q, Polynomial.map_comp, high_comp_profile_map, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_C, Rat.coe_castHom]
  have hd : Q.natDegree ≤ 2 * K.degree + 3 := by
    rw [← hmap, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective (α := ℝ))]
    exact
      Polynomial.natDegree_comp_le.trans
        (by simpa only [Polynomial.natDegree_X_add_C, mul_one] using high_rat_profile_degree K)
  have hterm (k : ℕ) (hk : k ∈ Finset.range (2 * K.degree + 4)) :
    ((K.cellPowerRow a 1)[k]?.getD 0 * ((k.factorial : ℚ) / s ^ (k + 1)) : ℚ) =
      P.coeff k * ((k.factorial : ℚ) / s ^ (k + 1)) := by
    rw [high_cell_power_coeff K a 1 (Finset.mem_range.mp hk), Polynomial.C_1, one_mul]
  rw [highGammaShiftMoment, Rat.cast_sum]
  calc
    _ =
        ∑ k ∈ Finset.range (2 * K.degree + 4),
          Q.coeff k * ((k.factorial : ℝ) / (s : ℝ) ^ (k + 1)) :=
      by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hterm k hk, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, ← hmap,
        Polynomial.coeff_map]
      rfl
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hd))
      intro k _ hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (Nat.lt_of_not_ge (fun h ↦ hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))),
        zero_mul]

/-- Evaluate the two finite gamma moments at a rational endpoint. Their
common translated moment uses the computable rational coefficient row. -/
theorem high_gamma_rational_moments (K : HighGaussianKernel) {a s : ℚ} (ha : 0 ≤ a) (hs : 0 < s) :
    let z : ℝ := a
    let r : ℝ := s
    (∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-r * t)) =
        highProfileLaplace K r - Real.exp (-r * z) * (highGammaShiftMoment K a s : ℝ) ∧
      (∫ t in (0 : ℝ)..z, Real.exp (r * (z - t)) * K.realProfile.eval t) =
        Real.exp (r * z) * highProfileLaplace K r - (highGammaShiftMoment K a s : ℝ) := by
  intro z r
  have hr : 0 < r := Rat.cast_pos.mpr hs
  have hz : 0 ≤ z := Rat.cast_nonneg.mpr ha
  rw [high_gamma_shift_moment_cast, high_profile_finite_laplace K hr hz,
    high_gamma_conv_moment K hr hz]
  exact ⟨rfl, rfl⟩

/-- An upper bound for the translated moment, together with a bound on the
endpoint exponential, gives a lower bound for the decaying gamma moment. -/
theorem high_gamma_endpoint_lower (K : HighGaussianKernel) {a s E M : ℚ} (ha : 0 ≤ a) (hs : 0 < s)
    (hM : 0 ≤ M) (hshift : highGammaShiftMoment K a s ≤ M)
    (hE : Real.exp (-(s : ℝ) * (a : ℝ)) ≤ (E : ℝ)) :
    ((highGammaRatTransform K s - E * M : ℚ) : ℝ) ≤
      ∫ t in (0 : ℝ)..(a : ℝ), K.realProfile.eval t * Real.exp (-(s : ℝ) * t) := by
  rw [(high_gamma_rational_moments K ha hs).1, Rat.cast_sub, Rat.cast_mul,
    high_gamma_transform_cast]
  exact
    sub_le_sub_left
      ((mul_le_mul_of_nonneg_left (Rat.cast_le.mpr hshift) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_right hE (Rat.cast_nonneg.mpr hM)))
      _

/-- The rational cutoff test certifies that the decaying moment is nonnegative. -/
theorem high_gamma_endpoint_nonneg (K : HighGaussianKernel) {a s : ℚ} (ha : 0 ≤ a) (hs : 0 < s)
    (h :
      negativeEndpointExpUpper (s * a) * max 0 (highGammaShiftMoment K a s) ≤
        highGammaRatTransform K s) :
    0 ≤ ∫ t in (0 : ℝ)..(a : ℝ), K.realProfile.eval t * Real.exp (-(s : ℝ) * t) := by
  have hE := negative_endpoint_exp_upper_valid (mul_nonneg hs.le ha)
  rw [Rat.cast_mul, ← neg_mul] at hE
  exact
    (Rat.cast_nonneg.mpr (sub_nonneg.mpr h)).trans
      (high_gamma_endpoint_lower K ha hs (le_max_left _ _) (le_max_right _ _) hE)

/-- Nonnegativity of the decaying moment at the certified boundary persists
at every later point. -/
theorem high_gamma_decay_nonneg (K : HighGaussianKernel) {s z : ℝ}
    (hz : (profileCorrectionEnd K : ℝ) ≤ z)
    (ha :
      0 ≤ ∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ), K.realProfile.eval t * Real.exp (-s * t)) :
    0 ≤ ∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-s * t) := by
  have h := (high_gamma_tail_deficits K (s := s) (d := s) hz).2
  change
    max (-(∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-s * t))) 0 ≤
      max
        (-(∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ), K.realProfile.eval t * Real.exp (-s * t)))
        0 at h
  rw [max_eq_right (neg_nonpos.mpr ha)] at h
  exact neg_nonpos.mp ((le_max_left _ _).trans h)

/-- The convolution has the same sign as the decaying moment at the
same rate, since their ratio is a positive exponential factor. -/
theorem high_gamma_conv_nonneg (K : HighGaussianKernel) {s z : ℝ}
    (h : 0 ≤ ∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-s * t)) :
    0 ≤ ∫ t in (0 : ℝ)..z, Real.exp (s * (z - t)) * K.realProfile.eval t := by
  have he (t : ℝ) :
    Real.exp (s * (z - t)) * K.realProfile.eval t =
      Real.exp (s * z) * (K.realProfile.eval t * Real.exp (-s * t)) := by
    rw [mul_sub, sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc, mul_comm (Real.exp (-(s * t)))]
  simpa only [he, intervalIntegral.integral_const_mul] using mul_nonneg (Real.exp_pos _).le h

/-- The two subtracted moments in H33 contribute no positive charge beyond
the cutoff if both scaled moments pass the endpoint nonnegativity test. -/
theorem high_gamma_tail_nonneg (K : HighGaussianKernel) {s d z : ℝ}
    (hz : (profileCorrectionEnd K : ℝ) ≤ z)
    (hs :
      0 ≤ ∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ), K.realProfile.eval t * Real.exp (-s * t))
    (hd :
      0 ≤ ∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ), K.realProfile.eval t * Real.exp (-d * t)) :
    (0 ≤ ∫ t in (0 : ℝ)..z, Real.exp (s * (z - t)) * K.realProfile.eval t) ∧
      (0 ≤ ∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-d * t)) := by
  exact
    ⟨high_gamma_conv_nonneg K (high_gamma_decay_nonneg K hz hs), high_gamma_decay_nonneg K hz hd⟩

/-- Beyond the certified cutoff, every derivative of the physical profile is
nonnegative. Termwise coefficient upper bounds therefore bound the H33 sum
without the derivative sign corrections from H34. -/
theorem high_gamma_tail_sum_le (K : HighGaussianKernel) {z : ℝ}
    (hz : (profileCorrectionEnd K : ℝ) ≤ z) (N : ℕ) {g u : ℕ → ℝ}
    (hgu : ∀ j ∈ Finset.range N, g j ≤ u j) :
    (∑ j ∈ Finset.range N, g j * ((Polynomial.derivative^[j]) K.realProfile).eval z) ≤
      ∑ j ∈ Finset.range N, u j * ((Polynomial.derivative^[j]) K.realProfile).eval z := by
  exact
    Finset.sum_le_sum fun j hj ↦
      mul_le_mul_of_nonneg_right (hgu j hj)
        (high_int_profile_sign K _ (high_correction_profile_check K) j hz)

/-- Bound the H33 expression beyond the cutoff by upper gamma coefficients
and the two propagated endpoint deficits. The remaining trivial zeros
contribute a nonpositive term. -/
theorem high_gamma_tail_expression_le (K : HighGaussianKernel) {s d z C D R NI NJ : ℝ}
    (hz : (profileCorrectionEnd K : ℝ) ≤ z)
    (hs :
      max
          (-(∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ),
              Real.exp (s * ((profileCorrectionEnd K : ℝ) - t)) * K.realProfile.eval t))
          0 ≤
        NI)
    (hd :
      max
          (-(∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ),
              K.realProfile.eval t * Real.exp (-d * t)))
          0 ≤
        NJ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R) (N : ℕ) {g u : ℕ → ℝ}
    (hgu : ∀ j ∈ Finset.range N, g j ≤ u j) :
    let I := ∫ t in (0 : ℝ)..z, Real.exp (s * (z - t)) * K.realProfile.eval t
    let J := ∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-d * t)
    C * ((∑ j ∈ Finset.range N, g j * ((Polynomial.derivative^[j]) K.realProfile).eval z) - I) -
        D * J -
        R ≤
      C * (∑ j ∈ Finset.range N, u j * ((Polynomial.derivative^[j]) K.realProfile).eval z) +
        C * (Real.exp (s * (z - (profileCorrectionEnd K : ℝ))) * NI) +
        D * NJ := by
  intro I J
  obtain ⟨hI, hJ⟩ := high_gamma_tail_deficits K (s := s) (d := d) hz
  have hi : -I ≤ Real.exp (s * (z - (profileCorrectionEnd K : ℝ))) * NI :=
    (le_max_left _ _).trans (hI.trans (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le))
  have hj : -J ≤ NJ := (le_max_left _ _).trans (hJ.trans hd)
  have hmain := mul_le_mul_of_nonneg_left (high_gamma_tail_sum_le K hz N hgu) hC
  linarith only [hmain, mul_le_mul_of_nonneg_left hi hC, mul_le_mul_of_nonneg_left hj hD, hR]

/-- A rational deficit bound applies even when the endpoint moment is negative. -/
theorem high_gamma_endpoint_deficit (K : HighGaussianKernel) {a s N : ℚ} (ha : 0 ≤ a) (hs : 0 < s)
    (hN : 0 ≤ N)
    (h :
      negativeEndpointExpUpper (s * a) * max 0 (highGammaShiftMoment K a s) -
          highGammaRatTransform K s ≤
        N) :
    max (-(∫ t in (0 : ℝ)..(a : ℝ), K.realProfile.eval t * Real.exp (-(s : ℝ) * t))) 0 ≤
      (N : ℝ) := by
  have hE := negative_endpoint_exp_upper_valid (mul_nonneg hs.le ha)
  rw [Rat.cast_mul, ← neg_mul] at hE
  have hlow := high_gamma_endpoint_lower K ha hs (le_max_left _ _) (le_max_right _ _) hE
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  exact
    max_le ((neg_le_neg hlow).trans (by simpa only [Rat.cast_sub, Rat.cast_mul, neg_sub] using hr))
      (Rat.cast_nonneg.mpr hN)

/-- The squared kernel transform is nonnegative on the real axis, including
the negative rates of the remaining trivial zeros in H33. -/
theorem high_profile_laplace_nonneg (K : HighGaussianKernel) (s : ℝ) :
    0 ≤ highProfileLaplace K s := by
  by_cases hs : s = 0
  · simp only [hs, highProfileLaplace, zero_pow (Nat.succ_ne_zero _), div_zero,
      Finset.sum_const_zero, le_refl]
  · rw [high_profile_laplace_square K hs]
    have he : 2 * K.degree + 4 = 2 * (K.degree + 2) := by ring
    rw [he, pow_mul]
    exact
      div_nonneg
        (mul_nonneg (Rat.cast_nonneg.mpr (high_gaussian_normalization_pos K).le) (sq_nonneg _))
        (pow_nonneg (sq_nonneg _) _)

/-- The remaining trivial-zero series in H33 is nonnegative. The indexing
starts at the second trivial zero, after the first has been absorbed. -/
theorem high_gamma_trivial_tail_nonneg (K : HighGaussianKernel) (d z : ℝ) :
    0 ≤
      ∑' k : ℕ,
        Real.exp (-((1 / 2 : ℝ) + 2 * (k + 2)) * z) * highProfileLaplace K (d - 2 * (k + 2)) := by
  exact tsum_nonneg fun k ↦ mul_nonneg (Real.exp_pos _).le (high_profile_laplace_nonneg K _)

/-- A lower bound of `-M` on the integrand over the new interval bounds
the increase in the negative part of its finite moment, as in H35. -/
theorem gamma_moment_deficit_local {f : ℝ → ℝ} {a z M : ℝ} (haz : a ≤ z) (hf : Continuous f)
    (hM : 0 ≤ M) (hfM : ∀ t ∈ Set.Icc a z, -M ≤ f t) :
    max (-(∫ t in (0 : ℝ)..z, f t)) 0 ≤ max (-(∫ t in (0 : ℝ)..a, f t)) 0 + (z - a) * M := by
  have hi := hf.intervalIntegrable (μ := MeasureTheory.volume) a z
  have hm := intervalIntegral.integral_mono_on haz (continuous_const.intervalIntegrable a z) hi hfM
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_neg] at hm
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 a) hi
  apply max_le
  · have ha := le_max_left (-(∫ t in (0 : ℝ)..a, f t)) 0
    linarith only [ha, hm, hadd]
  · exact add_nonneg (le_max_right _ _) (mul_nonneg (sub_nonneg.mpr haz) hM)

/-- The H35 decaying moment gains at most the interval length times the
left-endpoint exponential and a bound on the negative physical profile. -/
theorem high_gamma_decay_local (K : HighGaussianKernel) {a z d M : ℝ} (haz : a ≤ z) (hd : 0 ≤ d)
    (hM : 0 ≤ M) (hB : ∀ t ∈ Set.Icc a z, -M ≤ K.realProfile.eval t) :
    let J := fun b : ℝ ↦ ∫ t in (0 : ℝ)..b, K.realProfile.eval t * Real.exp (-d * t)
    max (-J z) 0 ≤ max (-J a) 0 + (z - a) * (Real.exp (-d * a) * M) := by
  intro J
  refine
    gamma_moment_deficit_local haz
      (K.realProfile.continuous.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
      (mul_nonneg (Real.exp_pos _).le hM) (fun t ht ↦ ?_)
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hd))
  change -(Real.exp (-d * a) * M) ≤ _
  rw [mul_comm (Real.exp (-d * a)) M, ← neg_mul]
  exact
    (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hM)).trans
      (mul_le_mul_of_nonneg_right (hB t ht) (Real.exp_pos _).le)

/-- The H35 convolution deficit over a cell is at most its left-endpoint
deficit plus the interval length times the profile deficit bound, all
multiplied by the exponential growth over the interval. -/
theorem high_gamma_conv_local (K : HighGaussianKernel) {a z s M : ℝ} (haz : a ≤ z) (hs : 0 ≤ s)
    (hM : 0 ≤ M) (hB : ∀ t ∈ Set.Icc a z, -M ≤ K.realProfile.eval t) :
    let I := fun b : ℝ ↦ ∫ t in (0 : ℝ)..b, Real.exp (s * (b - t)) * K.realProfile.eval t
    max (-I z) 0 ≤ Real.exp (s * (z - a)) * (max (-I a) 0 + (z - a) * M) := by
  intro I
  let E := Real.exp (s * (z - a))
  let f := fun t : ℝ ↦ Real.exp (s * (z - t)) * K.realProfile.eval t
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      K.realProfile.continuous
  have hlocal :=
    gamma_moment_deficit_local (f := f) haz hf (mul_nonneg (Real.exp_pos _).le hM : 0 ≤ E * M)
      (fun t ht ↦ by
        have he : Real.exp (s * (z - t)) ≤ E :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 _) hs)
        rw [mul_comm E M, ← neg_mul]
        exact
          (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hM)).trans
            ((by
              simpa only [f, mul_comm (-M)] using
                mul_le_mul_of_nonneg_left (hB t ht) (Real.exp_pos (s * (z - t))).le)))
  have he (t : ℝ) : f t = E * (Real.exp (s * (a - t)) * K.realProfile.eval t) := by
    rw [← mul_assoc]
    dsimp only [f, E]
    rw [← Real.exp_add]
    congr 2
    ring
  have ha : (∫ t in (0 : ℝ)..a, f t) = E * I a := by
    simp only [he, intervalIntegral.integral_const_mul, I]
  rw [ha, ← mul_neg] at hlocal
  have hmax := mul_max_of_nonneg (-I a) 0 (show 0 ≤ E from (Real.exp_pos _).le)
  rw [mul_zero] at hmax
  rw [← hmax] at hlocal
  rw [mul_left_comm (z - a) E M, ← mul_add] at hlocal
  exact hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
