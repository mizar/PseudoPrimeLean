/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSplit656
public import PseudoPrime.LLS.PaperStatements.MellinKernelZeta
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSplit656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxNumerics656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZero644

/-! # Common xi and half-point residues for the section 132 comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the oscillating xi zero series for the symmetric kernel equals
the normalized difference of the two vertical xi integrals at scale `exp b`.
The kernel is regular at the half-unit point. -/
theorem quarter_symmetric_xi_656 (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    let x := Real.exp b
    let F := fun s : ℂ ↦
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) *
        (quarterSymmetricKernel656 s * (x : ℂ) ^ s)
    (∑' ρ, quarterSymmetricMellin656.zetaOscillatingZeroTerm x ρ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  intro x F
  have h :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity quarterSymmetricMellin656 hRH (a :=
      (-9 / 16 : ℝ)) (b := 9 / 16)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (Real.one_le_exp hb)
  have hz (G : ℂ → ℂ) : quarterSymmetricMellin656.weightedResidue G x (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv G (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  change
    Complex.I *
        ((∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + t * Complex.I)) -
          ∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + t * Complex.I)) =
      (2 * Real.pi * Complex.I) *
        (quarterSymmetricMellin656.weightedResidue _ x (-1 / 2) -
          ∑' ρ, quarterSymmetricMellin656.zetaOscillatingZeroTerm x ρ) at h
  rw [hz, zero_sub, mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div]
  simp only [mul_comm Complex.I]
  rw [eq_inv_mul_iff_mul_eq₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  linear_combination he

/-- Under RH and at nonnegative frequency, the real xi contour equals the
real part of the symmetric kernel's oscillating xi zero series. -/
theorem quarter_xi_cosine_656 (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    quarterCosineXi656 b =
      ∑' ρ, (quarterSymmetricMellin656.zetaOscillatingZeroTerm (Real.exp b) ρ).re := by
  rw [←
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm quarterSymmetricMellin656
        hRH (Real.exp_pos b))]
  exact (congrArg Complex.re (quarter_symmetric_xi_656 hRH hb)).symm

private theorem aux_axis_norm_le (t : ℝ) :
    ‖quarterSymmetricKernel656 (Complex.I * t)‖ ≤
      2 * ‖quarterKernel644.function (Complex.I * t)‖ := by
  rw [symmetric_axis, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    quarter_zero_norm_644, ← mul_div_assoc]
  have h : (107 / 100 : ℝ) ^ 2 + t ^ 2 ≤ (11 / 10 : ℝ) ^ 2 + t ^ 2 := by linarith only
  exact
    (div_le_div_of_nonneg_right (by norm_num only : (11 / 10 : ℝ) ^ 5 ≤ 2 * (107 / 100) ^ 5)
          (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) h 3))

/-- The absolute xi term at each nonnegative frequency is at most 10⁻⁶.
The wider pole kernel is bounded by twice the existing certified zeta mass. -/
theorem quarter_xi_cosine_abs_656 (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    |quarterCosineXi656 b| ≤ 1 / 1000000 := by
  let K := quarterSymmetricMellin656
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm K hRH (Real.exp_pos b)
  have h644 :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm quarterKernel644 hRH
      (Real.exp_pos (0 : ℝ))
  have he (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖K.zetaOscillatingZeroTerm (Real.exp b) ρ‖ ≤ 2 * ‖quarterKernel644.zetaKernelZeroTerm ρ‖ := by
    rw [LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm K (Real.exp_pos b)]
    unfold LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm
    rw [norm_mul, norm_mul, mul_left_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (aux_axis_norm_le _) (norm_nonneg _)
  have hsum : Summable (fun ρ ↦ ‖quarterKernel644.zetaKernelZeroTerm ρ‖) :=
    h644.norm.congr
      (fun ρ ↦
        LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm quarterKernel644
          (Real.exp_pos (0 : ℝ)) ρ)
  have h := hs.norm.tsum_le_tsum he (hsum.mul_left 2)
  rw [tsum_mul_left] at h
  rw [quarter_xi_cosine_656 hRH hb, ← Complex.re_tsum hs]
  refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs.norm).trans ?_)
  exact
    h.trans
      ((mul_le_mul_of_nonneg_left (quarter_zeta_mass_644 hRH) (by norm_num only)).trans
        (by norm_num only))

/-- A uniformly bounded real function contributes at most its bound
times the absolute coefficient sum and half its square. -/
theorem quarter_aux_mix_bound_656 (F : ℝ → ℝ) {e : ℝ} (he : 0 ≤ e)
    (hF : ∀ i, |F (quarterAuxFrequency656 i)| ≤ e)
    (hD : ∀ i j, |F (quarterAuxFrequency656 i - quarterAuxFrequency656 j)| ≤ e) :
    |quarterAuxMix656 F| ≤ 4 * e := by
  let c := quarterAuxCoeff656
  let s := ∑ i, |c i|
  have hs₀ : 0 ≤ s := Finset.sum_nonneg (fun i _ ↦ abs_nonneg (c i))
  have hs : s ≤ 2 := by
    have h : (∑ i, |quarterAuxCoeffRat656 i|) ≤ 2 := by decide +kernel
    have hr := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [s, c, quarterAuxCoeff656, Rat.cast_sum, Rat.cast_abs, Rat.cast_ofNat] using hr
  have hp i j := mul_le_mul_of_nonneg_left (hD i j) (abs_nonneg (c i * c j))
  have hrow (i : Fin 7) :
    |∑ j, c i * c j * F (quarterAuxFrequency656 i - quarterAuxFrequency656 j)| ≤
      |c i| * (s * e) := by
    have h :
      |∑ j, c i * c j * F (quarterAuxFrequency656 i - quarterAuxFrequency656 j)| ≤
        ∑ j, |c i * c j| * e :=
      (Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (fun j ↦ c i * c j * F (quarterAuxFrequency656 i - quarterAuxFrequency656 j))).trans
        (Finset.sum_le_sum (fun j _ ↦ by simpa only [abs_mul] using hp i j))
    simpa only [abs_mul, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, s] using h
  have hP :
    |∑ i, ∑ j, c i * c j * F (quarterAuxFrequency656 i - quarterAuxFrequency656 j)| ≤
      s * (s * e) := by
    unfold s
    rw [Finset.sum_mul]
    exact
      (Finset.abs_sum_le_sum_abs (s := Finset.univ) _).trans (Finset.sum_le_sum (fun i _ ↦ hrow i))
  have hS : |∑ i, c i * F (quarterAuxFrequency656 i)| ≤ s * e := by
    unfold s
    rw [Finset.sum_mul]
    exact
      (Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (fun i ↦ c i * F (quarterAuxFrequency656 i))).trans
        (Finset.sum_le_sum
          (fun i _ ↦ by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hF i) (abs_nonneg (c i))))
  have h₂ := mul_le_mul_of_nonneg_right hs he
  have h₃ := mul_le_mul hs h₂ (mul_nonneg hs₀ he) (by norm_num only : (0 : ℝ) ≤ 2)
  unfold quarterAuxMix656
  apply (abs_sub _ _).trans
  rw [abs_div, abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
  dsimp only [c] at hP hS
  linarith only [hS, hP, h₂, h₃]

/-- The three common xi contributions in the seven-frequency combination
cost at most twelve millionths. -/
theorem quarter_seven_xi_cap_656 (hRH : RiemannHypothesis) :
    |3 * quarterAuxMix656 (fun t ↦ quarterCosineXi656 |t|)| ≤ 0.000012 := by
  have h :=
    quarter_aux_mix_bound_656 (fun t ↦ quarterCosineXi656 |t|) (by norm_num only)
      (fun _ ↦ quarter_xi_cosine_abs_656 hRH (abs_nonneg _))
      (fun _ _ ↦ quarter_xi_cosine_abs_656 hRH (abs_nonneg _))
  rw [abs_mul, abs_of_pos (by norm_num only : (0 : ℝ) < 3)]
  linarith only [h]

/-- The pair of symmetric residues at the two half-unit points is a common
rational factor times the sum of the two real exponentials. -/
theorem quarter_cosine_pole_pair_656 (t : ℝ) :
    let H := fun u : ℝ ↦ (quarterSymmetricKernel656 (u : ℂ) * (Real.exp t : ℂ) ^ (u : ℂ)).re
    H (-1 / 2) + H (1 / 2) =
      ((11 / 10 : ℝ) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3) *
        (Real.exp (-t / 2) + Real.exp (t / 2)) := by
  intro H
  have h (u : ℝ) (hu : u ^ 2 = 1 / 4) :
    H u = ((11 / 10 : ℝ) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3) * Real.exp (t * u) := by
    have hk :
      quarterSymmetricKernel656 (u : ℂ) =
        (((11 / 10 : ℝ) ^ 5 / (((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3) : ℝ) : ℂ) := by
      unfold quarterSymmetricKernel656
      rw [← hu, ← Complex.ofReal_ofNat (11 : ℕ), ← Complex.ofReal_ofNat (10 : ℕ)]
      push_cast
      ring
    dsimp only [H]
    rw [hk, ← Complex.ofReal_cpow (Real.exp_pos t).le, ← Complex.ofReal_mul, Complex.ofReal_re,
      Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  rw [h _ (by norm_num only), h _ (by norm_num only)]
  rw [show t * (-1 / 2) = -t / 2 by ring, show t * (1 / 2) = t / 2 by ring]
  ring

/-- The sum of the two half-point exponential factors in the cosine residue. -/
noncomputable def quarterAuxResidue656 (t : ℝ) : ℝ :=
  Real.exp (-|t| / 2) + Real.exp (|t| / 2)

private noncomputable def residueTaylor (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 54, (-|t| / 2) ^ j / (j.factorial : ℝ)) +
    (∑ j ∈ Finset.range 54, (|t| / 2) ^ j / (j.factorial : ℝ))

private def residueTaylorRat (t : ℚ) : ℚ :=
  auxExpTaylor656 (-|t| / 2) + auxExpTaylor656 (|t| / 2)

private theorem residue_taylor_cast (t : ℚ) : (residueTaylorRat t : ℝ) = residueTaylor t := by
  simp only [residueTaylorRat, residueTaylor, auxExpTaylor656, Rat.cast_add, Rat.cast_sum,
    Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_abs, Rat.cast_ofNat, Rat.cast_natCast]

private theorem residue_taylor_error (t : ℚ) (ht : |t| ≤ 10) :
    |quarterAuxResidue656 t - residueTaylor t| ≤ 2 / 10 ^ 16 := by
  have hp : |((|t| / 2 : ℚ) : ℝ)| ≤ 10 := by
    have h : |(t : ℝ)| ≤ 10 := by exact_mod_cast ht
    simp only [Rat.cast_div, Rat.cast_abs, Rat.cast_ofNat]
    rw [abs_of_nonneg (div_nonneg (abs_nonneg _) (by norm_num only))]
    linarith only [h]
  have hm : |((-|t| / 2 : ℚ) : ℝ)| ≤ 10 := by simpa only [neg_div, Rat.cast_neg, abs_neg] using hp
  have h₁ := aux_exp_error_656 (-|t| / 2) hm
  have h₂ := aux_exp_error_656 (|t| / 2) hp
  have h := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  rw [← add_sub_add_comm] at h
  rw [← residue_taylor_cast]
  simp only [quarterAuxResidue656, residueTaylorRat, Rat.cast_add, Rat.cast_div, Rat.cast_neg,
    Rat.cast_abs, Rat.cast_ofNat] at h ⊢
  linarith only [h]

private def residueMixRat : ℚ :=
  (∑ i,
        ∑ j,
          quarterAuxCoeffRat656 i * quarterAuxCoeffRat656 j *
            residueTaylorRat (auxFrequency i - auxFrequency j)) /
      2 -
    ∑ i, quarterAuxCoeffRat656 i * residueTaylorRat (auxFrequency i)

private theorem residue_mix_cast : (residueMixRat : ℝ) = quarterAuxMix656 residueTaylor := by
  simp only [residueMixRat, quarterAuxMix656, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, aux_coeff_cast, residue_taylor_cast, aux_frequency_cast]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- Kernel reduction evaluates the Taylor sums for the seven frequencies and their differences.
/-- The signed combination of both half-point residues for the three
characters recovers at least 3.8261443. -/
theorem quarter_aux_residue_lower_656 :
    (3.8261443 : ℝ) ≤
      3 * ((11 / 10 : ℝ) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3) *
        quarterAuxMix656 quarterAuxResidue656 := by
  have ht₁ : ∀ i, |auxFrequency i| ≤ 10 := by decide +kernel
  have ht₂ : ∀ i j, |auxFrequency i - auxFrequency j| ≤ 10 := by decide +kernel
  have h :=
    quarter_aux_mix_bound_656 (fun t ↦ quarterAuxResidue656 t - residueTaylor t)
      (by norm_num only : (0 : ℝ) ≤ 2 / 10 ^ 16)
      (fun i ↦ by simpa only [aux_frequency_cast] using residue_taylor_error _ (ht₁ i))
      (fun i j ↦ by
        simpa only [Rat.cast_sub, aux_frequency_cast] using residue_taylor_error _ (ht₂ i j))
  have he :
    quarterAuxMix656 (fun t ↦ quarterAuxResidue656 t - residueTaylor t) =
      quarterAuxMix656 quarterAuxResidue656 - quarterAuxMix656 residueTaylor := by
    unfold quarterAuxMix656
    simp only [mul_sub, Finset.sum_sub_distrib, sub_div]
    ring
  rw [he, ← residue_mix_cast] at h
  have hn : (70063265 : ℚ) / 100000000 ≤ residueMixRat := by decide +kernel
  have hn' := (Rat.cast_le (K := ℝ)).mpr hn
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hn'
  have hd := (abs_le.mp h).1
  linarith only [hd, hn']

/-- The symmetric conductor coefficient in the signed auxiliary combination. -/
noncomputable def quarterAuxConductor656 : ℝ :=
  quarterAuxMix656 (fun t ↦ quarterSymmetricProfile656 (Real.exp |t|)⁻¹)

/-- With the xi and half-point residues evaluated, the part of the cosine
comparison independent of Euler terms reduces to the conductor term minus
a uniform numerical gain. -/
theorem quarter_cosine_core_cap_656 (hRH : RiemannHypothesis) (L : ℝ) :
    quarterAuxMix656 (quarterCosineCore656 L) ≤ L * quarterAuxConductor656 - 3.8261323 := by
  let M : ℝ := (11 / 10) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3
  have he (t : ℝ) :
    quarterCosineCore656 L t =
      quarterCosineXi656 |t| * 3 + quarterAuxResidue656 t * (-3 * M) +
        quarterSymmetricProfile656 (Real.exp |t|)⁻¹ * L := by
    have h := quarter_cosine_pole_pair_656 |t|
    dsimp only at h
    unfold quarterCosineCore656 quarterAuxResidue656 M
    dsimp only
    linear_combination -3 * h
  have hx := (abs_le.mp (quarter_seven_xi_cap_656 hRH)).2
  have hr := quarter_aux_residue_lower_656
  rw [funext he]
  simp only [aux_mix_add_656, aux_mix_scale_656, quarterAuxConductor656, M]
  linarith only [hx, hr]

/-- The auxiliary forward comparison after absorbing the Euler, xi and
residue costs. Both finite intervals share the same constant gain. -/
theorem quarter_forward_residue_gain_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    (∑' n, quarterKernel656.summand a X n).re + (∑' n, quarterKernel656.summand b X n).re +
        (∑' n, quarterKernel656.summand c X n).re +
        (quarterShiftedForward656 a X + quarterShiftedForward656 b X +
          quarterShiftedForward656 c X) +
        3.673430088 ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a X).re + (contourRemainder656 b X).re +
          (contourRemainder656 c X).re) +
        (Real.log p + Real.log q + Real.log r) * quarterAuxConductor656 := by
  have h := quarter_three_forward_euler_656 ha hb hc hp hq hr hG hX ht hpa hpb hpc
  have hx := quarter_cosine_core_cap_656 hG.riemann (Real.log p + Real.log q + Real.log r)
  linarith only [h, hx]

end PseudoPrime.PrimeTestBounds.MillerRabin
