/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianFirstCutoff
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincTailAnchorRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroConjugateSum
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianFirstCutoff
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
public import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Shared rational spectral certificate for K137 and K197 -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def spectralCoeff : Fin 6 → ℚ :=
  ![-26643897 / 163840, -898317 / 4096, -25137 / 128, -1071 / 16, 69, 72]

private def spectralBracket : Fin 29 → ℚ :=
  ![14473 / 1024, 10763 / 512, 25611 / 1024, 31155 / 1024, 33725 / 1024, 4811 / 128, 10475 / 256,
    22183 / 512, 49157 / 1024, 6371 / 128, 54241 / 1024, 7225 / 128, 60771 / 1024, 62291 / 1024,
    66675 / 1024, 68689 / 1024, 71215 / 1024, 18449 / 256, 77521 / 1024, 19749 / 256, 81241 / 1024,
    21225 / 256, 86769 / 1024, 89523 / 1024, 22735 / 256, 94711 / 1024, 48461 / 512, 98171 / 1024,
    101203 / 1024]

private def spectralRounded : Fin 29 → ℕ :=
  ![5365032655, 2348780159, 1642061755, 1098893126, 934588307, 713914311, 600600871, 534699475,
    434219813, 403504022, 355690017, 312741257, 282577142, 268804565, 234273831, 220602268,
    205083037, 190858148, 172800424, 166352012, 157208772, 143844099, 137665557, 129262192,
    125235072, 115390798, 110149406, 107344890, 100966473]

/-- The common kernel's exponential prefactor lies below the rational
upper endpoint used by the spectral certificate. -/
public theorem gaussian_spectral_prefactor_le :
    ((11 / 10 : ℝ) ^ 5 * Real.exp (-((11 / 10 : ℝ) * (21 / 8)))) / 120 ≤
      (747750760233171678801217976482971 / 1000000000000000000000000000000000000 : ℝ) := by
  let C : ℚ := 747750760233171678801217976482971 / 1000000000000000000000000000000000000
  have hq :
    (11 / 10 : ℚ) ^ 5 / 120 ≤
      C * (∑ j ∈ Finset.range 55, (231 / 80 : ℚ) ^ j / (j.factorial : ℚ)) := by
    decide +kernel
  have h := (Rat.cast_le (K := ℝ)).mpr hq
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sum,
    Rat.cast_natCast] at h
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 231 / 80) 55
  have hC : 0 ≤ (C : ℝ) := by norm_num only [C, Rat.cast_div, Rat.cast_ofNat]
  have hp := h.trans (mul_le_mul_of_nonneg_left ht hC)
  rw [show (11 / 10 : ℝ) * (21 / 8) = 231 / 80 by norm_num only, Real.exp_neg,
    show
      (11 / 10 : ℝ) ^ 5 * (Real.exp (231 / 80))⁻¹ / 120 =
        ((11 / 10 : ℝ) ^ 5 / 120) / Real.exp (231 / 80)
      by ring]
  simpa only [C, Rat.cast_div, Rat.cast_ofNat] using (div_le_iff₀ (Real.exp_pos _)).mpr hp

/-- Height majorant from the common K137 and K197 spectral profile. -/
public def gaussianSpectralHeight (t : ℚ) : ℚ :=
  4 * (747750760233171678801217976482971 / 1000000000000000000000000000000000000) *
      (∑ j : Fin 6, |spectralCoeff j| / t ^ j.val) +
    (161051 / 100000) / t ^ 4

private theorem spectral_row_le (i : Fin 29) :
    2 * gaussianSpectralHeight (spectralBracket i) / spectralBracket i ^ 2 ≤
      (spectralRounded i : ℚ) / 1000000000000 := by
  fin_cases i <;> decide +kernel

private theorem spectral_tail_le :
    gaussianSpectralHeight 100 * (7872913 / 588750000) ≤ (6592786327 / 1000000000000 : ℚ) := by
  decide +kernel

/-- The rational absolute spectral budget sums the 29 conjugate pairs and
the height-100 tail. Both K137 and K197 use this budget. -/
public def gaussianSpectralBudget : ℚ :=
  (∑ i : Fin 29, 2 * gaussianSpectralHeight (spectralBracket i) / spectralBracket i ^ 2) +
    gaussianSpectralHeight 100 * (7872913 / 588750000)

/-- The shared finite arithmetic certificate bounds the absolute spectral budget by 1/40. -/
public theorem gaussian_spectral_budget_lt : gaussianSpectralBudget < 1 / 40 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ spectral_row_le i)
  unfold gaussianSpectralBudget
  exact (add_le_add h spectral_tail_le).trans_lt (by decide +kernel)

/-- The height majorant evaluated on real ordinates. -/
public noncomputable def gaussianSpectralHeightReal (t : ℝ) : ℝ :=
  4 * (747750760233171678801217976482971 / 1000000000000000000000000000000000000) *
      (∑ j : Fin 6, |(spectralCoeff j : ℝ)| / t ^ j.val) +
    (161051 / 100000) / t ^ 4

private theorem spectral_height_cast (t : ℚ) :
    (gaussianSpectralHeight t : ℝ) = gaussianSpectralHeightReal t := by
  simp only [gaussianSpectralHeight, gaussianSpectralHeightReal, Rat.cast_add, Rat.cast_mul,
    Rat.cast_div, Rat.cast_sum, Rat.cast_abs, Rat.cast_pow, Rat.cast_ofNat]

private theorem spectral_height_nonneg (t : ℝ) (h : 0 ≤ t) : 0 ≤ gaussianSpectralHeightReal t := by
  unfold gaussianSpectralHeightReal
  exact
    add_nonneg
      (mul_nonneg (by norm_num only)
        (Finset.sum_nonneg (fun j _ ↦ div_nonneg (abs_nonneg _) (pow_nonneg h _))))
      (div_nonneg (by norm_num only) (pow_nonneg h _))

private theorem spectral_height_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    gaussianSpectralHeightReal y ≤ gaussianSpectralHeightReal x := by
  unfold gaussianSpectralHeightReal
  have hpow (j : ℕ) := pow_le_pow_left₀ hx.le hxy j
  have hsum :=
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) fun j _ ↦
      div_le_div_of_nonneg_left (abs_nonneg (spectralCoeff j : ℝ)) (pow_pos hx _) (hpow j.val)
  exact
    add_le_add (mul_le_mul_of_nonneg_left hsum (by norm_num only))
      (div_le_div_of_nonneg_left (by norm_num only) (pow_pos hx _) (hpow 4))

private theorem spectral_bracket_eq (i : Fin 29) :
    spectralBracket i = AnalyticNumberTheory.RiemannZeta.lowZero100Lower i := by
  fin_cases i <;> decide +kernel

/-- Certified low-zero ordinates and the height-100 tail give a common
absolute cost below 1/40 after the analytic pointwise estimates. -/
public theorem gaussian_spectral_majorant_lt {g : Fin 29 → ℝ}
    (hg : ∀ i, g i ∈ gaussianLowOrdinateBox i) :
    (∑ i : Fin 29, 2 * gaussianSpectralHeightReal (g i) / (g i) ^ 2) +
        gaussianSpectralHeightReal 100 * (7872913 / 588750000) <
      1 / 40 := by
  have hpos (i : Fin 29) : 0 < spectralBracket i := by fin_cases i <;> decide +kernel
  have hrow (i : Fin 29) :
    2 * gaussianSpectralHeightReal (g i) / (g i) ^ 2 ≤
      2 * gaussianSpectralHeightReal (spectralBracket i) / (spectralBracket i : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) < (spectralBracket i : ℝ) := Rat.cast_pos.mpr (hpos i)
    have h1 : (spectralBracket i : ℝ) ≤ g i := by
      rw [spectral_bracket_eq]
      exact (hg i).1
    exact
      (div_le_div_of_nonneg_left
            (mul_nonneg (by norm_num only) (spectral_height_nonneg _ (h0.le.trans h1)))
            (pow_pos h0 _) (pow_le_pow_left₀ h0.le h1 2)).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (spectral_height_antitone h0 h1) (by norm_num only))
          (pow_nonneg h0.le _))
  have h := (Rat.cast_lt (K := ℝ)).mpr gaussian_spectral_budget_lt
  simp only [gaussianSpectralBudget, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_pow, spectral_height_cast] at h
  exact (add_le_add (Finset.sum_le_sum (fun i _ ↦ hrow i)) (le_refl _)).trans_lt h

/-- The actual inverse-square ordinate tail under RH fits the shared
spectral budget together with the 29 certified low-ordinate majorants. -/
public theorem gaussian_spectral_ordinate_budget (hRH : RiemannHypothesis) {g : Fin 29 → ℝ}
    (hg : ∀ i, g i ∈ gaussianLowOrdinateBox i) :
    (∑ i : Fin 29, 2 * gaussianSpectralHeightReal (g i) / (g i) ^ 2) +
        gaussianSpectralHeightReal 100 * AnalyticNumberTheory.RiemannZeta.ordinateTail 100 <
      1 / 40 := by
  have ht :=
    (AnalyticNumberTheory.RiemannZeta.ordinateTail_hundred_le hRH).trans
      (by norm_num only : (13 / 1000 : ℝ) ≤ 7872913 / 588750000)
  have hm := mul_le_mul_of_nonneg_left ht (spectral_height_nonneg 100 (by norm_num only))
  exact (add_le_add (le_refl _) hm).trans_lt (gaussian_spectral_majorant_lt hg)

private noncomputable def spectralZeroWeight (ρ : ℂ) : ℝ :=
  (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
    (gaussianSpectralHeightReal |ρ.im| / |ρ.im| ^ 2)

private theorem spectral_weight_nonneg (ρ : ℂ) : 0 ≤ spectralZeroWeight ρ := by
  exact
    mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (spectral_height_nonneg _ (abs_nonneg _)) (sq_nonneg _))

private theorem spectral_head_le (hRH : RiemannHypothesis) {g : Fin 29 → ℝ} (hm : StrictMono g)
    (hp : ∀ i, 0 < g i) (hu : ∀ i, g i ≤ 100)
    (hz : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) :
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100, spectralZeroWeight ρ) ≤
      ∑ i : Fin 29, 2 * gaussianSpectralHeightReal (g i) / (g i) ^ 2 := by
  have hcomplete :=
    AnalyticNumberTheory.RiemannZeta.critical_zeros_complete_simple hRH
      (AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH).le g hm hp hu hz
  let Z := fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hconj (ρ : ℂ) (hρ : ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100) :
    spectralZeroWeight ((starRingEnd ℂ) ρ) = spectralZeroWeight ρ := by
    have hzero :=
      (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hρ
    have hr :=
      AnalyticNumberTheory.RiemannZeta.zeta_zero_re_eq_half_of_riemannHypothesis hRH hzero.1
        hzero.2.1
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_re] at hr
      norm_num only at hr
    simp only [spectralZeroWeight, AnalyticNumberTheory.RiemannZeta.multiplicity_conj hne,
      Complex.conj_im, abs_neg]
  rw [AnalyticNumberTheory.RiemannZeta.zero_sum_eq_two_positive hRH
      (by norm_num only : (0 : ℝ) ≤ 100) spectralZeroWeight hconj]
  simp only [mul_div_assoc, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num only)
  refine
    (Finset.sum_le_sum_of_subset_of_nonneg hcomplete.1 (fun ρ _ _ ↦ spectral_weight_nonneg ρ)).trans
      ?_
  rw [Finset.sum_image
      (fun i _ j _ hij ↦
        AnalyticNumberTheory.RiemannZeta.critical_points_injective g hm.injective hij)]
  apply Finset.sum_le_sum
  intro i _
  have he : (Z i).im = g i := by
    simp only [Z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  change spectralZeroWeight (Z i) ≤ _
  simp only [spectralZeroWeight, he, abs_of_pos (hp i),
    show AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (Z i) = 1 from hcomplete.2 i,
    Nat.cast_one, one_mul, le_refl]

private theorem spectral_tail_sum_le (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hr : ∀ ρ ∈ S, 0 ≤ ρ.re) (hh : ∀ ρ ∈ S, 100 < |ρ.im|) :
    (∑ ρ ∈ S, spectralZeroWeight ρ) ≤
      gaussianSpectralHeightReal 100 * AnalyticNumberTheory.RiemannZeta.ordinateTail 100 := by
  have h100 : (0 : ℝ) < 100 := by norm_num only
  have htail := AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH S 100 hz hr hh
  refine le_trans ?_ (mul_le_mul_of_nonneg_left htail (spectral_height_nonneg 100 h100.le))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  have h := spectral_height_antitone h100 (hh ρ hρ).le
  have hdiv := div_le_div_of_nonneg_right h (sq_nonneg |ρ.im|)
  unfold spectralZeroWeight
  exact (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)).trans_eq (by ring)

/-- Under RH, any finite sum of nontrivial zero contributions meeting the
pointwise height majorant has absolute value below 1/40. -/
public theorem gaussian_spectral_finite_lt (hRH : RiemannHypothesis) (S : Finset ℂ) (f : ℂ → ℝ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hr : ∀ ρ ∈ S, 0 ≤ ρ.re)
    (hf :
      ∀ ρ ∈ S,
        |f ρ| ≤
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            (gaussianSpectralHeightReal |ρ.im| / |ρ.im| ^ 2)) :
    |∑ ρ ∈ S, f ρ| < 1 / 40 := by
  classical
  obtain ⟨g, hm, hp, hu, hg, hlo, hhi⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  let p := fun ρ : ℂ ↦ |ρ.im| ≤ (100 : ℝ)
  have hsub : S.filter p ⊆ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100 := by
    intro ρ hρ
    obtain ⟨hρS, hρp⟩ := Finset.mem_filter.mp hρ
    exact
      (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mpr
        ⟨hz ρ hρS, hr ρ hρS, hρp⟩
  have hhead :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ ↦ spectral_weight_nonneg ρ)).trans
      (spectral_head_le hRH hm hp hu hg)
  have htail :=
    spectral_tail_sum_le hRH (S.filter fun ρ ↦ ¬p ρ) (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ hr ρ (Finset.mem_filter.mp hρ).1)
      (fun _ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2)
  refine ((Finset.abs_sum_le_sum_abs f S).trans (Finset.sum_le_sum hf)).trans_lt ?_
  change (∑ ρ ∈ S, spectralZeroWeight ρ) < 1 / 40
  rw [← Finset.sum_filter_add_sum_filter_not S p spectralZeroWeight]
  exact
    (add_le_add hhead htail).trans_lt
      (gaussian_spectral_ordinate_budget hRH (fun i ↦ ⟨hlo i, hhi i⟩))

/-- Passing to the limit of finite explicit-formula sums preserves the
closed spectral allowance. -/
public theorem gaussian_spectral_limit_le {Z : ℝ} (hRH : RiemannHypothesis) (S : ℕ → Finset ℂ)
    (f : ℂ → ℝ) (hz : ∀ m ρ, ρ ∈ S m → riemannZeta ρ = 0) (hr : ∀ m ρ, ρ ∈ S m → 0 ≤ ρ.re)
    (hf :
      ∀ m ρ,
        ρ ∈ S m →
          |f ρ| ≤
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
              (gaussianSpectralHeightReal |ρ.im| / |ρ.im| ^ 2))
    (hlim : Filter.Tendsto (fun m ↦ ∑ ρ ∈ S m, f ρ) Filter.atTop (nhds Z)) : |Z| ≤ 1 / 40 := by
  apply le_of_tendsto hlim.abs
  exact
    Filter.Eventually.of_forall fun m ↦
      (gaussian_spectral_finite_lt hRH (S m) f (hz m) (hr m) (hf m)).le

/-- The common principal spectral coefficient before its radius-dependent
phase and the physical endpoint correction. -/
public noncomputable def gaussianSpectralCoeff (γ : ℝ) : ℂ :=
  let a : ℝ := 11 / 10
  let b : ℝ := 21 / 8
  let C := a ^ 5 * Real.exp (-(a * b)) / 120
  let ρ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I
  let s := (a : ℂ) + (γ : ℂ) * Complex.I
  ((4 * C : ℝ) : ℂ) * (∑ j : Fin 6, (spectralCoeff j : ℂ) / s ^ (j.val + 1)) / ρ +
    ((a ^ 5 : ℝ) : ℂ) * Complex.exp (((b * γ : ℝ) : ℂ) * Complex.I) / s ^ 6

private theorem spectral_norm_height {v γ : ℝ} : |γ| ≤ ‖(v : ℂ) + (γ : ℂ) * Complex.I‖ := by
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero] using
    Complex.abs_im_le_norm ((v : ℂ) + (γ : ℂ) * Complex.I)

private theorem spectral_exp_norm (v : ℝ) : ‖Complex.exp ((v : ℂ) * Complex.I)‖ = 1 := by
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]

/-- For nonzero ordinate, the complex principal coefficient is bounded by
the certified height majorant divided by the squared ordinate. -/
public theorem gaussian_spectral_coeff_norm {γ : ℝ} (hγ : γ ≠ 0) :
    ‖gaussianSpectralCoeff γ‖ ≤ gaussianSpectralHeightReal |γ| / |γ| ^ 2 := by
  let t := |γ|
  let a : ℝ := 11 / 10
  let b : ℝ := 21 / 8
  let C := a ^ 5 * Real.exp (-(a * b)) / 120
  let ρ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I
  let s := (a : ℂ) + (γ : ℂ) * Complex.I
  let U := ∑ j : Fin 6, |(spectralCoeff j : ℝ)| / t ^ (j.val + 1)
  have ht : 0 < t := abs_pos.mpr hγ
  have hρ : t ≤ ‖ρ‖ := spectral_norm_height
  have hs : t ≤ ‖s‖ := spectral_norm_height
  have hC : 0 ≤ C :=
    div_nonneg (mul_nonneg (by norm_num only [a]) (Real.exp_pos _).le) (by norm_num only)
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ ↦ div_nonneg (abs_nonneg _) (pow_nonneg ht.le _)
  have hsum : ‖∑ j : Fin 6, (spectralCoeff j : ℂ) / s ^ (j.val + 1)‖ ≤ U := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_div, norm_pow, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos ht _) (pow_le_pow_left₀ ht.le hs _)
  have hleft :
    ‖((4 * C : ℝ) : ℂ) * (∑ j : Fin 6, (spectralCoeff j : ℂ) / s ^ (j.val + 1)) / ρ‖ ≤
      4 * C * U / t := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num only) hC)]
    exact
      (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num only) hC))
            (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num only) hC) hU) ht hρ)
  have hright :
    ‖((a ^ 5 : ℝ) : ℂ) * Complex.exp (((b * γ : ℝ) : ℂ) * Complex.I) / s ^ 6‖ ≤ a ^ 5 / t ^ 6 := by
    rw [norm_div, norm_mul, spectral_exp_norm, mul_one, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by norm_num only [a])]
    exact
      div_le_div_of_nonneg_left (by norm_num only [a]) (pow_pos ht _) (pow_le_pow_left₀ ht.le hs _)
  refine (norm_add_le _ _).trans ((add_le_add hleft hright).trans ?_)
  have hT : 4 * C * U / t = (4 * C * ∑ j : Fin 6, |(spectralCoeff j : ℝ)| / t ^ j.val) / t ^ 2 := by
    unfold U
    simp only [Finset.mul_sum, Finset.sum_div, pow_add, pow_one]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [ht.ne']
  rw [hT]
  have hCa : C ≤ (747750760233171678801217976482971 / 1000000000000000000000000000000000000 : ℝ) :=
    gaussian_spectral_prefactor_le
  have hU' : 0 ≤ ∑ j : Fin 6, |(spectralCoeff j : ℝ)| / t ^ j.val :=
    Finset.sum_nonneg fun _ _ ↦ div_nonneg (abs_nonneg _) (pow_nonneg ht.le _)
  have he : a ^ 5 / t ^ 6 = (161051 / 100000 : ℝ) / t ^ 4 / t ^ 2 := by
    have ha : a ^ 5 = (161051 / 100000 : ℝ) := by norm_num only [a]
    simp only [ha, div_div, mul_assoc, ← pow_add, Nat.reduceAdd]
  rw [he]
  change _ ≤ gaussianSpectralHeightReal t / t ^ 2
  rw [gaussianSpectralHeightReal, add_div]
  exact
    add_le_add
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCa (by norm_num only)) hU')
        (sq_nonneg t))
      (le_refl _)

private def kernelMomentCoeff : Fin 6 → ℚ :=
  ![(21 / 8) ^ 5, 5 * (21 / 8) ^ 4, 20 * (21 / 8) ^ 3, 60 * (21 / 8) ^ 2, 120 * (21 / 8), 120]

private theorem spectral_cancellation {z : ℂ} (hs : z + 11 / 10 ≠ 0) (hρ : z + 1 / 2 ≠ 0) :
    (21 / 8 : ℂ) ^ 5 / (z + 1 / 2) -
        (∑ j : Fin 6, (kernelMomentCoeff j : ℂ) / (z + 11 / 10) ^ (j.val + 1)) =
      (∑ j : Fin 6, (spectralCoeff j : ℂ) / (z + 11 / 10) ^ (j.val + 1)) / (z + 1 / 2) := by
  generalize hs' : z + 11 / 10 = s at hs ⊢
  generalize hρ' : z + 1 / 2 = ρ at hρ ⊢
  have he : ρ = s - 3 / 5 := by
    rw [← hρ', ← hs']; ring
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, kernelMomentCoeff, spectralCoeff,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, add_zero]
  field_simp [hs, hρ]
  rw [he]
  ring

/-- The lower-window moment of the shared six-pole kernel, evaluated by
the exponential-polynomial antiderivative at the cutoff. -/
public noncomputable def gaussianSpectralMoment (γ : ℝ) : ℂ :=
  let C : ℝ := (11 / 10 : ℝ) ^ 5 * Real.exp (-((11 / 10 : ℝ) * (21 / 8))) / 120
  let s := ((11 / 10 : ℝ) : ℂ) + (γ : ℂ) * Complex.I
  (C : ℂ) * ∑ j : Fin 6, (kernelMomentCoeff j : ℂ) / s ^ (j.val + 1)

/-- The cutoff term minus four times the lower-window moment cancels
to the rational part of the certified spectral coefficient. -/
public theorem gaussian_spectral_coeff_eq {γ : ℝ} (hγ : γ ≠ 0) :
    let a : ℝ := 11 / 10
    let b : ℝ := 21 / 8
    let C := a ^ 5 * Real.exp (-(a * b)) / 120
    let ρ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I
    let s := (a : ℂ) + (γ : ℂ) * Complex.I
    gaussianSpectralCoeff γ =
      4 * ((C * b ^ 5 : ℝ) : ℂ) / ρ - 4 * gaussianSpectralMoment γ +
        ((a ^ 5 : ℝ) : ℂ) * Complex.exp (((b * γ : ℝ) : ℂ) * Complex.I) / s ^ 6 := by
  intro a b C ρ s
  have ht : 0 < |γ| := abs_pos.mpr hγ
  have hs : s ≠ 0 := norm_pos_iff.mp (ht.trans_le spectral_norm_height)
  have hρ : ρ ≠ 0 := norm_pos_iff.mp (ht.trans_le spectral_norm_height)
  have hs' : (γ : ℂ) * Complex.I + 11 / 10 ≠ 0 := by
    simpa only [s, a, Complex.ofReal_div, Complex.ofReal_ofNat, add_comm] using hs
  have hρ' : (γ : ℂ) * Complex.I + 1 / 2 ≠ 0 := by
    simpa only [ρ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, add_comm] using hρ
  have h := spectral_cancellation hs' hρ'
  have he :
    ((b : ℂ) ^ 5) / ρ - (∑ j : Fin 6, (kernelMomentCoeff j : ℂ) / s ^ (j.val + 1)) =
      (∑ j : Fin 6, (spectralCoeff j : ℂ) / s ^ (j.val + 1)) / ρ := by
    simpa only [s, ρ, a, b, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one,
      add_comm] using h
  unfold gaussianSpectralCoeff gaussianSpectralMoment
  change ((4 * C : ℝ) : ℂ) * _ / ρ + _ = _
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← he]
  ring

/-- Radius phase and multiplicity applied to the common principal coefficient. -/
public noncomputable def gaussianSpectralContribution (y : ℝ) (ρ : ℂ) : ℝ :=
  (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
    (Complex.exp (((ρ.im * Real.log (y ^ 2) : ℝ) : ℂ) * Complex.I) * gaussianSpectralCoeff ρ.im).re

private theorem gaussian_spectral_contribution_le (hRH : RiemannHypothesis) {y : ℝ} {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hr : 0 ≤ ρ.re) :
    |gaussianSpectralContribution y ρ| ≤ spectralZeroWeight ρ := by
  have him := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH hz hr
  have hpos : 0 < |ρ.im| := (mul_pos (by norm_num only) Real.pi_pos).trans him
  have hγ : ρ.im ≠ 0 := (abs_pos.mp hpos)
  unfold gaussianSpectralContribution spectralZeroWeight
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, spectral_exp_norm, one_mul]
  exact gaussian_spectral_coeff_norm hγ

/-- The limit of the common phased coefficient sums has cost at most 1/40
under RH. This bound is uniform in the physical radius. -/
public theorem gaussian_spectral_contribution_limit_le {y Z : ℝ} (hRH : RiemannHypothesis)
    (S : ℕ → Finset ℂ) (hz : ∀ m ρ, ρ ∈ S m → riemannZeta ρ = 0) (hr : ∀ m ρ, ρ ∈ S m → 0 ≤ ρ.re)
    (hlim :
      Filter.Tendsto (fun m ↦ ∑ ρ ∈ S m, gaussianSpectralContribution y ρ) Filter.atTop (nhds Z)) :
    |Z| ≤ 1 / 40 := by
  exact
    gaussian_spectral_limit_le hRH S _ hz hr
      (fun m ρ hρ ↦ gaussian_spectral_contribution_le hRH (hz m ρ hρ) (hr m ρ hρ)) hlim

end PseudoPrime.PrimeTestBounds.MillerRabin
