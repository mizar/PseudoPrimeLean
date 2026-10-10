/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ShiftedLogarithmicResidues
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mass bounds for shifted zero contributions

Critical-line zeros yield an inverse-square mass majorant. Summability controls the shifted
series and its integral over shifts greater than one, without a global residue formula.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For a complex point ρ with Re ρ = 1/2 and a real shift σ ≥ 1,
translation to ρ-σ does not decrease the squared norm. Expand real and imaginary
parts; the difference is σ(σ-1) ≥ 0. This compares shifted denominators with
the unshifted inverse-square mass without assuming ρ is a zero of a function. -/
theorem norm_sq_le_norm_sq_sub_real_of_half {ρ : ℂ} {σ : ℝ} (hρ : ρ.re = 1 / 2) (hσ : 1 ≤ σ) :
    ‖ρ‖ ^ 2 ≤ ‖ρ - (σ : ℂ)‖ ^ 2 := by
  rw [pow_two, Complex.norm_mul_self_eq_normSq, pow_two, Complex.norm_mul_self_eq_normSq,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero, hρ]
  have hm : 0 ≤ σ * (σ - 1) := mul_nonneg (zero_le_one.trans hσ) (sub_nonneg.mpr hσ)
  nlinarith only [hm]

/-- Any complex point with real part 1/2 is nonzero. Taking real parts of a hypothetical
zero gives a contradiction. This verifies that the critical-line mass denominators
are nonzero; no analytic function or zero-set hypothesis is required. -/
theorem zero_ne_of_re_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ρ ≠ 0 := by
  intro hz
  rw [hz, Complex.zero_re] at hρ
  norm_num only at hρ

/-- For a multiplicity m, a zero on the critical line, sigma>=1 and x>0, the shifted residue
norm is bounded by x ^ (1/2-sigma) times m/|rho|^2. Evaluate the complex power's norm and
compare the shifted denominator. This is the pointwise zero-error majorant. -/
theorem norm_shifted_zero_residue_le (m : ℕ) {ρ : ℂ} {σ x : ℝ} (hρ : ρ.re = 1 / 2) (hσ : 1 ≤ σ)
    (hx : 0 < x) :
    ‖-(m : ℂ) * (x : ℂ) ^ (ρ - (σ : ℂ)) / (ρ - (σ : ℂ)) ^ 2‖ ≤
      x ^ (1 / 2 - σ) * ((m : ℝ) / ‖ρ‖ ^ 2) := by
  have hpos : 0 < ‖ρ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (zero_ne_of_re_half hρ))
  have hbound :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg m) hpos (norm_sq_le_norm_sq_sub_real_of_half hρ hσ)
  calc
    ‖-(m : ℂ) * (x : ℂ) ^ (ρ - (σ : ℂ)) / (ρ - (σ : ℂ)) ^ 2‖ =
        x ^ (1 / 2 - σ) * ((m : ℝ) / ‖ρ - (σ : ℂ)‖ ^ 2) :=
      by
      rw [norm_div, norm_mul, norm_neg, Complex.norm_natCast, norm_pow,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.sub_re, Complex.ofReal_re, hρ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hx.le _)

/-- On the critical line, convergence of inverse-square multiplicity mass implies convergence
of the shifted residue series for sigma>=1 and x>0. Dominate norms by the mass majorant. -/
theorem summable_shifted_zero_residues {ι : Type*} (z : ι → ℂ) (m : ι → ℕ) {σ x : ℝ}
    (hz : ∀ i, (z i).re = 1 / 2) (hσ : 1 ≤ σ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖z i‖ ^ 2)) :
    Summable (fun i ↦ -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2) := by
  exact
    (hm.mul_left (x ^ (1 / 2 - σ))).of_norm_bounded
      (fun i ↦ norm_shifted_zero_residue_le (m i) (hz i) hσ hx)

/-- For any indexed family of critical-line points with natural multiplicities, assume
summability of m_i/norm(z_i)², real σ ≥ 1, and x > 0. The norm of the shifted residue
sum is at most `x^(1/2-σ)` times that mass. Sum the pointwise norm majorant using
absolute convergence. This bounds a whole shifted zero contribution independently
of the index type or a particular L-function. -/
theorem norm_tsum_shifted_zero_residues_le {ι : Type*} (z : ι → ℂ) (m : ι → ℕ) {σ x : ℝ}
    (hz : ∀ i, (z i).re = 1 / 2) (hσ : 1 ≤ σ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖z i‖ ^ 2)) :
    ‖∑' i, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2‖ ≤
      x ^ (1 / 2 - σ) * ∑' i, (m i : ℝ) / ‖z i‖ ^ 2 := by
  have hb := fun i ↦ norm_shifted_zero_residue_le (m i) (hz i) hσ hx
  have hmajor := hm.mul_left (x ^ (1 / 2 - σ))
  have hnorm : Summable (fun i ↦ ‖-(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2‖) :=
    Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _) hb hmajor
  calc
    _ ≤ ∑' i, ‖-(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, x ^ (1 / 2 - σ) * ((m i : ℝ) / ‖z i‖ ^ 2) := Summable.tsum_le_tsum hb hnorm hmajor
    _ = _ := tsum_mul_left

/-- For x>1, x ^ (-sigma) is integrable over sigma>1. Express the power as an exponential
with negative rate log x; this supplies the zero-error majorant's integrability. -/
theorem integrableOn_rpow_neg {x : ℝ} (hx : 1 < x) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ x ^ (-σ)) (Set.Ioi 1) := by
  have hf : (fun σ : ℝ ↦ x ^ (-σ)) = (fun σ ↦ Real.exp ((-Real.log x) * σ)) := by
    funext σ
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
    congr 1
    ring
  rw [hf]
  exact integrableOn_exp_mul_Ioi (neg_neg_of_pos (Real.log_pos hx)) 1

/-- For x>1, integration of x ^ (-sigma) over sigma>1 gives 1/(x log x).
Evaluate the decaying exponential integral to compute the zero-error coefficient. -/
theorem integral_rpow_neg {x : ℝ} (hx : 1 < x) :
    (∫ σ : ℝ in Set.Ioi 1, x ^ (-σ)) = x⁻¹ / Real.log x := by
  have hf : (fun σ : ℝ ↦ x ^ (-σ)) = (fun σ ↦ Real.exp ((-Real.log x) * σ)) := by
    funext σ
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
    congr 1
    ring
  rw [hf, integral_exp_mul_Ioi (neg_neg_of_pos (Real.log_pos hx)), mul_one, Real.exp_neg,
    Real.exp_log (zero_lt_one.trans hx)]
  ring

/-- For x>1 and any real mass M, x ^ (1/2-sigma)*M is integrable over sigma>1.
Factor out x ^ (1/2) and use exponential decay. -/
theorem integrableOn_shifted_zero_majorant {x : ℝ} (hx : 1 < x) (M : ℝ) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ x ^ (1 / 2 - σ) * M) (Set.Ioi 1) := by
  have hf : (fun σ : ℝ ↦ x ^ (1 / 2 - σ) * M) = (fun σ ↦ (x ^ (1 / 2 : ℝ) * x ^ (-σ)) * M) := by
    funext σ
    rw [sub_eq_add_neg, Real.rpow_add (zero_lt_one.trans hx)]
  rw [hf]
  exact ((integrableOn_rpow_neg hx).const_mul _).mul_const _

/-- For x>1 and real M, the integral of x ^ (1/2-sigma)*M over sigma>1 is
x ^ (-1/2)*M/log x. This yields the logarithmic explicit formula's zero-error scale. -/
theorem integral_shifted_zero_majorant {x : ℝ} (hx : 1 < x) (M : ℝ) :
    (∫ σ : ℝ in Set.Ioi 1, x ^ (1 / 2 - σ) * M) = x ^ (-(1 / 2 : ℝ)) / Real.log x * M := by
  have hf : (fun σ : ℝ ↦ x ^ (1 / 2 - σ) * M) = (fun σ ↦ (x ^ (1 / 2 : ℝ) * x ^ (-σ)) * M) := by
    funext σ
    rw [sub_eq_add_neg, Real.rpow_add (zero_lt_one.trans hx)]
  rw [hf, MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul, integral_rpow_neg hx]
  have hpow : x ^ (1 / 2 : ℝ) * x⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_add (zero_lt_one.trans hx)]
    norm_num only
  rw [← mul_div_assoc, hpow]

/-- For critical-line points, positive x, and summable inverse-square mass, the shifted residue
sum is measurable in sigma. Its fixed nonzero-multiplicity support is countable by mass
summability, so measurable summands suffice even for an arbitrary index type. -/
theorem measurable_shifted_zero_sum {ι : Type*} (z : ι → ℂ) (m : ι → ℕ) {x : ℝ}
    (hz : ∀ i, (z i).re = 1 / 2) (hx : 0 < x) (hm : Summable (fun i ↦ (m i : ℝ) / ‖z i‖ ^ 2)) :
    Measurable
      (fun σ : ℝ ↦ ∑' i, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2) := by
  let S : Set ι := {i | m i ≠ 0}
  have hS : S.Countable :=
    hm.countable_support.mono
      (by
        intro i hi
        exact
          div_ne_zero (Nat.cast_ne_zero.mpr hi)
            (pow_ne_zero 2 (norm_ne_zero_iff.mpr (zero_ne_of_re_half (hz i)))))
  let : Countable S := hS.to_subtype
  have heq :
    (fun σ : ℝ ↦ ∑' i, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2) =
      (fun σ : ℝ ↦ ∑' i : S, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2) := by
    funext σ
    symm
    apply
      tsum_subtype_eq_of_support_subset (s := S) (f := fun i : ι ↦
        -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2)
    intro i hi
    by_contra hnot
    have hm0 : m i = 0 := Classical.not_not.mp hnot
    exact hi (by simp only [hm0, Nat.cast_zero, neg_zero, zero_mul, zero_div])
  rw [heq]
  apply Measurable.tsum
  intro i
  have hpow : Continuous (fun σ : ℝ ↦ (x : ℂ) ^ (z i - (σ : ℂ))) :=
    (continuous_const.sub Complex.continuous_ofReal).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  exact
    (measurable_const.mul hpow.measurable).div
      ((measurable_const.sub Complex.measurable_ofReal).pow_const 2)

/-- For x>1 and critical-line zeros with summable inverse-square mass, the shifted residue
sum is integrable over sigma>1. Measurability and the integrable mass majorant prove this. -/
theorem integrableOn_shifted_zero_sum {ι : Type*} (z : ι → ℂ) (m : ι → ℕ) {x : ℝ}
    (hz : ∀ i, (z i).re = 1 / 2) (hx : 1 < x) (hm : Summable (fun i ↦ (m i : ℝ) / ‖z i‖ ^ 2)) :
    MeasureTheory.IntegrableOn
      (fun σ : ℝ ↦ ∑' i, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2)
      (Set.Ioi 1) := by
  apply
    (integrableOn_shifted_zero_majorant hx (∑' i, (m i : ℝ) / ‖z i‖ ^ 2)).mono'
      ((measurable_shifted_zero_sum z m hz (zero_lt_one.trans hx) hm).aestronglyMeasurable)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact norm_tsum_shifted_zero_residues_le z m hz (le_of_lt hσ) (zero_lt_one.trans hx) hm

/-- For x>1 and critical-line zeros with summable inverse-square mass, the integral of the
shifted residue sum has norm at most x ^ (-1/2)*mass/log x. Integrate the pointwise norm
majorant. Division by a further log x gives the zero-error scale in Lemma 2.5. -/
theorem norm_integral_shifted_zero_residues_le {ι : Type*} (z : ι → ℂ) (m : ι → ℕ) {x : ℝ}
    (hz : ∀ i, (z i).re = 1 / 2) (hx : 1 < x) (hm : Summable (fun i ↦ (m i : ℝ) / ‖z i‖ ^ 2)) :
    ‖∫ σ : ℝ in Set.Ioi 1, ∑' i, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2‖ ≤
      x ^ (-(1 / 2 : ℝ)) / Real.log x * ∑' i, (m i : ℝ) / ‖z i‖ ^ 2 := by
  have hbound :
    ∀ᵐ σ : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi 1),
      ‖∑' i, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2‖ ≤
        x ^ (1 / 2 - σ) * ∑' i, (m i : ℝ) / ‖z i‖ ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact norm_tsum_shifted_zero_residues_le z m hz (le_of_lt hσ) (zero_lt_one.trans hx) hm
  have hb :=
    MeasureTheory.norm_integral_le_of_norm_le
      (integrableOn_shifted_zero_majorant hx (∑' i, (m i : ℝ) / ‖z i‖ ^ 2)) hbound
  rwa [integral_shifted_zero_majorant hx] at hb

/-- For x>1 and a critical-line point, each shifted multiplicity residue is integrable over
sigma>1. Its measurable norm is bounded by the integrable inverse-square mass majorant. -/
theorem integrableOn_shifted_zero_residue (m : ℕ) {z : ℂ} {x : ℝ} (hz : z.re = 1 / 2) (hx : 1 < x) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ -(m : ℂ) * (x : ℂ) ^ (z - (σ : ℂ)) / (z - (σ : ℂ)) ^ 2)
      (Set.Ioi 1) := by
  have hpow : Continuous (fun σ : ℝ ↦ (x : ℂ) ^ (z - (σ : ℂ))) :=
    (continuous_const.sub Complex.continuous_ofReal).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'))
  have hmeas : Measurable (fun σ : ℝ ↦ -(m : ℂ) * (x : ℂ) ^ (z - (σ : ℂ)) / (z - (σ : ℂ)) ^ 2) :=
    (measurable_const.mul hpow.measurable).div
      ((measurable_const.sub Complex.measurable_ofReal).pow_const 2)
  apply (integrableOn_shifted_zero_majorant hx ((m : ℝ) / ‖z‖ ^ 2)).mono' hmeas.aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact norm_shifted_zero_residue_le m hz (le_of_lt hσ) (zero_lt_one.trans hx)

/-- For x>1 and a critical-line point, the L1 norm of a shifted residue is at most
x^(-1/2)*multiplicity/(|rho|^2 log x). This absolute-integral bound permits
sum-integral exchange. -/
theorem integral_norm_shifted_zero_residue_le (m : ℕ) {z : ℂ} {x : ℝ} (hz : z.re = 1 / 2)
    (hx : 1 < x) :
    (∫ σ : ℝ in Set.Ioi 1, ‖-(m : ℂ) * (x : ℂ) ^ (z - (σ : ℂ)) / (z - (σ : ℂ)) ^ 2‖) ≤
      x ^ (-(1 / 2 : ℝ)) / Real.log x * ((m : ℝ) / ‖z‖ ^ 2) := by
  have hb :
    ∀ᵐ σ : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi 1),
      ‖-(m : ℂ) * (x : ℂ) ^ (z - (σ : ℂ)) / (z - (σ : ℂ)) ^ 2‖ ≤
        x ^ (1 / 2 - σ) * ((m : ℝ) / ‖z‖ ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact norm_shifted_zero_residue_le m hz (le_of_lt hσ) (zero_lt_one.trans hx)
  have hi :=
    MeasureTheory.integral_mono_ae (integrableOn_shifted_zero_residue m hz hx).norm
      (integrableOn_shifted_zero_majorant hx ((m : ℝ) / ‖z‖ ^ 2)) hb
  rwa [integral_shifted_zero_majorant hx] at hi

/-- For x>1 and critical-line zeros with summable inverse-square mass, the residue sum may be
integrated termwise over sigma>1. Restrict to the countable nonzero-multiplicity support and
apply the absolute-integral summation theorem. This justifies the zero-side exchange. -/
theorem integral_tsum_shifted_zero_residues {ι : Type*} (z : ι → ℂ) (m : ι → ℕ) {x : ℝ}
    (hz : ∀ i, (z i).re = 1 / 2) (hx : 1 < x) (hm : Summable (fun i ↦ (m i : ℝ) / ‖z i‖ ^ 2)) :
    (∫ σ : ℝ in Set.Ioi 1, ∑' i, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2) =
      ∑' i, ∫ σ : ℝ in Set.Ioi 1, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2 := by
  have hi := fun i ↦ integrableOn_shifted_zero_residue (m i) (hz i) hx
  have hn :
    Summable
      (fun i ↦
        ∫ σ : ℝ in Set.Ioi 1, ‖-(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2‖) :=
    Summable.of_nonneg_of_le (fun i ↦ MeasureTheory.integral_nonneg (fun σ ↦ norm_nonneg _))
      (fun i ↦ integral_norm_shifted_zero_residue_le (m i) (hz i) hx)
      (hm.mul_left (x ^ (-(1 / 2 : ℝ)) / Real.log x))
  let S : Set ι := {i | m i ≠ 0}
  have hS : S.Countable :=
    hm.countable_support.mono
      (by
        intro i hi
        exact
          div_ne_zero (Nat.cast_ne_zero.mpr hi)
            (pow_ne_zero 2 (norm_ne_zero_iff.mpr (zero_ne_of_re_half (hz i)))))
  let : Countable S := hS.to_subtype
  have hs (σ : ℝ) :
    (∑' i : S, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2) =
      ∑' i, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2 := by
    apply
      tsum_subtype_eq_of_support_subset (s := S) (f := fun i : ι ↦
        -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2)
    intro i hsupport
    by_contra hnot
    have hm0 : m i = 0 := Classical.not_not.mp hnot
    exact hsupport (by simp only [hm0, Nat.cast_zero, neg_zero, zero_mul, zero_div])
  calc
    _ =
        ∫ σ : ℝ in Set.Ioi 1,
          ∑' i : S, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2 :=
      by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun σ ↦ (hs σ).symm)
    _ =
        ∑' i : S,
          ∫ σ : ℝ in Set.Ioi 1, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2 :=
      (MeasureTheory.hasSum_integral_of_summable_integral_norm (fun i : S ↦ hi i)
          (hn.subtype S)).tsum_eq.symm
    _ = _ := by
      apply
        tsum_subtype_eq_of_support_subset (s := S) (f := fun i : ι ↦
          ∫ σ : ℝ in Set.Ioi 1, -(m i : ℂ) * (x : ℂ) ^ (z i - (σ : ℂ)) / (z i - (σ : ℂ)) ^ 2)
      intro i hsupport
      by_contra hnot
      have hm0 : m i = 0 := Classical.not_not.mp hnot
      exact
        hsupport
          (by
            simp only [hm0, Nat.cast_zero, neg_zero, zero_mul, zero_div,
              MeasureTheory.integral_zero])

/-- For a complex point ρ with Re ρ = 1/2, the genus-one expression
`1/(1-ρ) + 1/ρ` equals the complex cast of `1/norm(ρ)²`.
Identify 1-ρ with the complex conjugate of ρ and combine the fractions.
This converts the Hadamard endpoint terms into inverse-square mass without
requiring a separate assumption that ρ is a function zero. -/
theorem genus_one_eq_inverseSquare_of_re_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / (1 - ρ) + 1 / ρ = ((1 : ℝ) / ‖ρ‖ ^ 2 : ℂ) := by
  have hz : ρ ≠ 0 := zero_ne_of_re_half hρ
  have hc : (1 : ℂ) - ρ = (starRingEnd ℂ) ρ := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith only [hρ]
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub]
  have hd : ρ * (1 - ρ) = (‖ρ‖ ^ 2 : ℝ) := by rw [hc, Complex.mul_conj', ← Complex.ofReal_pow]
  have hden : 1 - ρ ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith only [hr, hρ]
  calc
    _ = (ρ + (1 - ρ)) / ((1 - ρ) * ρ) := by
      rw [div_add_div _ _ hden hz]
      simp only [one_mul, mul_one]
    _ = 1 / (ρ * (1 - ρ)) := by rw [show ρ + (1 - ρ) = (1 : ℂ) by ring, mul_comm (1 - ρ) ρ]
    _ = _ := by rw [hd, Complex.ofReal_pow, Complex.ofReal_one]

/-- For a critical-line point and Re s > 1/2, the genus-one summand is bounded by an explicit
multiple of its inverse-square mass. The horizontal separation bounds the translated denominator. -/
theorem norm_genusTerm_le_inverseSquare {s ρ : ℂ} (hρ : ρ.re = 1 / 2) (hs : 1 / 2 < s.re) :
    ‖1 / (s - ρ) + 1 / ρ‖ ≤ ‖s‖ * (1 + ‖s‖ / (s.re - 1 / 2)) / ‖ρ‖ ^ 2 := by
  have hρ0 : ρ ≠ 0 := zero_ne_of_re_half hρ
  have hδ : 0 < s.re - 1 / 2 := sub_pos.mpr hs
  have hd : s.re - 1 / 2 ≤ ‖s - ρ‖ := by
    simpa only [Complex.sub_re, hρ] using Complex.re_le_norm (s - ρ)
  have hd0 : 0 < ‖s - ρ‖ := hδ.trans_le hd
  have hρnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hratio : ‖ρ‖ / ‖s - ρ‖ ≤ 1 + ‖s‖ / (s.re - 1 / 2) := by
    calc
      ‖ρ‖ / ‖s - ρ‖ ≤ (‖s - ρ‖ + ‖s‖) / ‖s - ρ‖ := by
        apply div_le_div_of_nonneg_right _ hd0.le
        have h := norm_sub_le s (s - ρ)
        rw [sub_sub_cancel] at h
        exact h.trans_eq (add_comm _ _)
      _ = 1 + ‖s‖ / ‖s - ρ‖ := by rw [add_div, div_self hd0.ne']
      _ ≤ _ := add_le_add (le_refl 1) (div_le_div_of_nonneg_left (norm_nonneg s) hδ hd)
  have hne : s - ρ ≠ 0 := norm_pos_iff.mp hd0
  have he : 1 / (s - ρ) + 1 / ρ = s / ((s - ρ) * ρ) := by
    field_simp [hne, hρ0]
    ring
  rw [he, norm_div, norm_mul]
  have hh := mul_le_mul_of_nonneg_left hratio (norm_nonneg s)
  calc
    ‖s‖ / (‖s - ρ‖ * ‖ρ‖) = (‖s‖ * (‖ρ‖ / ‖s - ρ‖)) / ‖ρ‖ ^ 2 := by field_simp [hd0.ne', hρnorm.ne']
    _ ≤ _ := div_le_div_of_nonneg_right hh (sq_nonneg _)

end PseudoPrime.AnalyticNumberTheory.General
