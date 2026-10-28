/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MethodBarrier.IndexSixDualIntegral

/-! # A uniform obstruction for the index-six Fourier certificate method

This file bounds every admissible test function for the index-six EP1
functional. The Fourier transform may be complex-valued: the functional
uses its real part, so the usual real-valued Fourier class is included.

The obstruction concerns the coefficient attainable through this Fourier
method. It is not a disproof of the number-theoretic statement of LLS
Theorem 1.3. In particular, the final quantified statements concern EP1
certificates, not primes or the truth of GRH.

All rational upper certificates, with arbitrary denominators, are covered.
Changing the search family or refining a rational approximation cannot
cross the proved lower bound for this functional.
-/

@[expose] public section

namespace PseudoPrime.LLS.IndexSixBarrier

open MeasureTheory in
/-- The L1 mass of a complex test function on the real line. -/
noncomputable def l1Mass (F : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖F x‖

open MeasureTheory in
/-- The index-six EP1 integrand, extended to arbitrary complex Fourier
transforms by using their real part. The positive-side penalty includes
both the negative part and one fifth of the positive part. -/
noncomputable def ep1Integrand (F : ℝ → ℂ) (t : ℝ) : ℝ :=
  if t ≤ 0 then (FourierTransform.fourier F t).re * Real.exp (Real.pi * t)
  else
    -(max (-(FourierTransform.fourier F t).re) 0 +
          (1 / 5 : ℝ) * max (FourierTransform.fourier F t).re 0) *
      Real.exp (Real.pi * t)

open MeasureTheory in
/-- The numerator of the index-six EP1 functional. Its integrability is
explicitly required by the admissibility predicate. -/
noncomputable def ep1Numerator (F : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, ep1Integrand F t

open MeasureTheory in
/-- The prime-bound coefficient associated with one EP1 test function.
The positive numerator condition is imposed separately. -/
noncomputable def ep1Coefficient (F : ℝ → ℂ) : ℝ :=
  (l1Mass F / (2 * Real.pi * ep1Numerator F)) ^ 2

open MeasureTheory in
/-- Hypotheses under which the EP1 numerator and the dual comparison are
genuine integrable quantities with positive denominator. -/
def EP1Admissible (F : ℝ → ℂ) : Prop :=
  Integrable F ∧ Integrable (ep1Integrand F) ∧ 0 < ep1Numerator F

open MeasureTheory in
/-- Pointwise majorization by the dual weight. On the truncated positive
interval the full EP1 penalty dominates one fifth of the Fourier real
part; beyond that interval the EP1 integrand is nonpositive. -/
theorem ep1Integrand_le_dual_pairing (F : ℝ → ℂ) (t : ℝ) :
    ep1Integrand F t ≤ dualWeight t * (FourierTransform.fourier F t).re := by
  have he : 0 ≤ Real.exp (Real.pi * t) := (Real.exp_pos _).le
  by_cases ht : t ≤ 0
  · rw [ep1Integrand, ite_eq_left ht, dualWeight_of_nonpos ht]
    exact le_of_eq (mul_comm _ _)
  · have htpos : 0 < t := lt_of_not_ge ht
    rw [ep1Integrand, ite_eq_right ht]
    have hn : 0 ≤ max (-(FourierTransform.fourier F t).re) 0 := le_max_right _ _
    have hp : 0 ≤ max (FourierTransform.fourier F t).re 0 := le_max_right _ _
    by_cases htc : t ≤ cutoff
    · rw [dualWeight_of_pos_le htpos htc]
      have hr :
        (1 / 5 : ℝ) * (FourierTransform.fourier F t).re ≤
          max (-(FourierTransform.fourier F t).re) 0 +
            (1 / 5 : ℝ) * max (FourierTransform.fourier F t).re 0 := by
        linarith only [hn, le_max_left (FourierTransform.fourier F t).re 0]
      calc
        _ ≤ -((1 / 5 : ℝ) * (FourierTransform.fourier F t).re) * Real.exp (Real.pi * t) :=
          mul_le_mul_of_nonneg_right (neg_le_neg hr) he
        _ = _ := by ring
    · rw [dualWeight_of_cutoff_lt (lt_of_not_ge htc), zero_mul]
      have hpenalty :
        0 ≤
          max (-(FourierTransform.fourier F t).re) 0 +
            (1 / 5 : ℝ) * max (FourierTransform.fourier F t).re 0 :=
        add_nonneg hn (mul_nonneg (by norm_num only) hp)
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpenalty) he

open MeasureTheory in
/-- Integrating the pointwise majorization is legitimate because both
the EP1 integrand and the dual pairing are integrable. -/
theorem ep1Numerator_le_dual_pairing (F : ℝ → ℂ) (hF : Integrable F)
    (hJ : Integrable (ep1Integrand F)) :
    ep1Numerator F ≤ ∫ t : ℝ, dualWeight t * (FourierTransform.fourier F t).re :=
  integral_mono hJ (integrable_dual_pairing F hF) (ep1Integrand_le_dual_pairing F)

open MeasureTheory in
/-- A uniform upper bound for the normalized EP1 numerator. The estimate
holds for the whole integrable class, without a Fourier sign hypothesis. -/
theorem ep1_numerator_bound (F : ℝ → ℂ) (hF : Integrable F) (hJ : Integrable (ep1Integrand F)) :
    2 * Real.pi * ep1Numerator F ≤ Real.sqrt (121 / 60 : ℝ) * l1Mass F := by
  have hp : 0 ≤ 2 * Real.pi := (mul_pos (by norm_num only) Real.pi_pos).le
  exact
    (mul_le_mul_of_nonneg_left (ep1Numerator_le_dual_pairing F hF hJ) hp).trans
      (dual_pairing_le F hF)

open MeasureTheory in
/-- Every admissible index-six EP1 test function has coefficient at least
`60/121`. This is a bound on the whole function class, not on a sampled or
finite-dimensional search family. -/
theorem ep1_coefficient_ge (F : ℝ → ℂ) (hF : Integrable F) (hJ : Integrable (ep1Integrand F))
    (hpos : 0 < ep1Numerator F) : (60 / 121 : ℝ) ≤ ep1Coefficient F := by
  have hd : 0 < 2 * Real.pi * ep1Numerator F :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) hpos
  have hb := ep1_numerator_bound F hF hJ
  have hs : (2 * Real.pi * ep1Numerator F) ^ 2 ≤ (121 / 60 : ℝ) * (l1Mass F) ^ 2 := by
    calc
      _ ≤ (Real.sqrt (121 / 60 : ℝ) * l1Mass F) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self hd.le hb
      _ = _ := by rw [mul_pow, Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 121 / 60)]
  unfold ep1Coefficient
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  linarith only [hs]

open MeasureTheory in
/-- Every certified rational upper bound for an EP1 coefficient is
strictly above the paper target at epsilon `1/200`. The denominator of
the rational certificate is completely unrestricted. -/
theorem paperCoefficient_lt_of_ep1Coefficient_le_rat (F : ℝ → ℂ) (hF : Integrable F)
    (hJ : Integrable (ep1Integrand F)) (hpos : 0 < ep1Numerator F) (r : ℚ)
    (hr : ep1Coefficient F ≤ (r : ℝ)) : paperCoefficient (1 / 200) < (r : ℝ) :=
  paperCoefficient_one_div_two_hundred_lt_barrier.trans_le
    ((ep1_coefficient_ge F hF hJ hpos).trans hr)

open MeasureTheory in
/-- No admissible EP1 function attains the paper's index-six target at
the fixed positive epsilon `1/200`. This does not assert that the prime
bound itself is false. -/
theorem no_ep1_certificate_at_paper_target :
    ¬∃ F : ℝ → ℂ, EP1Admissible F ∧ ep1Coefficient F ≤ paperCoefficient (1 / 200) := by
  rintro ⟨F, ⟨hF, hJ, hpos⟩, hc⟩
  exact
    (not_le_of_gt paperCoefficient_one_div_two_hundred_lt_barrier)
      ((ep1_coefficient_ge F hF hJ hpos).trans hc)

open MeasureTheory in
/-- In particular, no rational upper certificate for an admissible EP1
function can lie at or below the paper target. -/
theorem no_rational_ep1_certificate_at_paper_target :
    ¬∃ (F : ℝ → ℂ) (r : ℚ),
        EP1Admissible F ∧ ep1Coefficient F ≤ (r : ℝ) ∧ (r : ℝ) ≤ paperCoefficient (1 / 200) := by
  rintro ⟨F, r, ⟨hF, hJ, hpos⟩, hr, hc⟩
  exact (not_le_of_gt (paperCoefficient_lt_of_ep1Coefficient_le_rat F hF hJ hpos r hr)) hc

open MeasureTheory in
/-- The EP1 certificate method cannot supply the family of coefficients
required for every positive epsilon in the index-six paper statement.
A single explicit positive epsilon already contradicts the uniform
coefficient barrier. -/
theorem not_ep1_certificates_for_all_positive_epsilon :
    ¬(∀ ε : ℝ, 0 < ε → ∃ F : ℝ → ℂ, EP1Admissible F ∧ ep1Coefficient F ≤ paperCoefficient ε) := by
  intro h
  exact no_ep1_certificate_at_paper_target (h (1 / 200) (by norm_num only))

end PseudoPrime.LLS.IndexSixBarrier
