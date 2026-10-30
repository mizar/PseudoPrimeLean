/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.IndexSixBarrier.IndexSixFourier

/-! # Fourier method obstruction for every penalty at least one fifth

Increasing the positive Fourier-side penalty decreases the EP1 numerator.
The existing dual certificate therefore bounds the whole parameter family,
including the penalties one third and one quarter for indices four and five.
This is a method obstruction, not a counterexample to a prime bound under GRH.
-/

@[expose] public section

namespace PseudoPrime.LLS.IndexSixBarrier

/-- The EP1 integrand with positive-part penalty `A` and negative-part penalty one.
For a complex test function `F`, the negative half-line has the original exponential weight.
The parameter is unrestricted here; monotonicity supplies the later comparison. -/
noncomputable def penaltyIntegrand (A : ℝ) (F : ℝ → ℂ) (t : ℝ) : ℝ :=
  if t ≤ 0 then (FourierTransform.fourier F t).re * Real.exp (Real.pi * t)
  else -(max (-(FourierTransform.fourier F t).re) 0 +
    A * max (FourierTransform.fourier F t).re 0) * Real.exp (Real.pi * t)

/-- The real-line integral of the EP1 integrand with penalty `A`.
Integrability is a hypothesis of comparison theorems, so the integral represents the
analytic numerator there. This extends the fixed index-six numerator. -/
noncomputable def penaltyNumerator (A : ℝ) (F : ℝ → ℂ) : ℝ :=
  MeasureTheory.integral MeasureTheory.volume (penaltyIntegrand A F)

/-- The squared L1-mass to normalized-numerator ratio for penalty `A`.
A positive numerator is required in the barrier theorem. At penalty one fifth this
is the existing index-six EP1 coefficient. -/
noncomputable def penaltyCoefficient (A : ℝ) (F : ℝ → ℂ) : ℝ :=
  (l1Mass F / (2 * Real.pi * penaltyNumerator A F)) ^ 2

/-- For ordered real penalties, the EP1 integrand decreases pointwise.
The positive Fourier part and exponential weight are nonnegative; the other terms
are unchanged. This is the input to the integral and dual comparisons. -/
theorem penaltyIntegrand_antitone {A B : ℝ} (hAB : A ≤ B) (F : ℝ → ℂ) (t : ℝ) :
    penaltyIntegrand B F t ≤ penaltyIntegrand A F t := by
  by_cases ht : t ≤ 0
  · exact le_of_eq (by rw [penaltyIntegrand, penaltyIntegrand, ite_eq_left ht, ite_eq_left ht])
  · rw [penaltyIntegrand, penaltyIntegrand, ite_eq_right ht, ite_eq_right ht]
    exact mul_le_mul_of_nonneg_right
      (neg_le_neg (add_le_add_right
        (mul_le_mul_of_nonneg_right hAB (le_max_right _ _)) _))
      (Real.exp_pos _).le

/-- At penalty one fifth, the integrand is the existing index-six integrand.
The definitions agree, allowing the old dual certificate to be reused. -/
theorem penaltyIntegrand_fifth (F : ℝ → ℂ) :
    penaltyIntegrand (1 / 5) F = ep1Integrand F := by
  rfl

/-- At penalty one fifth, the numerator is the existing index-six numerator.
The integrands agree definitionally, preserving the canonical normalization. -/
theorem penaltyNumerator_fifth (F : ℝ → ℂ) :
    penaltyNumerator (1 / 5) F = ep1Numerator F := by
  rfl

/-- For ordered penalties with integrable integrands, the numerator decreases.
Integrate the pointwise comparison to obtain the full functional inequality. -/
theorem penaltyNumerator_antitone {A B : ℝ} (hAB : A ≤ B) (F : ℝ → ℂ)
    (hA : MeasureTheory.Integrable (penaltyIntegrand A F))
    (hB : MeasureTheory.Integrable (penaltyIntegrand B F)) :
    penaltyNumerator B F ≤ penaltyNumerator A F := by
  exact MeasureTheory.integral_mono hB hA (penaltyIntegrand_antitone hAB F)

/-- For a penalty at least one fifth, the numerator is at most the index-six numerator.
Both integrands must be integrable. This is the comparison `J_A(F) ≤ J_(1/5)(F)`. -/
theorem penaltyNumerator_le_ep1 {A : ℝ} (hA : 1 / 5 ≤ A) (F : ℝ → ℂ)
    (hJ : MeasureTheory.Integrable (penaltyIntegrand A F))
    (hE : MeasureTheory.Integrable (ep1Integrand F)) :
    penaltyNumerator A F ≤ ep1Numerator F := by
  exact penaltyNumerator_antitone hA F hE hJ

/-- For a penalty at least one fifth, the existing dual weight majorizes the integrand.
Combine penalty monotonicity with the index-six pointwise certificate. No Fourier
sign assumption is imposed on the complex test function. -/
theorem penaltyIntegrand_le_dual {A : ℝ} (hA : 1 / 5 ≤ A)
    (F : ℝ → ℂ) (t : ℝ) :
    penaltyIntegrand A F t ≤ dualWeight t * (FourierTransform.fourier F t).re := by
  exact (penaltyIntegrand_antitone hA F t).trans (ep1Integrand_le_dual_pairing F t)

/-- For an integrable test function and parameterized integrand, the normalized numerator
has the existing dual upper bound when the penalty is at least one fifth.
Only the parameterized integrand needs to be integrable for this bound. -/
theorem penaltyNumerator_bound {A : ℝ} (hA : 1 / 5 ≤ A) (F : ℝ → ℂ)
    (hF : MeasureTheory.Integrable F)
    (hJ : MeasureTheory.Integrable (penaltyIntegrand A F)) :
    2 * Real.pi * penaltyNumerator A F ≤ Real.sqrt (121 / 60 : ℝ) * l1Mass F := by
  have h := MeasureTheory.integral_mono hJ (integrable_dual_pairing F hF)
    (penaltyIntegrand_le_dual hA F)
  exact (mul_le_mul_of_nonneg_left h (mul_pos (by norm_num only) Real.pi_pos).le).trans
    (dual_pairing_le F hF)

/-- For a positive numerator and penalty at least one fifth, square the dual upper bound.
Positivity justifies squaring; the explicit square root then cancels. This supplies
the normalized coefficient obstruction. -/
theorem penaltyNumerator_sq_bound {A : ℝ} (hA : 1 / 5 ≤ A) (F : ℝ → ℂ)
    (hF : MeasureTheory.Integrable F)
    (hJ : MeasureTheory.Integrable (penaltyIntegrand A F))
    (hpos : 0 < penaltyNumerator A F) :
    (2 * Real.pi * penaltyNumerator A F) ^ 2 ≤ (121 / 60 : ℝ) * (l1Mass F) ^ 2 := by
  have hd := mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos) hpos
  have hb := penaltyNumerator_bound hA F hF hJ
  calc
    _ ≤ (Real.sqrt (121 / 60 : ℝ) * l1Mass F) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self hd.le hb
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 121 / 60)]

/-- For any penalty at least one fifth, an integrable test function and integrand with
positive numerator have coefficient at least `60/121`. Clear the positive squared
denominator in the dual bound. This obstructs the entire admissible function class. -/
theorem penaltyCoefficient_ge {A : ℝ} (hA : 1 / 5 ≤ A) (F : ℝ → ℂ)
    (hF : MeasureTheory.Integrable F)
    (hJ : MeasureTheory.Integrable (penaltyIntegrand A F))
    (hpos : 0 < penaltyNumerator A F) : (60 / 121 : ℝ) ≤ penaltyCoefficient A F := by
  have hd := mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos) hpos
  have hs := penaltyNumerator_sq_bound hA F hF hJ hpos
  unfold penaltyCoefficient
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  linarith only [hs]

/-- At penalty one fifth, the coefficient is the existing index-six coefficient.
The definitions agree, so the generalized obstruction retains the old contract. -/
theorem penaltyCoefficient_fifth (F : ℝ → ℂ) :
    penaltyCoefficient (1 / 5) F = ep1Coefficient F := by
  rfl

/-- Analytic conditions for the functional with penalty `A` to be admissible.
The function and its integrand are integrable and its numerator is positive.
These conditions ensure a genuine positive denominator in certificate obstructions. -/
def PenaltyAdmissible (A : ℝ) (F : ℝ → ℂ) : Prop :=
  MeasureTheory.Integrable F ∧ MeasureTheory.Integrable (penaltyIntegrand A F) ∧
    0 < penaltyNumerator A F

/-- For a penalty at least one fifth and an admissible test function, every rational
upper certificate lies strictly above the index-six paper target at epsilon `1/200`.
Combine the coefficient barrier with the existing strict target comparison. -/
theorem penalty_paper_lt_of_le_rat {A : ℝ} (hA : 1 / 5 ≤ A) (F : ℝ → ℂ)
    (hF : MeasureTheory.Integrable F)
    (hJ : MeasureTheory.Integrable (penaltyIntegrand A F))
    (hpos : 0 < penaltyNumerator A F) (r : ℚ)
    (hr : penaltyCoefficient A F ≤ (r : ℝ)) : paperCoefficient (1 / 200) < (r : ℝ) := by
  exact paperCoefficient_one_div_two_hundred_lt_barrier.trans_le
    ((penaltyCoefficient_ge hA F hF hJ hpos).trans hr)

/-- No admissible test function with penalty at least one fifth attains the index-six
paper target at epsilon `1/200`. The uniform coefficient lower bound contradicts
the target comparison; this says nothing against the number-theoretic statement. -/
theorem no_penalty_certificate {A : ℝ} (hA : 1 / 5 ≤ A) :
    ¬∃ F : ℝ → ℂ, PenaltyAdmissible A F ∧
      penaltyCoefficient A F ≤ paperCoefficient (1 / 200) := by
  rintro ⟨F, ⟨hF, hJ, hpos⟩, hc⟩
  exact (not_le_of_gt paperCoefficient_one_div_two_hundred_lt_barrier)
    ((penaltyCoefficient_ge hA F hF hJ hpos).trans hc)

/-- A fixed penalty at least one fifth cannot supply admissible EP1 certificates for
every positive epsilon in the index-six target. Specialize to epsilon `1/200` and
apply the certificate obstruction. -/
theorem no_penalty_for_all_epsilon {A : ℝ} (hA : 1 / 5 ≤ A) :
    ¬(∀ ε : ℝ, 0 < ε → ∃ F : ℝ → ℂ,
      PenaltyAdmissible A F ∧ penaltyCoefficient A F ≤ paperCoefficient ε) := by
  intro h
  exact no_penalty_certificate hA (h (1 / 200) (by norm_num only))

end PseudoPrime.LLS.IndexSixBarrier
