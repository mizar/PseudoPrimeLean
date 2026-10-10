/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroMultiplicity

/-!
# Finite zeta zero-contribution bounds under RH
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

open PseudoPrime.AnalyticNumberTheory.RiemannXi in
/-- Under RH, the inverse-norm-square multiplicity sum of a finite set of
nontrivial zeta zeros is at most twice the Riemann zero mass. The summable
xi-zero family supplies the bound used by both smoothed kernels. -/
theorem sum_riemannZetaZeroMultiplicity_invNormSq_le (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hSzero : ∀ ρ ∈ S, riemannZeta ρ = 0) (hSre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) ≤ 2 * riemannZeroMass := by
  have ht :=
    (summable_riemannXiZeroMultiplicityInvNormSq_of_riemannHypothesis hRH).sum_le_tsum S
      (fun ρ _ ↦ by
        split <;> [exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _); exact le_refl 0])
  rw [tsum_riemannXiZeroMultiplicity_invNormSq_eq_two_mul_riemannZeroMass_of_riemannHypothesis
      hRH] at ht
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun ρ hρ ↦ ?_))) ht
  have hz := riemannXi_eq_zero_of_riemannZeta_zero_re_nonneg (hSzero ρ hρ) (hSre ρ hρ)
  rw [ite_eq_left hz, riemannXiZeroMultiplicity_eq_riemannZetaZeroMultiplicity_of_zero hz]

/-- Under RH and x > 0, the logarithmic contributions of a finite set of zeta zeros
with nonnegative real part have a sum of norm at most `2 * riemannZeroMass * sqrt x`.
Use the triangle inequality, the critical-line norm identity, and the finite
inverse-square multiplicity bound. This controls both signs of the real error. -/
theorem norm_sum_riemannZetaLogZeroContribution_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (S : Finset ℂ) (hSzero : ∀ ρ ∈ S, riemannZeta ρ = 0) (hSre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    ‖∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ‖ ≤
      2 * RiemannXi.riemannZeroMass * Real.sqrt x := by
  have heq :
    (∑ ρ ∈ S, ‖riemannZetaLogZeroContribution x ρ‖) =
      Real.sqrt x * ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ := by
    rw [Finset.mul_sum]
    exact
      Finset.sum_congr rfl fun ρ hρ ↦ by
        rw [norm_riemannZetaLogZeroContribution_of_rh hRH hx (hSzero ρ hρ) (hSre ρ hρ),
          mul_div_assoc]
  have hb :=
    mul_le_mul_of_nonneg_left (sum_riemannZetaZeroMultiplicity_invNormSq_le hRH S hSzero hSre)
      (Real.sqrt_nonneg x)
  calc
    _ ≤ ∑ ρ ∈ S, ‖riemannZetaLogZeroContribution x ρ‖ := norm_sum_le _ _
    _ ≤ 2 * RiemannXi.riemannZeroMass * Real.sqrt x := by
      rw [heq]
      exact hb.trans_eq (mul_comm _ _)

/-- Under RH and x > 0, the reciprocal contributions of a finite set of zeta zeros
with nonnegative real part have a sum of norm at most `2 * riemannZeroMass / sqrt x`.
Apply the triangle inequality and the critical-line norm identity, then divide
the finite inverse-square multiplicity bound by sqrt x. This gives the complex
error estimate used in the reciprocal explicit formula. -/
theorem norm_sum_riemannZetaReciprocalZeroContribution_le (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) (S : Finset ℂ) (hSzero : ∀ ρ ∈ S, riemannZeta ρ = 0) (hSre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    ‖∑ ρ ∈ S, riemannZetaReciprocalZeroContribution x ρ‖ ≤
      2 * RiemannXi.riemannZeroMass / Real.sqrt x := by
  have heq :
    (∑ ρ ∈ S, ‖riemannZetaReciprocalZeroContribution x ρ‖) =
      (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) / Real.sqrt x := by
    rw [Finset.sum_div]
    exact
      Finset.sum_congr rfl fun ρ hρ ↦ by
        rw [norm_riemannZetaReciprocalZeroContribution_of_rh hRH hx (hSzero ρ hρ) (hSre ρ hρ)]
        ring
  calc
    _ ≤ ∑ ρ ∈ S, ‖riemannZetaReciprocalZeroContribution x ρ‖ := norm_sum_le _ _
    _ ≤ 2 * RiemannXi.riemannZeroMass / Real.sqrt x := by
      rw [heq]
      exact
        div_le_div_of_nonneg_right (sum_riemannZetaZeroMultiplicity_invNormSq_le hRH S hSzero hSre)
          (Real.sqrt_nonneg x)

open PseudoPrime.AnalyticNumberTheory.RiemannXi in
/-- Under RH and for `x > 0`, the logarithmic-kernel contributions from any
finite set of zeta zeros with nonnegative real part have real part at least
`-2 * riemannZeroMass * √x`, by the inverse-square zero-mass bound. -/
theorem re_sum_riemannZetaLogZeroContribution_nontrivial_ge_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) (S : Finset ℂ)
    (hSzero : ∀ ρ ∈ S, riemannZeta ρ = 0) (hSre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    -(2 * riemannZeroMass * Real.sqrt x) ≤ (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ).re := by
  exact
    neg_le_of_abs_le
      ((Complex.abs_re_le_norm _).trans
        (norm_sum_riemannZetaLogZeroContribution_le hRH hx S hSzero hSre))

/-- Under RH and for `x > 1`, a finite logarithmic-kernel zero sum has real
part at least minus the logarithmic trivial-zero series minus
`2 * riemannZeroMass * √x`. Split zeros into trivial and nontrivial parts. -/
theorem re_sum_riemannZetaLogZeroContribution_ge_of_riemannHypothesis (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 1 < x) (S : Finset ℂ) (hS : ∀ ρ ∈ S, riemannZeta ρ = 0) :
    -riemannZetaLogTrivialZeroSeries x - 2 * RiemannXi.riemannZeroMass * Real.sqrt x ≤
      (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ).re := by
  classical
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  set St := S.filter (fun ρ => ρ.re < 0) with hSt_def
  set Sn := S.filter (fun ρ => ¬ρ.re < 0) with hSn_def
  have hsplit : St ∪ Sn = S := Finset.filter_union_filter_not_eq _ S
  have hdisj : Disjoint St Sn := Finset.disjoint_filter_filter_not S S _
  have hsum_split :
    (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ) =
      (∑ ρ ∈ St, riemannZetaLogZeroContribution x ρ) +
        ∑ ρ ∈ Sn, riemannZetaLogZeroContribution x ρ := by
    rw [← hsplit, Finset.sum_union hdisj]
  rw [hsum_split, Complex.add_re]
  have hStz : ∀ ρ ∈ St, riemannZeta ρ = 0 ∧ ρ.re < 0 := by
    intro ρ hρ
    have hmem := Finset.mem_filter.mp hρ
    exact ⟨hS ρ hmem.1, hmem.2⟩
  have hSnz : ∀ ρ ∈ Sn, riemannZeta ρ = 0 ∧ 0 ≤ ρ.re := by
    intro ρ hρ
    have hmem := Finset.mem_filter.mp hρ
    exact ⟨hS ρ hmem.1, not_lt.mp hmem.2⟩
  have hStriv : ∀ ρ ∈ St, ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := fun ρ hρ =>
    exists_nat_eq_neg_two_mul_add_one_of_riemannZeta_zero_re_neg (hStz ρ hρ).2 (hStz ρ hρ).1
  have htriv :
    -riemannZetaLogTrivialZeroSeries x ≤ (∑ ρ ∈ St, riemannZetaLogZeroContribution x ρ).re := by
    rw [Complex.re_sum]
    have heq :
      ∀ ρ ∈ St,
        (riemannZetaLogZeroContribution x ρ).re =
          -(x⁻¹ ^ (2 * (trivialZeroIndex ρ + 1)) / (4 * ((trivialZeroIndex ρ : ℝ) + 1) ^ 2)) := by
      intro ρ hρ
      have hspec := trivialZeroIndex_spec (hStriv ρ hρ)
      conv_lhs => rw [hspec]
      rw [riemannZetaLogZeroContribution_neg_two_mul_nat_add_one hxpos, Complex.neg_re,
        Complex.ofReal_re]
    rw [Finset.sum_congr rfl heq, Finset.sum_neg_distrib]
    linarith only [sum_logTrivialZeroTerm_le hx St hStriv]
  have hnontriv :=
    re_sum_riemannZetaLogZeroContribution_nontrivial_ge_of_riemannHypothesis hRH hxpos Sn
      (fun ρ hρ => (hSnz ρ hρ).1) (fun ρ hρ => (hSnz ρ hρ).2)
  linarith only [htriv, hnontriv]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
