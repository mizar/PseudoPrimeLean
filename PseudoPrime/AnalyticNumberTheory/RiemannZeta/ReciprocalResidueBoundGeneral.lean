/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalTrivialZeroSeries
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ContourKernelConjugation

/-! General RH bounds for smoothed zeta zero sums and contour integrals. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

open PseudoPrime.AnalyticNumberTheory.RiemannXi in
/-- Under RH and for `x > 1`, any finite zeta-zero contribution sum for the
reciprocal kernel has real part at least minus the reciprocal trivial-zero
series minus `2 * riemannZeroMass / √x`. -/
theorem re_sum_riemannZetaReciprocalZeroContribution_ge_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0) :
    -riemannReciprocalTrivialZeroSeries x - 2 * riemannZeroMass / Real.sqrt x ≤
      (∑ ρ ∈ S, riemannZetaReciprocalZeroContribution x ρ).re := by
  classical
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  set St := S.filter (fun ρ => ρ.re < 0) with hSt_def
  set Sn := S.filter (fun ρ => ¬ρ.re < 0) with hSn_def
  have hsplit : St ∪ Sn = S := Finset.filter_union_filter_not_eq _ S
  have hdisj : Disjoint St Sn := Finset.disjoint_filter_filter_not S S _
  have hsum_split :
    (∑ ρ ∈ S, riemannZetaReciprocalZeroContribution x ρ) =
      (∑ ρ ∈ St, riemannZetaReciprocalZeroContribution x ρ) +
        ∑ ρ ∈ Sn, riemannZetaReciprocalZeroContribution x ρ := by
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
    -riemannReciprocalTrivialZeroSeries x ≤
      (∑ ρ ∈ St, riemannZetaReciprocalZeroContribution x ρ).re := by
    rw [Complex.re_sum]
    have heq :
      ∀ ρ ∈ St,
        (riemannZetaReciprocalZeroContribution x ρ).re =
          -(x⁻¹ ^ (2 * (trivialZeroIndex ρ + 1) + 1) /
              ((2 * (trivialZeroIndex ρ + 1) : ℝ) * (2 * (trivialZeroIndex ρ + 1) + 1))) := by
      intro ρ hρ
      have hspec := trivialZeroIndex_spec (hStriv ρ hρ)
      conv_lhs => rw [hspec]
      rw [riemannZetaReciprocalZeroContribution_neg_two_mul_nat_add_one hxpos, Complex.neg_re,
        Complex.ofReal_re]
    rw [Finset.sum_congr rfl heq, Finset.sum_neg_distrib]
    linarith only [sum_reciprocalTrivialZeroTerm_le hx St hStriv]
  have hnontriv :
    -(2 * riemannZeroMass / Real.sqrt x) ≤
      (∑ ρ ∈ Sn, riemannZetaReciprocalZeroContribution x ρ).re := by
    exact
      neg_le_of_abs_le
        ((Complex.abs_re_le_norm _).trans
          (norm_sum_riemannZetaReciprocalZeroContribution_le hRH hxpos Sn (fun ρ hρ ↦ (hSnz ρ hρ).1)
            (fun ρ hρ ↦ (hSnz ρ hρ).2)))
  linarith only [htriv, hnontriv]

/-- Under RH, combine the closed-form residues at zero and one with the finite
zero-contribution bound to obtain the reciprocal residue-ledger lower bound. -/
theorem re_riemannZetaReciprocalContourResidueLedger_unifiedTau_ge_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x τ : ℝ} (hx : 1 < x) (hτ : 1 < τ) (m : ℕ) :
    Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
        riemannReciprocalTrivialZeroSeries x -
        2 * RiemannXi.riemannZeroMass / Real.sqrt x ≤
      (riemannZetaReciprocalContourResidueLedger x (unifiedRectangleLower m)
          (unifiedTauRectangleUpper τ m)).re := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  rw [riemannZetaReciprocalContourResidueLedger_unifiedTau_eq hτ, Complex.add_re, Complex.add_re,
    riemannZetaReciprocalResidueAtZero_eq, riemannZetaReciprocalResidueAtOne_eq hxpos]
  have hre0 : (Complex.log (2 * (Real.pi : ℂ)) * (x : ℂ)⁻¹).re = Real.log (2 * Real.pi) / x := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) from by
        push_cast
        ring,
      ← Complex.ofReal_log (by positivity),
      show (x : ℂ)⁻¹ = ((x⁻¹ : ℝ) : ℂ) from by rw [Complex.ofReal_inv], ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  have hre1 :
    (Complex.log (x : ℂ) - 1 - (Real.eulerMascheroniConstant : ℂ)).re =
      Real.log x - 1 - Real.eulerMascheroniConstant := by
    rw [← Complex.ofReal_log hxpos.le]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  rw [hre0, hre1]
  unfold riemannZetaReciprocalContourZeroLedger
  have hzero_ledger :=
    re_sum_riemannZetaReciprocalZeroContribution_ge_of_riemannHypothesis hRH hx
      (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m))
      (fun ρ hρ => (mem_riemannZetaZerosInAnyRectangle_iff.mp hρ).2)
  linarith only [hzero_ledger]

/-- **The `τ = 2` case of the vertical-integral lower bound, under RH.** Combines the finite
ledger bound with `RiemannZeta.tendsto_riemannZetaReciprocalContourResidueLedger_atTop` via
`le_of_tendsto`,
after cancelling the leading `I` factor. -/
theorem re_integral_riemannZetaReciprocalContourKernel_two_ge_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
        riemannReciprocalTrivialZeroSeries x -
        2 * RiemannXi.riemannZeroMass / Real.sqrt x ≤
      ((2 * Real.pi : ℝ)⁻¹ •
          ∫ y : ℝ, riemannZetaReciprocalContourKernel x ((2 : ℂ) + (y : ℂ) * Complex.I)).re := by
  apply General.re_inv_two_pi_smul_ge_of_tendsto_residueLedger
  · simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul] using
      tendsto_riemannZetaReciprocalContourResidueLedger_atTop hx (by norm_num only) le_rfl
  · intro m
    exact
      re_riemannZetaReciprocalContourResidueLedger_unifiedTau_ge_of_riemannHypothesis hRH hx
        (by norm_num only) m

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
