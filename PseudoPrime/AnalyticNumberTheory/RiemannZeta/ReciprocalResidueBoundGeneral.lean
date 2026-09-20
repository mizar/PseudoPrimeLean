/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalTrivialZeroSeries
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ContourKernelConjugation

/-! General RH bounds for smoothed zeta zero sums and contour integrals. -/

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
  have hxpos : 0 < x := by linarith
  have hxsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
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
    linarith [sum_reciprocalTrivialZeroTerm_le hx St hStriv]
  have hnontriv :
    -(2 * riemannZeroMass / Real.sqrt x) ≤
      (∑ ρ ∈ Sn, riemannZetaReciprocalZeroContribution x ρ).re := by
    rw [Complex.re_sum]
    have hbound :
      ∀ ρ ∈ Sn,
        -((riemannZetaZeroMultiplicity ρ : ℝ) / (Real.sqrt x * Complex.normSq ρ)) ≤
          (riemannZetaReciprocalZeroContribution x ρ).re := by
      intro ρ hρ
      have h1 := Complex.abs_re_le_norm (riemannZetaReciprocalZeroContribution x ρ)
      have h2 := abs_le.mp h1
      rw [norm_riemannZetaReciprocalZeroContribution_of_rh hRH hxpos (hSnz ρ hρ).1
          (hSnz ρ hρ).2] at h2
      linarith [h2.1]
    have hsum_bound :
      -(∑ ρ ∈ Sn, (riemannZetaZeroMultiplicity ρ : ℝ) / (Real.sqrt x * Complex.normSq ρ)) ≤
        ∑ ρ ∈ Sn, (riemannZetaReciprocalZeroContribution x ρ).re := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum hbound
    refine le_trans ?_ hsum_bound
    have hzm :=
      tsum_riemannXiZeroMultiplicity_invNormSq_eq_two_mul_riemannZeroMass_of_riemannHypothesis hRH
    have hxieq :
      ∀ ρ ∈ Sn,
        (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ =
          if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 := by
      intro ρ hρ
      have hxi0 := riemannXi_eq_zero_of_riemannZeta_zero_re_nonneg (hSnz ρ hρ).1 (hSnz ρ hρ).2
      rw [ite_eq_left hxi0, riemannXiZeroMultiplicity_eq_riemannZetaZeroMultiplicity_of_zero hxi0]
    have hsum_eq :
      (∑ ρ ∈ Sn, (riemannZetaZeroMultiplicity ρ : ℝ) / (Real.sqrt x * Complex.normSq ρ)) =
        (Real.sqrt x)⁻¹ *
          ∑ ρ ∈ Sn,
            if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ
            else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [← hxieq ρ hρ]
      field_simp
    rw [hsum_eq]
    have hle_tsum :
      (∑ ρ ∈ Sn,
          if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0) ≤
        2 * riemannZeroMass := by
      rw [← hzm]
      exact
        (summable_riemannXiZeroMultiplicityInvNormSq_of_riemannHypothesis hRH).sum_le_tsum Sn
          (fun ρ _ => by
            split <;> [exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _);
              exact le_refl 0])
    have hinv_nonneg : (0 : ℝ) ≤ (Real.sqrt x)⁻¹ := inv_nonneg.mpr hxsqrtpos.le
    have hmul := mul_le_mul_of_nonneg_left hle_tsum hinv_nonneg
    have heq2 :
      (2 : ℝ) * riemannZeroMass / Real.sqrt x = (Real.sqrt x)⁻¹ * (2 * riemannZeroMass) := by ring
    linarith [hmul, heq2]
  linarith [htriv, hnontriv]

/-- Under RH, combine the closed-form residues at zero and one with the finite
zero-contribution bound to obtain the reciprocal residue-ledger lower bound. -/
theorem re_riemannZetaReciprocalContourResidueLedger_unifiedTau_ge_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x τ : ℝ} (hx : 1 < x) (hτ : 1 < τ) (m : ℕ) :
    Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
        riemannReciprocalTrivialZeroSeries x -
        2 * RiemannXi.riemannZeroMass / Real.sqrt x ≤
      (riemannZetaReciprocalContourResidueLedger x (unifiedRectangleLower m)
          (unifiedTauRectangleUpper τ m)).re := by
  have hxpos : 0 < x := by linarith
  rw [riemannZetaReciprocalContourResidueLedger_unifiedTau_eq hτ, Complex.add_re, Complex.add_re,
    riemannZetaReciprocalResidueAtZero_eq, riemannZetaReciprocalResidueAtOne_eq hxpos]
  have hre0 : (Complex.log (2 * (Real.pi : ℂ)) * (x : ℂ)⁻¹).re = Real.log (2 * Real.pi) / x := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) from by
        push_cast; ring,
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
  linarith [hzero_ledger]

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
