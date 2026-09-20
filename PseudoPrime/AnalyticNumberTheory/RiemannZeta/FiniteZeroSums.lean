import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroMultiplicity

/-!
# Finite zeta zero-contribution bounds under RH
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

open PseudoPrime.AnalyticNumberTheory.RiemannXi in
/-- Under RH and for `x > 0`, the logarithmic-kernel contributions from any
finite set of zeta zeros with nonnegative real part have real part at least
`-2 * riemannZeroMass * √x`, by the inverse-square zero-mass bound. -/
theorem re_sum_riemannZetaLogZeroContribution_nontrivial_ge_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) (S : Finset ℂ)
    (hSzero : ∀ ρ ∈ S, riemannZeta ρ = 0) (hSre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    -(2 * riemannZeroMass * Real.sqrt x) ≤ (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ).re := by
  classical
  have hxsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  rw [Complex.re_sum]
  have hbound :
    ∀ ρ ∈ S,
      -(Real.sqrt x * (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) ≤
        (riemannZetaLogZeroContribution x ρ).re := by
    intro ρ hρ
    have h2 := abs_le.mp (Complex.abs_re_le_norm (riemannZetaLogZeroContribution x ρ))
    rw [norm_riemannZetaLogZeroContribution_of_rh hRH hx (hSzero ρ hρ) (hSre ρ hρ)] at h2
    linarith [h2.1]
  have hsum_bound :
    -(∑ ρ ∈ S, Real.sqrt x * (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) ≤
      ∑ ρ ∈ S, (riemannZetaLogZeroContribution x ρ).re := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hbound
  refine le_trans ?_ hsum_bound
  have hzm :=
    tsum_riemannXiZeroMultiplicity_invNormSq_eq_two_mul_riemannZeroMass_of_riemannHypothesis hRH
  have hxieq :
    ∀ ρ ∈ S,
      (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ =
        if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 := by
    intro ρ hρ
    have hxi0 := riemannXi_eq_zero_of_riemannZeta_zero_re_nonneg (hSzero ρ hρ) (hSre ρ hρ)
    rw [ite_eq_left hxi0, riemannXiZeroMultiplicity_eq_riemannZetaZeroMultiplicity_of_zero hxi0]
  have hsum_eq :
    (∑ ρ ∈ S, Real.sqrt x * (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) =
      Real.sqrt x *
        ∑ ρ ∈ S,
          if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [← hxieq ρ hρ]
    field_simp
  rw [hsum_eq]
  have hle_tsum :
    (∑ ρ ∈ S, if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0) ≤
      2 * riemannZeroMass := by
    rw [← hzm]
    exact
      (summable_riemannXiZeroMultiplicityInvNormSq_of_riemannHypothesis hRH).sum_le_tsum S
        (fun ρ _ => by
          split <;> [exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _);
            exact le_refl 0])
  have hmul := mul_le_mul_of_nonneg_left hle_tsum hxsqrt_nonneg
  linarith [hmul]

/-- Under RH and for `x > 1`, a finite logarithmic-kernel zero sum has real
part at least minus the logarithmic trivial-zero series minus
`2 * riemannZeroMass * √x`. Split zeros into trivial and nontrivial parts. -/
theorem re_sum_riemannZetaLogZeroContribution_ge_of_riemannHypothesis (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 1 < x) (S : Finset ℂ) (hS : ∀ ρ ∈ S, riemannZeta ρ = 0) :
    -riemannZetaLogTrivialZeroSeries x - 2 * RiemannXi.riemannZeroMass * Real.sqrt x ≤
      (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ).re := by
  classical
  have hxpos : 0 < x := by linarith
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
    linarith [sum_logTrivialZeroTerm_le hx St hStriv]
  have hnontriv :=
    re_sum_riemannZetaLogZeroContribution_nontrivial_ge_of_riemannHypothesis hRH hxpos Sn
      (fun ρ hρ => (hSnz ρ hρ).1) (fun ρ hρ => (hSnz ρ hρ).2)
  linarith [htriv, hnontriv]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
