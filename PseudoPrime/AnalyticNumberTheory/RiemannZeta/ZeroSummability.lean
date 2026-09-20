/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Jensen
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.JensenNeg

/-!
# Summable weights on nontrivial zeta zeros

Jensen bounds on height bands give summability of `1/(1+(Im ρ)²)` over
nontrivial zeta zeros, both with and without analytic multiplicity.
Positive and negative heights are treated separately and then combined;
compactness handles the bounded-height bands.
-/

noncomputable section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For any compact set `D` on which `ζ` is analytic, its zeros in `D` form an explicit finite
ledger: a `Finset` `S` with positive multiplicities `m` (matching the local `divisor` values),
covering exactly the zero set `D ∩ ζ⁻¹{0}`. -/
theorem exists_riemannZeta_zero_ledger_of_compact {D : Set ℂ} (hD : IsCompact D)
    (hAn : AnalyticOnNhd ℂ riemannZeta D) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ u ∈ S, 0 < m u) ∧
        (∀ u ∈ S, u ∈ D) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ D, riemannZeta u = 0 → u ∈ S) ∧
        (Function.support (MeromorphicOn.divisor riemannZeta D) = (S : Set ℂ)) ∧
        ∀ u ∈ S, (m u : ℤ) = MeromorphicOn.divisor riemannZeta D u := by
  have h1f : MeromorphicOn riemannZeta D := hAn.meromorphicOn
  have hfin : (MeromorphicOn.divisor riemannZeta D).support.Finite :=
    h1f.divisor_support_finite_of_subset hD subset_rfl
  have hdivnn : ∀ u : ℂ, (0 : ℤ) ≤ MeromorphicOn.divisor riemannZeta D u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u
  have hzeroeq : D ∩ riemannZeta ⁻¹' {0} = Function.support (MeromorphicOn.divisor riemannZeta D) :=
    hAn.meromorphicNFOn.zero_set_eq_divisor_support
      (fun u => meromorphicOrderAt_riemannZeta_ne_top u)
  set S : Finset ℂ := hfin.toFinset with hS_def
  set m : ℂ → ℕ := fun u => (MeromorphicOn.divisor riemannZeta D u).toNat with hm_def
  have hmeq : ∀ u ∈ S, (m u : ℤ) = MeromorphicOn.divisor riemannZeta D u := fun u _ => by
    rw [hm_def]; exact Int.toNat_of_nonneg (hdivnn u)
  have hSsupp : ∀ u, u ∈ S ↔ u ∈ D ∧ riemannZeta u = 0 := by
    intro u
    rw [hS_def, Set.Finite.mem_toFinset]
    change u ∈ Function.support (MeromorphicOn.divisor riemannZeta D) ↔ u ∈ D ∧ riemannZeta u = 0
    rw [← hzeroeq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hmpos : ∀ u ∈ S, 0 < m u := by
    intro u hu
    have hune : u ∈ Function.support (MeromorphicOn.divisor riemannZeta D) := by
      rw [hS_def, Set.Finite.mem_toFinset] at hu; exact hu
    rw [Function.mem_support] at hune
    rw [hm_def]
    simp only
    apply Nat.pos_of_ne_zero
    intro h0
    apply hune
    have hcast := Int.toNat_of_nonneg (hdivnn u)
    rw [h0] at hcast
    omega
  exact
    ⟨S, m, hmpos, fun u hu => ((hSsupp u).mp hu).1, fun u hu => ((hSsupp u).mp hu).2,
      fun u huD hu0 => (hSsupp u).mpr ⟨huD, hu0⟩, (Set.Finite.coe_toFinset hfin).symm, hmeq⟩

/-- On an analytic compact ledger, the divisor multiplicity is exactly the global analytic
zero multiplicity of zeta. This identifies Jensen's local multiplicity certificates with the
multiplicities used by the explicit formula. -/
theorem riemannZetaZeroMultiplicity_eq_divisor_toNat_of_mem_compact_ledger {D : Set ℂ}
    (hAn : AnalyticOnNhd ℂ riemannZeta D) {u : ℂ} (hu : u ∈ D) (hzero : riemannZeta u = 0) :
    riemannZetaZeroMultiplicity u = (MeromorphicOn.divisor riemannZeta D u).toNat := by
  have hu1 : u ≠ 1 := by
    intro h
    rw [h] at hzero
    exact riemannZeta_one_ne_zero hzero
  have hfinite : analyticOrderAt riemannZeta u ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hu1
  unfold riemannZetaZeroMultiplicity
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hu]
  generalize hA : analyticOrderAt riemannZeta u = A
  lift A to ℕ using (by rwa [← hA])
  simp only [analyticOrderNatAt, hA, ENat.map_natCast, WithTop.untop₀_coe]
  rfl

/-- The Jensen-ball zero ledger (`n : ℝ`, `8 ≤ n`) with the explicit multiplicity-sum bound
from the zeta-side estimate, reformulating
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.finsum_divisor_riemannZeta_le_explicit`
as a `Finset.sum`. -/
theorem exists_jensenBall_zero_ledger {T : ℝ} (hT : 8 ≤ T) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ u ∈ S, 0 < m u) ∧
        (∀ u ∈ S, u ∈ Metric.closedBall (jensenCenter T) (37 / 10)) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ Metric.closedBall (jensenCenter T) (37 / 10), riemannZeta u = 0 → u ∈ S) ∧
        ((∑ u ∈ S, m u : ℕ) : ℝ) ≤ jensenLogConst * Real.log (T + 2) := by
  set D : Set ℂ := Metric.closedBall (jensenCenter T) (37 / 10) with hD_def
  have hAn : AnalyticOnNhd ℂ riemannZeta D :=
    (jensen_analyticOnNhd (by linarith : (4 : ℝ) ≤ T)).mono
      (Metric.closedBall_subset_closedBall (by norm_num only))
  obtain ⟨S, m, hmpos, hSD, hSzero, hDzero, hsupp_eq, hmeq⟩ :=
    exists_riemannZeta_zero_ledger_of_compact (isCompact_closedBall _ _) hAn
  refine ⟨S, m, hmpos, hSD, hSzero, hDzero, ?_⟩
  have hSsub : Function.support (MeromorphicOn.divisor riemannZeta D) ⊆ (S : Finset ℂ) :=
    hsupp_eq.le
  have heq1 : (∑ u ∈ S, (m u : ℤ)) = ∑ᶠ u, MeromorphicOn.divisor riemannZeta D u :=
    (Finset.sum_congr rfl hmeq).trans (finsum_eq_sum_of_support_subset _ hSsub).symm
  have hbound := finsum_divisor_riemannZeta_le_explicit hT
  have hcast : ((∑ u ∈ S, (m u : ℤ) : ℤ) : ℝ) ≤ jensenLogConst * Real.log (T + 2) := by
    rw [heq1]; exact hbound
  exact_mod_cast hcast

/-- The Jensen-ball ledger may use the global analytic zero multiplicity directly. Its total
multiplicity retains the explicit Jensen bound, so it is suitable for a multiplicity-aware
Hadamard construction. -/
theorem exists_jensenBall_zero_ledger_with_analyticMultiplicity {T : ℝ} (hT : 8 ≤ T) :
    ∃ S : Finset ℂ,
      (∀ u ∈ S, 0 < riemannZetaZeroMultiplicity u) ∧
        (∀ u ∈ S, u ∈ Metric.closedBall (jensenCenter T) (37 / 10)) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ Metric.closedBall (jensenCenter T) (37 / 10), riemannZeta u = 0 → u ∈ S) ∧
        ((∑ u ∈ S, riemannZetaZeroMultiplicity u : ℕ) : ℝ) ≤ jensenLogConst * Real.log (T + 2) := by
  set D : Set ℂ := Metric.closedBall (jensenCenter T) (37 / 10) with hD_def
  have hAn : AnalyticOnNhd ℂ riemannZeta D :=
    (jensen_analyticOnNhd (by linarith : (4 : ℝ) ≤ T)).mono
      (Metric.closedBall_subset_closedBall (by norm_num only))
  obtain ⟨S, m, hmpos, hSD, hSzero, hDzero, hsupp_eq, hmeq⟩ :=
    exists_riemannZeta_zero_ledger_of_compact (isCompact_closedBall _ _) hAn
  have hmult : ∀ u ∈ S, riemannZetaZeroMultiplicity u = m u := by
    intro u hu
    have hdiv :=
      riemannZetaZeroMultiplicity_eq_divisor_toNat_of_mem_compact_ledger hAn (hSD u hu)
        (hSzero u hu)
    rw [← hmeq u hu] at hdiv
    exact hdiv
  refine ⟨S, ?_, hSD, hSzero, hDzero, ?_⟩
  · intro u hu
    rw [hmult u hu]
    exact hmpos u hu
  · have hsum : (∑ u ∈ S, riemannZetaZeroMultiplicity u : ℕ) = ∑ u ∈ S, m u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hmult u hu]
    rw [hsum]
    have hSsub : Function.support (MeromorphicOn.divisor riemannZeta D) ⊆ (S : Finset ℂ) :=
      hsupp_eq.le
    have heq1 : (∑ u ∈ S, (m u : ℤ)) = ∑ᶠ u, MeromorphicOn.divisor riemannZeta D u :=
      (Finset.sum_congr rfl hmeq).trans (finsum_eq_sum_of_support_subset _ hSsub).symm
    have hbound := finsum_divisor_riemannZeta_le_explicit hT
    have hcast : ((∑ u ∈ S, (m u : ℤ) : ℤ) : ℝ) ≤ jensenLogConst * Real.log (T + 2) := by
      rw [heq1]
      exact hbound
    exact_mod_cast hcast

/-- Any finite family of zeta-zeros inside a positive-height Jensen ball has total global
analytic multiplicity bounded by the Jensen certificate. This is the reusable height-band
estimate for the forthcoming multiplicity-weighted summability argument. -/
theorem sum_riemannZetaZeroMultiplicity_le_jensenBall_bound {T : ℝ} (hT : 8 ≤ T) {U : Finset ℂ}
    (hU : ∀ u ∈ U, u ∈ Metric.closedBall (jensenCenter T) (37 / 10))
    (hzero : ∀ u ∈ U, riemannZeta u = 0) :
    ((∑ u ∈ U, riemannZetaZeroMultiplicity u : ℕ) : ℝ) ≤ jensenLogConst * Real.log (T + 2) := by
  obtain ⟨S, hmpos, hSD, hSzero, hDzero, hbound⟩ :=
    exists_jensenBall_zero_ledger_with_analyticMultiplicity hT
  have hsub : U ⊆ S := by
    intro u hu
    exact hDzero u (hU u hu) (hzero u hu)
  have hsum : ∑ u ∈ U, riemannZetaZeroMultiplicity u ≤ ∑ u ∈ S, riemannZetaZeroMultiplicity u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro u _ _
    exact Nat.zero_le _
  have hsumR :
    ((∑ u ∈ U, riemannZetaZeroMultiplicity u : ℕ) : ℝ) ≤
      ∑ u ∈ S, riemannZetaZeroMultiplicity u := by
    exact_mod_cast hsum
  exact hsumR.trans hbound

/-- The mirror of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_jensenBall_zero_ledger`
for `T ≤ -8`. -/
theorem exists_jensenBall_zero_ledger_neg {T : ℝ} (hT : T ≤ -8) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ u ∈ S, 0 < m u) ∧
        (∀ u ∈ S, u ∈ Metric.closedBall (jensenCenter T) (37 / 10)) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ Metric.closedBall (jensenCenter T) (37 / 10), riemannZeta u = 0 → u ∈ S) ∧
        ((∑ u ∈ S, m u : ℕ) : ℝ) ≤ jensenLogConst * Real.log (-T + 2) := by
  set D : Set ℂ := Metric.closedBall (jensenCenter T) (37 / 10) with hD_def
  have hAn : AnalyticOnNhd ℂ riemannZeta D :=
    jensen_analyticOnNhd_of_abs (T := T)
        (by
          rw [abs_of_neg (by linarith : T < 0)]; linarith) |>.mono
      (Metric.closedBall_subset_closedBall (by norm_num only))
  obtain ⟨S, m, hmpos, hSD, hSzero, hDzero, hsupp_eq, hmeq⟩ :=
    exists_riemannZeta_zero_ledger_of_compact (isCompact_closedBall _ _) hAn
  refine ⟨S, m, hmpos, hSD, hSzero, hDzero, ?_⟩
  have hSsub : Function.support (MeromorphicOn.divisor riemannZeta D) ⊆ (S : Finset ℂ) :=
    hsupp_eq.le
  have heq1 : (∑ u ∈ S, (m u : ℤ)) = ∑ᶠ u, MeromorphicOn.divisor riemannZeta D u :=
    (Finset.sum_congr rfl hmeq).trans (finsum_eq_sum_of_support_subset _ hSsub).symm
  have hbound := finsum_divisor_riemannZeta_le_explicit_neg hT
  have hcast : ((∑ u ∈ S, (m u : ℤ) : ℤ) : ℝ) ≤ jensenLogConst * Real.log (-T + 2) := by
    rw [heq1]; exact hbound
  exact_mod_cast hcast

/-- The negative-height Jensen ledger also carries global analytic zeta multiplicities with the
same explicit local bound. -/
theorem exists_jensenBall_zero_ledger_neg_with_analyticMultiplicity {T : ℝ} (hT : T ≤ -8) :
    ∃ S : Finset ℂ,
      (∀ u ∈ S, 0 < riemannZetaZeroMultiplicity u) ∧
        (∀ u ∈ S, u ∈ Metric.closedBall (jensenCenter T) (37 / 10)) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ Metric.closedBall (jensenCenter T) (37 / 10), riemannZeta u = 0 → u ∈ S) ∧
        ((∑ u ∈ S, riemannZetaZeroMultiplicity u : ℕ) : ℝ) ≤
          jensenLogConst * Real.log (-T + 2) := by
  set D : Set ℂ := Metric.closedBall (jensenCenter T) (37 / 10) with hD_def
  have hAn : AnalyticOnNhd ℂ riemannZeta D :=
    jensen_analyticOnNhd_of_abs (T := T)
        (by
          rw [abs_of_neg (by linarith : T < 0)]; linarith) |>.mono
      (Metric.closedBall_subset_closedBall (by norm_num only))
  obtain ⟨S, m, hmpos, hSD, hSzero, hDzero, hsupp_eq, hmeq⟩ :=
    exists_riemannZeta_zero_ledger_of_compact (isCompact_closedBall _ _) hAn
  have hmult : ∀ u ∈ S, riemannZetaZeroMultiplicity u = m u := by
    intro u hu
    have hdiv :=
      riemannZetaZeroMultiplicity_eq_divisor_toNat_of_mem_compact_ledger hAn (hSD u hu)
        (hSzero u hu)
    rw [← hmeq u hu] at hdiv
    exact hdiv
  refine ⟨S, ?_, hSD, hSzero, hDzero, ?_⟩
  · intro u hu
    rw [hmult u hu]
    exact hmpos u hu
  · have hsum : (∑ u ∈ S, riemannZetaZeroMultiplicity u : ℕ) = ∑ u ∈ S, m u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hmult u hu]
    rw [hsum]
    have hSsub : Function.support (MeromorphicOn.divisor riemannZeta D) ⊆ (S : Finset ℂ) :=
      hsupp_eq.le
    have heq1 : (∑ u ∈ S, (m u : ℤ)) = ∑ᶠ u, MeromorphicOn.divisor riemannZeta D u :=
      (Finset.sum_congr rfl hmeq).trans (finsum_eq_sum_of_support_subset _ hSsub).symm
    have hbound := finsum_divisor_riemannZeta_le_explicit_neg hT
    have hcast : ((∑ u ∈ S, (m u : ℤ) : ℤ) : ℝ) ≤ jensenLogConst * Real.log (-T + 2) := by
      rw [heq1]
      exact hbound
    exact_mod_cast hcast

/-- Any finite family of zeta-zeros inside a negative-height Jensen ball has total global
analytic multiplicity bounded by the mirrored Jensen certificate. -/
theorem sum_riemannZetaZeroMultiplicity_le_jensenBall_bound_neg {T : ℝ} (hT : T ≤ -8) {U : Finset ℂ}
    (hU : ∀ u ∈ U, u ∈ Metric.closedBall (jensenCenter T) (37 / 10))
    (hzero : ∀ u ∈ U, riemannZeta u = 0) :
    ((∑ u ∈ U, riemannZetaZeroMultiplicity u : ℕ) : ℝ) ≤ jensenLogConst * Real.log (-T + 2) := by
  obtain ⟨S, hmpos, hSD, hSzero, hDzero, hbound⟩ :=
    exists_jensenBall_zero_ledger_neg_with_analyticMultiplicity hT
  have hsub : U ⊆ S := by
    intro u hu
    exact hDzero u (hU u hu) (hzero u hu)
  have hsum : ∑ u ∈ U, riemannZetaZeroMultiplicity u ≤ ∑ u ∈ S, riemannZetaZeroMultiplicity u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro u _ _
    exact Nat.zero_le _
  have hsumR :
    ((∑ u ∈ U, riemannZetaZeroMultiplicity u : ℕ) : ℝ) ≤
      ∑ u ∈ S, riemannZetaZeroMultiplicity u := by
    exact_mod_cast hsum
  exact hsumR.trans hbound

/-- The tail series
`∑_n PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenLogConst·log(n+2)/(1+n²)`
converges (comparison with the `p = 3/2` p-series, via `log t ≤ t^{1/2}` eventually from
`Real.isLittleO_log_rpow_atTop`). -/
theorem summable_jensenLogConst_mul_log_div_sq :
    Summable (fun n : ℕ => jensenLogConst * Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2)) := by
  apply summable_of_isBigO_nat (g := fun n : ℕ => 1 / ((n : ℝ) + 2) ^ (3 / 2 : ℝ))
  · have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num only)
    have hshift := (summable_nat_add_iff 2).mpr hbase
    simpa only [one_div, Nat.cast_add, Nat.cast_ofNat] using hshift
  · have hlogle : ∀ᶠ t : ℝ in Filter.atTop, Real.log t ≤ t ^ (1 / 2 : ℝ) := by
      have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num only)).eventuallyLE
      filter_upwards [h, Filter.eventually_gt_atTop (1 : ℝ)] with t ht ht1
      have hlogpos : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hrpow_pos : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
      rwa [Real.norm_of_nonneg hlogpos, Real.norm_of_nonneg hrpow_pos] at ht
    have htendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop
    have hev := htendsto.eventually hlogle
    apply Asymptotics.IsBigO.of_bound (4 * jensenLogConst)
    filter_upwards [hev, Filter.eventually_ge_atTop (2 : ℕ)] with n hn hn2
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hn2pos : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    have hLCnn : (0 : ℝ) ≤ jensenLogConst := jensenLogConst_pos.le
    have hlognn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hrpow_eq :
      ((n : ℝ) + 2) ^ (1 / 2 : ℝ) * ((n : ℝ) + 2) ^ (3 / 2 : ℝ) = ((n : ℝ) + 2) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hn2pos, show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num only, Real.rpow_two]
    have hpoly : ((n : ℝ) + 2) ^ (2 : ℕ) ≤ 4 * (1 + (n : ℝ) ^ 2) := by nlinarith
    have hrpow32pos : (0 : ℝ) < ((n : ℝ) + 2) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn2pos _
    have hstep :
      Real.log ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ (3 / 2 : ℝ) ≤
        ((n : ℝ) + 2) ^ (1 / 2 : ℝ) * ((n : ℝ) + 2) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hn hrpow32pos.le
    have hkey : Real.log ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ (3 / 2 : ℝ) ≤ 4 * (1 + (n : ℝ) ^ 2) := by
      rw [hrpow_eq] at hstep; linarith
    have hmain : Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2) ≤ 4 / ((n : ℝ) + 2) ^ (3 / 2 : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hrpow32pos]
      linarith [hkey]
    have hgoal :
      jensenLogConst * (Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2)) ≤
        jensenLogConst * (4 / ((n : ℝ) + 2) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain hLCnn
    calc
      jensenLogConst * Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2) =
          jensenLogConst * (Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2)) :=
        by ring
      _ ≤ jensenLogConst * (4 / ((n : ℝ) + 2) ^ (3 / 2 : ℝ)) := hgoal
      _ = 4 * jensenLogConst * (1 / ((n : ℝ) + 2) ^ (3 / 2 : ℝ)) := by ring

/-- A positive high-height band has a multiplicity-weighted reciprocal-square
bound. This supplies the local estimate for summing over height bands. -/
theorem sum_riemannZetaZeroMultiplicity_div_one_add_im_sq_le_jensenBand {j : ℕ} (hj : 8 ≤ j)
    {U : Finset ℂ}
    (hU : ∀ s ∈ U, riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ ⌊s.im⌋₊ = j) :
    ∑ s ∈ U, (riemannZetaZeroMultiplicity s : ℝ) / (1 + s.im ^ 2) ≤
      jensenLogConst * Real.log ((j : ℝ) + 2) / (1 + (j : ℝ) ^ 2) := by
  have hjR : (8 : ℝ) ≤ j := by exact_mod_cast hj
  have hball : ∀ s ∈ U, s ∈ Metric.closedBall (jensenCenter (j : ℝ)) (37 / 10) := by
    intro s hs
    obtain ⟨hzero, _, _, him, hfloor⟩ := hU s hs
    have hfloor_le := Nat.floor_le him
    have hfloor_lt := Nat.lt_floor_add_one s.im
    rw [hfloor] at hfloor_le hfloor_lt
    apply riemannZeta_zero_mem_jensenBall hjR hzero
    rw [abs_le]
    constructor <;> linarith
  have hzero : ∀ s ∈ U, riemannZeta s = 0 := fun s hs => (hU s hs).1
  have hsum := sum_riemannZetaZeroMultiplicity_le_jensenBall_bound hjR hball hzero
  have hterm :
    ∀ s ∈ U,
      (riemannZetaZeroMultiplicity s : ℝ) / (1 + s.im ^ 2) ≤
        (riemannZetaZeroMultiplicity s : ℝ) / (1 + (j : ℝ) ^ 2) := by
    intro s hs
    obtain ⟨_, _, _, him, hfloor⟩ := hU s hs
    have hfloor_le := Nat.floor_le him
    rw [hfloor] at hfloor_le
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  calc
    ∑ s ∈ U, (riemannZetaZeroMultiplicity s : ℝ) / (1 + s.im ^ 2) ≤
        ∑ s ∈ U, (riemannZetaZeroMultiplicity s : ℝ) / (1 + (j : ℝ) ^ 2) :=
      Finset.sum_le_sum hterm
    _ = (1 / (1 + (j : ℝ) ^ 2)) * ∑ s ∈ U, riemannZetaZeroMultiplicity s := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (1 / (1 + (j : ℝ) ^ 2)) * (jensenLogConst * Real.log ((j : ℝ) + 2)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = jensenLogConst * Real.log ((j : ℝ) + 2) / (1 + (j : ℝ) ^ 2) := by ring

/-- A negative high-height band of nontrivial zeta-zeros has the corresponding
multiplicity-weighted reciprocal-square bound, obtained from the mirrored Jensen certificate. -/
theorem sum_riemannZetaZeroMultiplicity_div_one_add_im_sq_le_jensenBand_neg {j : ℕ} (hj : 8 ≤ j)
    {U : Finset ℂ}
    (hU : ∀ s ∈ U, riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0 ∧ ⌊-s.im⌋₊ = j) :
    ∑ s ∈ U, (riemannZetaZeroMultiplicity s : ℝ) / (1 + s.im ^ 2) ≤
      jensenLogConst * Real.log ((j : ℝ) + 2) / (1 + (j : ℝ) ^ 2) := by
  have hjR : (8 : ℝ) ≤ j := by exact_mod_cast hj
  have hball : ∀ s ∈ U, s ∈ Metric.closedBall (jensenCenter (-(j : ℝ))) (37 / 10) := by
    intro s hs
    obtain ⟨hzero, _, _, him, hfloor⟩ := hU s hs
    have hfloor_le := Nat.floor_le (neg_nonneg.mpr (le_of_lt him))
    have hfloor_lt := Nat.lt_floor_add_one (-s.im)
    rw [hfloor] at hfloor_le hfloor_lt
    apply riemannZeta_zero_mem_jensenBall_neg (by linarith) hzero
    rw [abs_le]
    constructor <;> linarith
  have hzero : ∀ s ∈ U, riemannZeta s = 0 := fun s hs => (hU s hs).1
  have hsum :=
    sum_riemannZetaZeroMultiplicity_le_jensenBall_bound_neg (T := -(j : ℝ)) (by linarith) hball
      hzero
  simp only [neg_neg] at hsum
  have hterm :
    ∀ s ∈ U,
      (riemannZetaZeroMultiplicity s : ℝ) / (1 + s.im ^ 2) ≤
        (riemannZetaZeroMultiplicity s : ℝ) / (1 + (j : ℝ) ^ 2) := by
    intro s hs
    obtain ⟨_, _, _, him, hfloor⟩ := hU s hs
    have hfloor_le := Nat.floor_le (neg_nonneg.mpr (le_of_lt him))
    rw [hfloor] at hfloor_le
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  calc
    ∑ s ∈ U, (riemannZetaZeroMultiplicity s : ℝ) / (1 + s.im ^ 2) ≤
        ∑ s ∈ U, (riemannZetaZeroMultiplicity s : ℝ) / (1 + (j : ℝ) ^ 2) :=
      Finset.sum_le_sum hterm
    _ = (1 / (1 + (j : ℝ) ^ 2)) * ∑ s ∈ U, riemannZetaZeroMultiplicity s := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (1 / (1 + (j : ℝ) ^ 2)) * (jensenLogConst * Real.log ((j : ℝ) + 2)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = jensenLogConst * Real.log ((j : ℝ) + 2) / (1 + (j : ℝ) ^ 2) := by ring

/-- The nontrivial zeta zeros with `0 ≤ Im s < 8` form a finite set.
They lie in the compact disk centered at `1/2+4i` of radius five; compact
zero finiteness also handles the presence of the pole in that disk. -/
theorem lowBand_zeros_finite :
    {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im < 8}.Finite := by
  apply
    Set.Finite.subset
      (finite_riemannZeta_zerosOn_compact (K := Metric.closedBall (1 / 2 + 4 * Complex.I) 5)
        (isCompact_closedBall _ _))
  rintro s ⟨hz, hre0, hre1, him0, him8⟩
  refine ⟨?_, hz⟩
  rw [Metric.mem_closedBall, dist_eq_norm, Complex.norm_eq_sqrt_sq_add_sq]
  have hre_eq : (s - (1 / 2 + 4 * Complex.I)).re = s.re - 1 / 2 := by
    simp only [one_div, Complex.sub_re, Complex.add_re, Complex.inv_re, Complex.re_ofNat,
      Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re, Complex.I_re, mul_zero,
      Complex.im_ofNat, Complex.I_im, mul_one, sub_self, add_zero]
  have him_eq : (s - (1 / 2 + 4 * Complex.I)).im = s.im - 4 := by
    simp only [one_div, Complex.sub_im, Complex.add_im, Complex.inv_im, Complex.im_ofNat, neg_zero,
      Complex.normSq_ofNat, zero_div, Complex.mul_im, Complex.re_ofNat, Complex.I_im, mul_one,
      Complex.I_re, mul_zero, add_zero, zero_add]
  rw [hre_eq, him_eq, show (5 : ℝ) = Real.sqrt (5 ^ 2) from (Real.sqrt_sq (by norm_num only)).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg hre0 (show (0 : ℝ) ≤ 1 - s.re by linarith),
    mul_nonneg him0 (show (0 : ℝ) ≤ 8 - s.im by linarith)]

/-- The mirror of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.lowBand_zeros_finite`
for `-8 < Im s < 0`. -/
theorem lowBand_zeros_finite_neg :
    {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ -8 < s.im ∧ s.im < 0}.Finite := by
  apply
    Set.Finite.subset
      (finite_riemannZeta_zerosOn_compact (K := Metric.closedBall (1 / 2 - 4 * Complex.I) 5)
        (isCompact_closedBall _ _))
  rintro s ⟨hz, hre0, hre1, him0, him8⟩
  refine ⟨?_, hz⟩
  rw [Metric.mem_closedBall, dist_eq_norm, Complex.norm_eq_sqrt_sq_add_sq]
  have hre_eq : (s - (1 / 2 - 4 * Complex.I)).re = s.re - 1 / 2 := by
    simp only [one_div, Complex.sub_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.I_re, mul_zero, Complex.im_ofNat, Complex.I_im,
      mul_one, sub_self, sub_zero]
  have him_eq : (s - (1 / 2 - 4 * Complex.I)).im = s.im + 4 := by
    simp only [one_div, Complex.sub_im, Complex.inv_im, Complex.im_ofNat, neg_zero,
      Complex.normSq_ofNat, zero_div, Complex.mul_im, Complex.re_ofNat, Complex.I_im, mul_one,
      Complex.I_re, mul_zero, add_zero, zero_sub, sub_neg_eq_add]
  rw [hre_eq, him_eq, show (5 : ℝ) = Real.sqrt (5 ^ 2) from (Real.sqrt_sq (by norm_num only)).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg hre0 (show (0 : ℝ) ≤ 1 - s.re by linarith),
    mul_nonneg (show (0 : ℝ) ≤ s.im + 8 by linarith) (show (0 : ℝ) ≤ -s.im by linarith)]

/-- The multiplicity-weighted positive-height reciprocal-square summand for nontrivial zeta
zeros. This is the summand needed by the infinite xi Hadamard product. -/
noncomputable def nontrivialZetaZeroMultiplicityWeight (s : ℂ) : ℝ :=
  if riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im then
    riemannZetaZeroMultiplicity s / (1 + s.im ^ 2)
  else 0

/-- The positive-height multiplicity weight is nonnegative. -/
theorem nontrivialZetaZeroMultiplicityWeight_nonneg (s : ℂ) :
    0 ≤ nontrivialZetaZeroMultiplicityWeight s := by
  unfold nontrivialZetaZeroMultiplicityWeight
  split <;> positivity

/-- The zero-weight summand (multiplicity ignored): `1/(1+Im s²)` at a nontrivial zero of `ζ` with
`0 ≤ Im s`, and `0` elsewhere. -/
noncomputable def nontrivialZetaZeroWeight (s : ℂ) : ℝ :=
  if riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im then 1 / (1 + s.im ^ 2) else 0

theorem nontrivialZetaZeroWeight_nonneg (s : ℂ) : 0 ≤ nontrivialZetaZeroWeight s := by
  unfold nontrivialZetaZeroWeight
  split
  · positivity
  · exact le_refl 0

/-- The multiplicity-weighted negative-height reciprocal-square summand for nontrivial zeta
zeros. Together with the positive summand, it is the desired global zero-series integrand. -/
noncomputable def nontrivialZetaZeroMultiplicityWeightNeg (s : ℂ) : ℝ :=
  if riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0 then
    riemannZetaZeroMultiplicity s / (1 + s.im ^ 2)
  else 0

/-- The negative-height multiplicity weight is nonnegative. -/
theorem nontrivialZetaZeroMultiplicityWeightNeg_nonneg (s : ℂ) :
    0 ≤ nontrivialZetaZeroMultiplicityWeightNeg s := by
  unfold nontrivialZetaZeroMultiplicityWeightNeg
  split <;> positivity

/-- The reciprocal-square height weight is summable over nontrivial zeta zeros
with `Im ρ ≥ 0`, ignoring multiplicity. -/
theorem summable_nontrivialZetaZeroWeight : Summable nontrivialZetaZeroWeight := by
  classical
  set L : ℝ := (lowBand_zeros_finite.toFinset.card : ℝ) with hL_def
  set g : ℕ → ℝ := fun n => jensenLogConst * Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2) with hg_def
  have hgsum : Summable g := summable_jensenLogConst_mul_log_div_sq
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    have h1 := jensenLogConst_pos.le
    have h2 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg
        (by
          have := Nat.cast_nonneg (α := ℝ) n; linarith)
    simp only [hg_def]
    positivity
  refine summable_of_sum_le nontrivialZetaZeroWeight_nonneg (c := L + ∑' n, g n) fun u => ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun s => s.im < 8)]
  have hlow : ∑ s ∈ u.filter (fun s => s.im < 8), nontrivialZetaZeroWeight s ≤ L := by
    calc
      ∑ s ∈ u.filter (fun s => s.im < 8), nontrivialZetaZeroWeight s ≤
          ∑ s ∈ u.filter (fun s => s.im < 8),
            (if s ∈ lowBand_zeros_finite.toFinset then (1 : ℝ) else 0) :=
        by
        apply Finset.sum_le_sum
        intro s hs
        rw [Finset.mem_filter] at hs
        unfold nontrivialZetaZeroWeight
        by_cases hcond : riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im
        · rw [ite_eq_left hcond]
          have hmemLow : s ∈ lowBand_zeros_finite.toFinset := by
            rw [Set.Finite.mem_toFinset]
            exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, hs.2⟩
          rw [ite_eq_left hmemLow, div_le_one (by positivity)]
          nlinarith [sq_nonneg s.im]
        · rw [ite_eq_right hcond]; split_ifs <;> norm_num only
      _ =
          ((u.filter (fun s => s.im < 8)).filter
              (fun s => s ∈ lowBand_zeros_finite.toFinset)).card :=
        Finset.sum_boole _ _
      _ ≤ L := by
        rw [hL_def]
        exact_mod_cast Finset.card_le_card (fun s hs => (Finset.mem_filter.mp hs).2)
  have hhigh : ∑ s ∈ u.filter (fun s => ¬s.im < 8), nontrivialZetaZeroWeight s ≤ ∑' n, g n := by
    set uh := u.filter (fun s => ¬s.im < 8) with huh_def
    set t : Finset ℕ := uh.image (fun s => ⌊s.im⌋₊) with ht_def
    have hmaps : ∀ s ∈ uh, ⌊s.im⌋₊ ∈ t := fun s hs => Finset.mem_image_of_mem _ hs
    have hband :
      ∀ j ∈ t, ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j), nontrivialZetaZeroWeight s ≤ g j := by
      intro j hj
      have hj8 : (8 : ℕ) ≤ j := by
        rw [ht_def, Finset.mem_image] at hj
        obtain ⟨s, hs, hsj⟩ := hj
        rw [huh_def, Finset.mem_filter] at hs
        push Not at hs
        rw [← hsj]
        exact Nat.le_floor (by exact_mod_cast hs.2)
      have hj8R : (8 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj8
      obtain ⟨S, m, hmpos, hSD, hSzero, hDzero, hmeq⟩ :=
        exists_jensenBall_zero_ledger (T := (j : ℝ)) hj8R
      have hfilter_sub :
        ∀ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j),
          nontrivialZetaZeroWeight s ≤ (if s ∈ S then (1 : ℝ) / (1 + (j : ℝ) ^ 2) else 0) := by
        intro s hs
        rw [Finset.mem_filter] at hs
        obtain ⟨hsuh, hsfl⟩ := hs
        rw [huh_def, Finset.mem_filter] at hsuh
        push Not at hsuh
        have hsim0 : (0 : ℝ) ≤ s.im := by linarith [hsuh.2]
        have hfl_le := Nat.floor_le hsim0
        have hfl_lt := Nat.lt_floor_add_one s.im
        rw [hsfl] at hfl_le hfl_lt
        unfold nontrivialZetaZeroWeight
        by_cases hcond : riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im
        · rw [ite_eq_left hcond]
          have him2 : |s.im - (j : ℝ)| ≤ 2 := by
            rw [abs_le]; constructor <;> linarith
          have hmemD : s ∈ Metric.closedBall (jensenCenter (j : ℝ)) (37 / 10) :=
            riemannZeta_zero_mem_jensenBall hj8R hcond.1 him2
          have hmemS : s ∈ S := hDzero s hmemD hcond.1
          rw [ite_eq_left hmemS]
          apply div_le_div_of_nonneg_left (by norm_num only) (by positivity)
          nlinarith
        · rw [ite_eq_right hcond]
          split_ifs <;> positivity
      calc
        ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j), nontrivialZetaZeroWeight s ≤
            ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j),
              (if s ∈ S then (1 : ℝ) / (1 + (j : ℝ) ^ 2) else 0) :=
          Finset.sum_le_sum hfilter_sub
        _ =
            ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j),
              (1 / (1 + (j : ℝ) ^ 2)) * (if s ∈ S then (1 : ℝ) else 0) :=
          by
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : s ∈ S <;> simp only [h, reduceIte, one_div, mul_one, mul_zero]
        _ =
            (1 / (1 + (j : ℝ) ^ 2)) *
              ((uh.filter (fun s => ⌊s.im⌋₊ = j)).filter (fun s => s ∈ S)).card :=
          by rw [← Finset.mul_sum, Finset.sum_boole]
        _ ≤ (1 / (1 + (j : ℝ) ^ 2)) * (∑ u ∈ S, m u) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (((uh.filter (fun s => ⌊s.im⌋₊ = j)).filter (fun s => s ∈ S)).card : ℝ) ≤
                (S.card : ℝ) :=
              mod_cast Finset.card_le_card (fun s hs => (Finset.mem_filter.mp hs).2)
            _ ≤ (∑ u ∈ S, m u : ℕ) := by
              have : S.card ≤ ∑ u ∈ S, m u := by
                calc
                  S.card = ∑ _u ∈ S, 1 := (Finset.card_eq_sum_ones S)
                  _ ≤ ∑ u ∈ S, m u := Finset.sum_le_sum (fun u hu => hmpos u hu)
              exact_mod_cast this
        _ ≤ (1 / (1 + (j : ℝ) ^ 2)) * (jensenLogConst * Real.log ((j : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_left hmeq (by positivity)
        _ = g j := by
          simp only [hg_def]; ring
    calc
      ∑ s ∈ uh, nontrivialZetaZeroWeight s =
          ∑ j ∈ t, ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j), nontrivialZetaZeroWeight s :=
        (Finset.sum_fiberwise_of_maps_to hmaps nontrivialZetaZeroWeight).symm
      _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum hband
      _ ≤ ∑' n, g n := hgsum.sum_le_tsum t (fun n _ => hgnn n)
  linarith [hlow, hhigh]

/-- The mirror of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.nontrivialZetaZeroWeight`
for `Im s < 0`. -/
noncomputable def nontrivialZetaZeroWeightNeg (s : ℂ) : ℝ :=
  if riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0 then 1 / (1 + s.im ^ 2) else 0

theorem nontrivialZetaZeroWeightNeg_nonneg (s : ℂ) : 0 ≤ nontrivialZetaZeroWeightNeg s := by
  unfold nontrivialZetaZeroWeightNeg
  split
  · positivity
  · exact le_refl 0

/-- The reciprocal-square height weight is summable over nontrivial zeta zeros
with `Im ρ < 0`, using the conjugated Jensen bound and finite low-height band. -/
theorem summable_nontrivialZetaZeroWeightNeg : Summable nontrivialZetaZeroWeightNeg := by
  classical
  set L : ℝ := (lowBand_zeros_finite_neg.toFinset.card : ℝ) with hL_def
  set g : ℕ → ℝ := fun n => jensenLogConst * Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2) with hg_def
  have hgsum : Summable g := summable_jensenLogConst_mul_log_div_sq
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    have h1 := jensenLogConst_pos.le
    have h2 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg
        (by
          have := Nat.cast_nonneg (α := ℝ) n; linarith)
    simp only [hg_def]
    positivity
  refine summable_of_sum_le nontrivialZetaZeroWeightNeg_nonneg (c := L + ∑' n, g n) fun u => ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun s => -8 < s.im)]
  have hlow : ∑ s ∈ u.filter (fun s => -8 < s.im), nontrivialZetaZeroWeightNeg s ≤ L := by
    calc
      ∑ s ∈ u.filter (fun s => -8 < s.im), nontrivialZetaZeroWeightNeg s ≤
          ∑ s ∈ u.filter (fun s => -8 < s.im),
            (if s ∈ lowBand_zeros_finite_neg.toFinset then (1 : ℝ) else 0) :=
        by
        apply Finset.sum_le_sum
        intro s hs
        rw [Finset.mem_filter] at hs
        unfold nontrivialZetaZeroWeightNeg
        by_cases hcond : riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0
        · rw [ite_eq_left hcond]
          have hmemLow : s ∈ lowBand_zeros_finite_neg.toFinset := by
            rw [Set.Finite.mem_toFinset]
            exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hs.2, hcond.2.2.2⟩
          rw [ite_eq_left hmemLow, div_le_one (by positivity)]
          nlinarith [sq_nonneg s.im]
        · rw [ite_eq_right hcond]; split_ifs <;> norm_num only
      _ =
          ((u.filter (fun s => -8 < s.im)).filter
              (fun s => s ∈ lowBand_zeros_finite_neg.toFinset)).card :=
        Finset.sum_boole _ _
      _ ≤ L := by
        rw [hL_def]
        exact_mod_cast Finset.card_le_card (fun s hs => (Finset.mem_filter.mp hs).2)
  have hhigh :
    ∑ s ∈ u.filter (fun s => ¬(-8 < s.im)), nontrivialZetaZeroWeightNeg s ≤ ∑' n, g n := by
    set uh := u.filter (fun s => ¬(-8 < s.im)) with huh_def
    set t : Finset ℕ := uh.image (fun s => ⌊-s.im⌋₊) with ht_def
    have hmaps : ∀ s ∈ uh, ⌊-s.im⌋₊ ∈ t := fun s hs => Finset.mem_image_of_mem _ hs
    have hband :
      ∀ j ∈ t, ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j), nontrivialZetaZeroWeightNeg s ≤ g j := by
      intro j hj
      have hj8 : (8 : ℕ) ≤ j := by
        rw [ht_def, Finset.mem_image] at hj
        obtain ⟨s, hs, hsj⟩ := hj
        rw [huh_def, Finset.mem_filter] at hs
        push Not at hs
        rw [← hsj]
        refine Nat.le_floor ?_
        have h := hs.2
        push_cast
        linarith
      have hj8R : (8 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj8
      obtain ⟨S, m, hmpos, hSD, hSzero, hDzero, hmeq⟩ :=
        exists_jensenBall_zero_ledger_neg (T := -(j : ℝ)) (by linarith)
      have hfilter_sub :
        ∀ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j),
          nontrivialZetaZeroWeightNeg s ≤ (if s ∈ S then (1 : ℝ) / (1 + (j : ℝ) ^ 2) else 0) := by
        intro s hs
        rw [Finset.mem_filter] at hs
        obtain ⟨hsuh, hsfl⟩ := hs
        rw [huh_def, Finset.mem_filter] at hsuh
        push Not at hsuh
        have hsim0 : (0 : ℝ) ≤ -s.im := by linarith [hsuh.2]
        have hfl_le := Nat.floor_le hsim0
        have hfl_lt := Nat.lt_floor_add_one (-s.im)
        rw [hsfl] at hfl_le hfl_lt
        unfold nontrivialZetaZeroWeightNeg
        by_cases hcond : riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0
        · rw [ite_eq_left hcond]
          have him2 : |s.im - (-(j : ℝ))| ≤ 2 := by
            rw [abs_le]; constructor <;> linarith
          have hmemD : s ∈ Metric.closedBall (jensenCenter (-(j : ℝ))) (37 / 10) :=
            riemannZeta_zero_mem_jensenBall_neg (by linarith) hcond.1 him2
          have hmemS : s ∈ S := hDzero s hmemD hcond.1
          rw [ite_eq_left hmemS]
          apply div_le_div_of_nonneg_left (by norm_num only) (by positivity)
          nlinarith
        · rw [ite_eq_right hcond]
          split_ifs <;> positivity
      calc
        ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j), nontrivialZetaZeroWeightNeg s ≤
            ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j),
              (if s ∈ S then (1 : ℝ) / (1 + (j : ℝ) ^ 2) else 0) :=
          Finset.sum_le_sum hfilter_sub
        _ =
            ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j),
              (1 / (1 + (j : ℝ) ^ 2)) * (if s ∈ S then (1 : ℝ) else 0) :=
          by
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : s ∈ S <;> simp only [h, reduceIte, one_div, mul_one, mul_zero]
        _ =
            (1 / (1 + (j : ℝ) ^ 2)) *
              ((uh.filter (fun s => ⌊-s.im⌋₊ = j)).filter (fun s => s ∈ S)).card :=
          by rw [← Finset.mul_sum, Finset.sum_boole]
        _ ≤ (1 / (1 + (j : ℝ) ^ 2)) * (∑ u ∈ S, m u) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (((uh.filter (fun s => ⌊-s.im⌋₊ = j)).filter (fun s => s ∈ S)).card : ℝ) ≤
                (S.card : ℝ) :=
              mod_cast Finset.card_le_card (fun s hs => (Finset.mem_filter.mp hs).2)
            _ ≤ (∑ u ∈ S, m u : ℕ) := by
              have : S.card ≤ ∑ u ∈ S, m u := by
                calc
                  S.card = ∑ _u ∈ S, 1 := (Finset.card_eq_sum_ones S)
                  _ ≤ ∑ u ∈ S, m u := Finset.sum_le_sum (fun u hu => hmpos u hu)
              exact_mod_cast this
        _ ≤ (1 / (1 + (j : ℝ) ^ 2)) * (jensenLogConst * Real.log ((j : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [Nat.cast_sum, neg_neg] using hmeq
        _ = g j := by
          simp only [hg_def]; ring
    calc
      ∑ s ∈ uh, nontrivialZetaZeroWeightNeg s =
          ∑ j ∈ t, ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j), nontrivialZetaZeroWeightNeg s :=
        (Finset.sum_fiberwise_of_maps_to hmaps nontrivialZetaZeroWeightNeg).symm
      _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum hband
      _ ≤ ∑' n, g n := hgsum.sum_le_tsum t (fun n _ => hgnn n)
  linarith [hlow, hhigh]

/-- The full zero-weight summand, with no restriction on the sign of `Im s`. -/
noncomputable def nontrivialZetaZeroWeightFull (s : ℂ) : ℝ :=
  if riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 then 1 / (1 + s.im ^ 2) else 0

/-- The reciprocal-square height weight is summable over all nontrivial zeta
zeros, ignoring multiplicity, by combining the two signs of the imaginary part. -/
theorem summable_nontrivialZetaZeroWeightFull : Summable nontrivialZetaZeroWeightFull := by
  have heq :
    nontrivialZetaZeroWeightFull = fun s =>
      nontrivialZetaZeroWeight s + nontrivialZetaZeroWeightNeg s := by
    funext s
    unfold nontrivialZetaZeroWeightFull nontrivialZetaZeroWeight nontrivialZetaZeroWeightNeg
    by_cases hz : riemannZeta s = 0
    · by_cases hre0 : 0 ≤ s.re
      · by_cases hre1 : s.re ≤ 1
        · rcases lt_or_ge s.im 0 with him | him
          · simp only [hz, hre0, hre1, and_self, ↓reduceIte, one_div, not_le.mpr him, and_false,
              him, zero_add]
          · simp only [hz, hre0, hre1, and_self, ↓reduceIte, one_div, him, not_lt.mpr him,
              and_false, add_zero]
        · simp only [hre1, and_false, ↓reduceIte, false_and, add_zero]
      · simp only [hre0, false_and, and_false, ↓reduceIte, add_zero]
    · simp only [hz, false_and, ↓reduceIte, add_zero]
  rw [heq]
  exact Summable.add summable_nontrivialZetaZeroWeight summable_nontrivialZetaZeroWeightNeg

/-- The positive-height nontrivial zeta-zero series remains summable when each zero is weighted
by its analytic multiplicity. The proof reuses the zeta-side estimate height decomposition and the
multiplicity-aware Jensen-band estimate. -/
theorem summable_nontrivialZetaZeroMultiplicityWeight :
    Summable nontrivialZetaZeroMultiplicityWeight := by
  classical
  set L : ℝ := ∑ s ∈ lowBand_zeros_finite.toFinset, riemannZetaZeroMultiplicity s with hL_def
  set g : ℕ → ℝ := fun n => jensenLogConst * Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2) with hg_def
  have hgsum : Summable g := summable_jensenLogConst_mul_log_div_sq
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    have h1 := jensenLogConst_pos.le
    have h2 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg
        (by
          have := Nat.cast_nonneg (α := ℝ) n; linarith)
    simp only [hg_def]
    positivity
  refine
    summable_of_sum_le nontrivialZetaZeroMultiplicityWeight_nonneg (c := L + ∑' n, g n) fun u => ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun s => s.im < 8)]
  have hlow : ∑ s ∈ u.filter (fun s => s.im < 8), nontrivialZetaZeroMultiplicityWeight s ≤ L := by
    set v :=
      (u.filter (fun s => s.im < 8)).filter
        (fun s => riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im) with
      hv_def
    have hsum_eq :
      ∑ s ∈ u.filter (fun s => s.im < 8), nontrivialZetaZeroMultiplicityWeight s =
        ∑ s ∈ v, nontrivialZetaZeroMultiplicityWeight s := by
      rw [hv_def]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro s hs hnot
      have hcond : ¬(riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im) := by
        intro hcond
        apply hnot
        rw [Finset.mem_filter]
        exact ⟨hs, hcond⟩
      unfold nontrivialZetaZeroMultiplicityWeight
      simp only [hcond, ↓reduceIte]
    calc
      ∑ s ∈ u.filter (fun s => s.im < 8), nontrivialZetaZeroMultiplicityWeight s =
          ∑ s ∈ v, nontrivialZetaZeroMultiplicityWeight s :=
        hsum_eq
      _ ≤ ∑ s ∈ v, (riemannZetaZeroMultiplicity s : ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        unfold nontrivialZetaZeroMultiplicityWeight
        rw [ite_eq_left]
        · apply div_le_self (by positivity)
          nlinarith [sq_nonneg s.im]
        · rw [hv_def, Finset.mem_filter] at hs
          exact hs.2
      _ ≤ ∑ s ∈ lowBand_zeros_finite.toFinset, (riemannZetaZeroMultiplicity s : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          rw [hv_def, Finset.mem_filter] at hs
          obtain ⟨hs, hcond⟩ := hs
          rw [Finset.mem_filter] at hs
          rw [Set.Finite.mem_toFinset]
          exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, hs.2⟩
        · intro s _ _
          positivity
      _ = L := by exact hL_def.symm
  have hhigh :
    ∑ s ∈ u.filter (fun s => ¬s.im < 8), nontrivialZetaZeroMultiplicityWeight s ≤ ∑' n, g n := by
    set uh := u.filter (fun s => ¬s.im < 8) with huh_def
    set t : Finset ℕ := uh.image (fun s => ⌊s.im⌋₊) with ht_def
    have hmaps : ∀ s ∈ uh, ⌊s.im⌋₊ ∈ t := fun s hs => Finset.mem_image_of_mem _ hs
    have hband :
      ∀ j ∈ t,
        ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j), nontrivialZetaZeroMultiplicityWeight s ≤ g j := by
      intro j hj
      have hj8 : (8 : ℕ) ≤ j := by
        rw [ht_def, Finset.mem_image] at hj
        obtain ⟨s, hs, hsj⟩ := hj
        rw [huh_def, Finset.mem_filter] at hs
        push Not at hs
        rw [← hsj]
        exact Nat.le_floor (by exact_mod_cast hs.2)
      set v :=
        (uh.filter (fun s => ⌊s.im⌋₊ = j)).filter
          (fun s => riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im) with
        hv_def
      have hU : ∀ s ∈ v, riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ ⌊s.im⌋₊ = j := by
        intro s hs
        rw [hv_def, Finset.mem_filter] at hs
        obtain ⟨hbase, hcond⟩ := hs
        rw [Finset.mem_filter] at hbase
        obtain ⟨_, hfloor⟩ := hbase
        exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, hfloor⟩
      have hsum_eq :
        ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j), nontrivialZetaZeroMultiplicityWeight s =
          ∑ s ∈ v, nontrivialZetaZeroMultiplicityWeight s := by
        rw [hv_def]
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro s hs hv
        have hcond : ¬(riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im) := by
          intro hcond
          apply hv
          rw [Finset.mem_filter]
          exact ⟨hs, hcond⟩
        unfold nontrivialZetaZeroMultiplicityWeight
        simp only [hcond, ↓reduceIte]
      calc
        ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j), nontrivialZetaZeroMultiplicityWeight s =
            ∑ s ∈ v, (riemannZetaZeroMultiplicity s : ℝ) / (1 + s.im ^ 2) :=
          by
          rw [hsum_eq]
          apply Finset.sum_congr rfl
          intro s hs
          unfold nontrivialZetaZeroMultiplicityWeight
          exact
            ite_eq_left (by exact ⟨(hU s hs).1, (hU s hs).2.1, (hU s hs).2.2.1, (hU s hs).2.2.2.1⟩)
        _ ≤ jensenLogConst * Real.log ((j : ℝ) + 2) / (1 + (j : ℝ) ^ 2) :=
          sum_riemannZetaZeroMultiplicity_div_one_add_im_sq_le_jensenBand hj8 hU
        _ = g j := by simp only [hg_def]
    calc
      ∑ s ∈ uh, nontrivialZetaZeroMultiplicityWeight s =
          ∑ j ∈ t, ∑ s ∈ uh.filter (fun s => ⌊s.im⌋₊ = j), nontrivialZetaZeroMultiplicityWeight s :=
        (Finset.sum_fiberwise_of_maps_to hmaps nontrivialZetaZeroMultiplicityWeight).symm
      _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum hband
      _ ≤ ∑' n, g n := hgsum.sum_le_tsum t (fun n _ => hgnn n)
  linarith [hlow, hhigh]

/-- The negative-height mirror of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.summable_nontrivialZetaZeroMultiplicityWeight`. -/
theorem summable_nontrivialZetaZeroMultiplicityWeightNeg :
    Summable nontrivialZetaZeroMultiplicityWeightNeg := by
  classical
  set L : ℝ := ∑ s ∈ lowBand_zeros_finite_neg.toFinset, riemannZetaZeroMultiplicity s with hL_def
  set g : ℕ → ℝ := fun n => jensenLogConst * Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2) with hg_def
  have hgsum : Summable g := summable_jensenLogConst_mul_log_div_sq
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    have h1 := jensenLogConst_pos.le
    have h2 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg
        (by
          have := Nat.cast_nonneg (α := ℝ) n; linarith)
    simp only [hg_def]
    positivity
  refine
    summable_of_sum_le nontrivialZetaZeroMultiplicityWeightNeg_nonneg (c := L + ∑' n, g n) fun u =>
      ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun s => -8 < s.im)]
  have hlow :
    ∑ s ∈ u.filter (fun s => -8 < s.im), nontrivialZetaZeroMultiplicityWeightNeg s ≤ L := by
    set v :=
      (u.filter (fun s => -8 < s.im)).filter
        (fun s => riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0) with
      hv_def
    have hsum_eq :
      ∑ s ∈ u.filter (fun s => -8 < s.im), nontrivialZetaZeroMultiplicityWeightNeg s =
        ∑ s ∈ v, nontrivialZetaZeroMultiplicityWeightNeg s := by
      rw [hv_def]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro s hs hnot
      have hcond : ¬(riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0) := by
        intro hcond
        apply hnot
        rw [Finset.mem_filter]
        exact ⟨hs, hcond⟩
      unfold nontrivialZetaZeroMultiplicityWeightNeg
      simp only [hcond, ↓reduceIte]
    calc
      ∑ s ∈ u.filter (fun s => -8 < s.im), nontrivialZetaZeroMultiplicityWeightNeg s =
          ∑ s ∈ v, nontrivialZetaZeroMultiplicityWeightNeg s :=
        hsum_eq
      _ ≤ ∑ s ∈ v, (riemannZetaZeroMultiplicity s : ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        unfold nontrivialZetaZeroMultiplicityWeightNeg
        rw [ite_eq_left]
        · apply div_le_self (by positivity)
          nlinarith [sq_nonneg s.im]
        · rw [hv_def, Finset.mem_filter] at hs
          exact hs.2
      _ ≤ ∑ s ∈ lowBand_zeros_finite_neg.toFinset, (riemannZetaZeroMultiplicity s : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          rw [hv_def, Finset.mem_filter] at hs
          obtain ⟨hs, hcond⟩ := hs
          rw [Finset.mem_filter] at hs
          rw [Set.Finite.mem_toFinset]
          exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hs.2, hcond.2.2.2⟩
        · intro s _ _
          positivity
      _ = L := by exact hL_def.symm
  have hhigh :
    ∑ s ∈ u.filter (fun s => ¬(-8 < s.im)), nontrivialZetaZeroMultiplicityWeightNeg s ≤
      ∑' n, g n := by
    set uh := u.filter (fun s => ¬(-8 < s.im)) with huh_def
    set t : Finset ℕ := uh.image (fun s => ⌊-s.im⌋₊) with ht_def
    have hmaps : ∀ s ∈ uh, ⌊-s.im⌋₊ ∈ t := fun s hs => Finset.mem_image_of_mem _ hs
    have hband :
      ∀ j ∈ t,
        ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j), nontrivialZetaZeroMultiplicityWeightNeg s ≤
          g j := by
      intro j hj
      have hj8 : (8 : ℕ) ≤ j := by
        rw [ht_def, Finset.mem_image] at hj
        obtain ⟨s, hs, hsj⟩ := hj
        rw [huh_def, Finset.mem_filter] at hs
        push Not at hs
        rw [← hsj]
        refine Nat.le_floor ?_
        have h := hs.2
        push_cast
        linarith
      set v :=
        (uh.filter (fun s => ⌊-s.im⌋₊ = j)).filter
          (fun s => riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0) with
        hv_def
      have hU : ∀ s ∈ v, riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0 ∧ ⌊-s.im⌋₊ = j := by
        intro s hs
        rw [hv_def, Finset.mem_filter] at hs
        obtain ⟨hbase, hcond⟩ := hs
        rw [Finset.mem_filter] at hbase
        obtain ⟨_, hfloor⟩ := hbase
        exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, hfloor⟩
      have hsum_eq :
        ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j), nontrivialZetaZeroMultiplicityWeightNeg s =
          ∑ s ∈ v, nontrivialZetaZeroMultiplicityWeightNeg s := by
        rw [hv_def]
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro s hs hv
        have hcond : ¬(riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im < 0) := by
          intro hcond
          apply hv
          rw [Finset.mem_filter]
          exact ⟨hs, hcond⟩
        unfold nontrivialZetaZeroMultiplicityWeightNeg
        simp only [hcond, ↓reduceIte]
      calc
        ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j), nontrivialZetaZeroMultiplicityWeightNeg s =
            ∑ s ∈ v, (riemannZetaZeroMultiplicity s : ℝ) / (1 + s.im ^ 2) :=
          by
          rw [hsum_eq]
          apply Finset.sum_congr rfl
          intro s hs
          unfold nontrivialZetaZeroMultiplicityWeightNeg
          exact
            ite_eq_left (by exact ⟨(hU s hs).1, (hU s hs).2.1, (hU s hs).2.2.1, (hU s hs).2.2.2.1⟩)
        _ ≤ jensenLogConst * Real.log ((j : ℝ) + 2) / (1 + (j : ℝ) ^ 2) :=
          sum_riemannZetaZeroMultiplicity_div_one_add_im_sq_le_jensenBand_neg hj8 hU
        _ = g j := by simp only [hg_def]
    calc
      ∑ s ∈ uh, nontrivialZetaZeroMultiplicityWeightNeg s =
          ∑ j ∈ t,
            ∑ s ∈ uh.filter (fun s => ⌊-s.im⌋₊ = j), nontrivialZetaZeroMultiplicityWeightNeg s :=
        (Finset.sum_fiberwise_of_maps_to hmaps nontrivialZetaZeroMultiplicityWeightNeg).symm
      _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum hband
      _ ≤ ∑' n, g n := hgsum.sum_le_tsum t (fun n _ => hgnn n)
  linarith [hlow, hhigh]

/-- The multiplicity-weighted reciprocal-square summand over all nontrivial zeta zeros. -/
noncomputable def nontrivialZetaZeroMultiplicityWeightFull (s : ℂ) : ℝ :=
  if riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 then riemannZetaZeroMultiplicity s / (1 + s.im ^ 2)
  else 0

/-- The full multiplicity-weighted zeta zero series is summable. This supplies the zero-series
input required to pass from finite xi Hadamard products to an infinite product. -/
theorem summable_nontrivialZetaZeroMultiplicityWeightFull :
    Summable nontrivialZetaZeroMultiplicityWeightFull := by
  have heq :
    nontrivialZetaZeroMultiplicityWeightFull = fun s =>
      nontrivialZetaZeroMultiplicityWeight s + nontrivialZetaZeroMultiplicityWeightNeg s := by
    funext s
    unfold nontrivialZetaZeroMultiplicityWeightFull nontrivialZetaZeroMultiplicityWeight
      nontrivialZetaZeroMultiplicityWeightNeg
    by_cases hz : riemannZeta s = 0
    · by_cases hre0 : 0 ≤ s.re
      · by_cases hre1 : s.re ≤ 1
        · by_cases him : 0 ≤ s.im
          · simp only [hz, hre0, hre1, and_self, ↓reduceIte, him, not_lt.mpr him, and_false,
              add_zero]
          · have himneg : s.im < 0 := lt_of_not_ge him
            simp only [hz, hre0, hre1, and_self, ↓reduceIte, him, and_false, himneg, zero_add]
        · simp only [hre1, and_false, ↓reduceIte, false_and, add_zero]
      · simp only [hre0, false_and, and_false, ↓reduceIte, add_zero]
    · simp only [hz, false_and, ↓reduceIte, add_zero]
  rw [heq]
  exact
    Summable.add summable_nontrivialZetaZeroMultiplicityWeight
      summable_nontrivialZetaZeroMultiplicityWeightNeg

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
