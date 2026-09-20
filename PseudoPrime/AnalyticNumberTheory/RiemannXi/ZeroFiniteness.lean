/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannXi.Basic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroSummability
import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.AnalyticNumberTheory.General.FinsetNeighborhood

/-!
# Xi zeros in compact sets

Xi is entire and nonzero at zero, so the identity theorem makes its zeros
discrete and their complement codiscrete. Compact sets therefore contain only
finitely many zeros. Finite zero ledgers, multiplicity weights, and local
Hadamard quotients support finite-radius logarithmic-derivative estimates.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- A zeta zero with nonnegative real part is also a zero of
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`.  Kept in the xi-zero
layer so low-level trivial-zero bookkeeping need not depend on xi machinery. -/
theorem riemannXi_eq_zero_of_riemannZeta_zero_re_nonneg {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) : riemannXi ρ = 0 := by
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h] at hz
    exact riemannZeta_one_ne_zero hz
  have hnt : ∀ n : ℕ, ρ ≠ -2 * ((n : ℂ) + 1) := by
    intro n h
    have hn' : ρ = ((-(2 * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    rw [hn', Complex.ofReal_re] at hre
    nlinarith only [hre, Nat.cast_nonneg (α := ℝ) n]
  exact (riemannXi_eq_zero_iff_of_denom_ne_zero hne1 (riemannZetaDenom_ne_zero hnt)).mpr hz

/-- `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi` is not the zero function
(`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi 0 = 1/2 ≠ 0`). -/
theorem riemannXi_ne_zero_fun : ¬Set.EqOn riemannXi 0 Set.univ := by
  intro h
  have := h (Set.mem_univ (0 : ℂ))
  rw [riemannXi_zero] at this
  simp only [Pi.zero_apply] at this
  norm_num only at this

/-- Xi is nonzero on a codiscrete set: its zero set is discrete.
The identity theorem applies because xi is entire and not identically zero. -/
theorem riemannXi_eventually_ne_zero :
    ∀ᶠ x in Filter.codiscreteWithin Set.univ, riemannXi x ≠ 0 := by
  have hanalytic : AnalyticOnNhd ℂ riemannXi Set.univ := fun z _ =>
    differentiable_riemannXi.analyticAt z
  rcases hanalytic.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with heq |
    hev
  · exact absurd heq riemannXi_ne_zero_fun
  · exact hev

/-- **The zeros of `riemannXi` inside any closed ball form a finite set.** -/
theorem riemannXi_zeros_inter_closedBall_finite (R : ℝ) :
    (riemannXi ⁻¹' {0} ∩ Metric.closedBall (0 : ℂ) R).Finite := by
  have hmem : {x : ℂ | riemannXi x ≠ 0} ∈ Filter.codiscreteWithin (Metric.closedBall (0 : ℂ) R) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) riemannXi_eventually_ne_zero
  have hfin := (isCompact_closedBall (0 : ℂ) R).finite_sdiff_of_mem_codiscreteWithin hmem
  have heq :
    Metric.closedBall (0 : ℂ) R \ {x : ℂ | riemannXi x ≠ 0} =
      riemannXi ⁻¹' {0} ∩ Metric.closedBall (0 : ℂ) R := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_not, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    tauto
  rwa [heq] at hfin

/-- The finite zero ledger of `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`
in the closed ball of radius `R` about zero.

This is the finite index set for the radius-`R` factors in the later Hadamard quotient. -/
noncomputable def riemannXiZerosInClosedBall (R : ℝ) : Finset ℂ :=
  (riemannXi_zeros_inter_closedBall_finite R).toFinset

/-- Membership in the radius-`R` xi-zero ledger has its direct analytic meaning. -/
theorem mem_riemannXiZerosInClosedBall_iff {R : ℝ} {ρ : ℂ} :
    ρ ∈ riemannXiZerosInClosedBall R ↔ riemannXi ρ = 0 ∧ ρ ∈ Metric.closedBall (0 : ℂ) R := by
  rw [riemannXiZerosInClosedBall, Set.Finite.mem_toFinset]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]

/-- Every entry of the finite xi-zero ledger is a zero in its defining closed ball. -/
theorem riemannXi_zero_mem_closedBall_of_mem_ledger {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) : riemannXi ρ = 0 ∧ ρ ∈ Metric.closedBall (0 : ℂ) R :=
  mem_riemannXiZerosInClosedBall_iff.mp hρ

/-- Increasing the radius only enlarges the finite xi-zero ledger. -/
theorem riemannXiZerosInClosedBall_mono {R S : ℝ} (hRS : R ≤ S) :
    riemannXiZerosInClosedBall R ⊆ riemannXiZerosInClosedBall S := by
  intro ρ hρ
  obtain ⟨hzero, hball⟩ := mem_riemannXiZerosInClosedBall_iff.mp hρ
  apply mem_riemannXiZerosInClosedBall_iff.mpr
  exact ⟨hzero, Metric.closedBall_subset_closedBall hRS hball⟩

/-- No xi-zero in a finite radius ledger is the origin, since `ξ(0)=1/2`. -/
theorem riemannXiZero_ne_zero_of_mem_ledger {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) : ρ ≠ 0 := by
  intro hρ0
  obtain ⟨hzero, _⟩ := riemannXi_zero_mem_closedBall_of_mem_ledger hρ
  rw [hρ0, riemannXi_zero] at hzero
  norm_num only at hzero

/-- A zero of `ξ` cannot lie to the left of the critical strip. This turns the zero-free
left half-plane for `ξ` into the lower real-part bound used in zero ledgers. -/
theorem riemannXi_zero_re_nonneg {s : ℂ} (hs : riemannXi s = 0) : 0 ≤ s.re := by
  by_contra hneg
  exact riemannXi_ne_zero_of_re_neg (lt_of_not_ge hneg) hs

/-- A zero of `ξ` cannot lie to the right of the critical strip. -/
theorem riemannXi_zero_re_le_one {s : ℂ} (hs : riemannXi s = 0) : s.re ≤ 1 := by
  by_contra hgt
  exact riemannXi_ne_zero_of_one_lt_re (lt_of_not_ge hgt) hs

/-- Every xi-zero is a nontrivial zeta-zero. The strip bounds exclude the Gamma-denominator's
trivial-zero locations, while `ξ(1)=1/2` excludes the pole at one. -/
theorem riemannZeta_zero_of_riemannXi_zero {s : ℂ} (hs : riemannXi s = 0) : riemannZeta s = 0 := by
  have hre : 0 ≤ s.re := riemannXi_zero_re_nonneg hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, riemannXi_one] at hs
    norm_num only at hs
  have hnt : ∀ n : ℕ, s ≠ -2 * (n + 1) := by
    intro n h
    rw [h] at hre
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, Complex.natCast_re, Complex.natCast_im] at hre
    nlinarith only [hre, Nat.cast_nonneg (α := ℝ) n]
  exact (riemannXi_eq_zero_iff_of_denom_ne_zero hs1 (riemannZetaDenom_ne_zero hnt)).mp hs

/--
Riemann's hypothesis places every zero of the completed xi function on the critical line.

Input/assumptions: `hRH` is mathlib's Riemann hypothesis and `hs` is a xi-zero.
Conclusion: the real part of the zero is `1 / 2`.
Content: a xi-zero is first converted to a nontrivial zeta-zero; its nonnegative real part rules
out all negative even trivial-zero locations, while `ξ(1) = 1/2` rules out the zeta pole.
Role: this is the RH specialization used when finite xi ledgers are converted to critical-line
zero sums in the xi-side result.
-/
theorem riemannXi_zero_re_eq_half_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : riemannXi s = 0) : s.re = (1 : ℝ) / 2 := by
  apply hRH s (riemannZeta_zero_of_riemannXi_zero hs)
  · intro htrivial
    obtain ⟨n, hn⟩ := htrivial
    have hre : 0 ≤ s.re := riemannXi_zero_re_nonneg hs
    rw [hn] at hre
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, Complex.natCast_re, Complex.natCast_im] at hre
    nlinarith only [hre, Nat.cast_nonneg (α := ℝ) n]
  · intro hsone
    rw [hsone, riemannXi_one] at hs
    norm_num only at hs

/--
Riemann's hypothesis places every entry of a finite xi-zero ledger on the critical line.

Input/assumptions: `hRH` is Riemann's hypothesis and `hρ` is membership in the radius-`R` ledger.
Conclusion: `ρ.re = 1 / 2`.
Content: extract the xi-zero assertion from the ledger and apply the global critical-line theorem.
Role: this is the finite-ledger form consumed by radius-by-radius Hadamard and zero-sum estimates.
-/
theorem riemannXiZero_re_eq_half_of_mem_ledger (hRH : RiemannHypothesis) {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) : ρ.re = (1 : ℝ) / 2 := by
  exact
    riemannXi_zero_re_eq_half_of_riemannHypothesis hRH
      (riemannXi_zero_mem_closedBall_of_mem_ledger hρ).1

/--
On RH, the squared norm of a xi-zero is its critical-line normal form.

Input/assumptions: `hRH` is Riemann's hypothesis and `hs` is a xi-zero.
Conclusion: `‖s‖² = 1/4 + (Im s)²`.
Content: expand `Complex.normSq` and substitute the critical-line equality for the real part.
Role: it converts radial Hadamard weights into the one-dimensional zero weights used by downstream
  modules.
-/
theorem norm_sq_riemannXi_zero_eq_quarter_add_im_sq_of_riemannHypothesis (hRH : RiemannHypothesis)
    {s : ℂ} (hs : riemannXi s = 0) : ‖s‖ ^ 2 = (1 : ℝ) / 4 + s.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    riemannXi_zero_re_eq_half_of_riemannHypothesis hRH hs]
  ring

/-- Each entry of a finite xi-zero ledger is a zeta-zero in the critical strip. -/
theorem riemannZeta_zero_re_mem_of_mem_riemannXi_ledger {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  have hzero : riemannXi ρ = 0 := (riemannXi_zero_mem_closedBall_of_mem_ledger hρ).1
  exact
    ⟨riemannZeta_zero_of_riemannXi_zero hzero, riemannXi_zero_re_nonneg hzero,
      riemannXi_zero_re_le_one hzero⟩

/-- The multiplicity-free reciprocal-square weight of a xi-zero. This is the zero-set
summability input for the genus-one product; upgrading it to analytic multiplicities remains
separate. -/
noncomputable def riemannXiZeroWeight (s : ℂ) : ℝ :=
  if riemannXi s = 0 then 1 / (1 + s.im ^ 2) else 0

/-- The xi-zero weight is nonnegative. -/
theorem riemannXiZeroWeight_nonneg (s : ℂ) : 0 ≤ riemannXiZeroWeight s := by
  unfold riemannXiZeroWeight
  split <;> positivity

/-- The xi-zero weight is pointwise bounded by the already summable nontrivial-zeta-zero weight.
The zero-set correspondence and critical-strip bounds established above provide the comparison. -/
theorem riemannXiZeroWeight_le_nontrivialZetaZeroWeightFull (s : ℂ) :
    riemannXiZeroWeight s ≤ RiemannZeta.nontrivialZetaZeroWeightFull s := by
  unfold riemannXiZeroWeight RiemannZeta.nontrivialZetaZeroWeightFull
  by_cases hs : riemannXi s = 0
  · rw [ite_eq_left hs]
    rw [ite_eq_left
        ⟨riemannZeta_zero_of_riemannXi_zero hs, riemannXi_zero_re_nonneg hs,
          riemannXi_zero_re_le_one hs⟩]
  · rw [ite_eq_right hs]
    positivity

/-- The reciprocal-square weights of all xi-zeros are summable, without multiplicity.
This supplies the convergence datum needed before the multiplicity-weighted Hadamard product is
passed to an infinite-radius limit. -/
theorem summable_riemannXiZeroWeight : Summable riemannXiZeroWeight := by
  exact
    Summable.of_nonneg_of_le riemannXiZeroWeight_nonneg
      riemannXiZeroWeight_le_nontrivialZetaZeroWeightFull
      RiemannZeta.summable_nontrivialZetaZeroWeightFull

/-- The norm-based reciprocal-square weight of a xi-zero, regularized at the origin.
This is the radial form naturally used by the genus-one Hadamard factors. -/
noncomputable def riemannXiZeroNormWeight (s : ℂ) : ℝ :=
  if riemannXi s = 0 then 1 / (1 + ‖s‖ ^ 2) else 0

/-- The radial xi-zero weight is bounded by the imaginary-part weight. -/
theorem riemannXiZeroNormWeight_le_riemannXiZeroWeight (s : ℂ) :
    riemannXiZeroNormWeight s ≤ riemannXiZeroWeight s := by
  unfold riemannXiZeroNormWeight riemannXiZeroWeight
  by_cases hs : riemannXi s = 0
  · rw [ite_eq_left hs, ite_eq_left hs]
    apply one_div_le_one_div_of_le
    · positivity
    · rw [← Complex.normSq_eq_norm_sq]
      nlinarith [Complex.im_sq_le_normSq s]
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- The analytic order of `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`
is finite at every complex point.

An infinite order would make the entire function vanish on a neighborhood; the analytic identity
principle would then contradict `ξ(0)=1/2`. -/
theorem riemannXi_analyticOrderAt_ne_top (s : ℂ) : analyticOrderAt riemannXi s ≠ ⊤ := by
  intro htop
  have hlocal : ∀ᶠ z in nhds s, riemannXi z = 0 := analyticOrderAt_eq_top.mp htop
  have hanalytic : AnalyticOnNhd ℂ riemannXi Set.univ := fun z _ =>
    differentiable_riemannXi.analyticAt z
  have hzero :=
    hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s)
      hlocal
  exact riemannXi_ne_zero_fun (fun z _ => hzero (Set.mem_univ z))

/-- The multiplicity of a xi-zero, represented by mathlib's finite analytic order. -/
noncomputable def riemannXiZeroMultiplicity (ρ : ℂ) : ℕ :=
  analyticOrderNatAt riemannXi ρ

/-- For `Re ρ ≥ 0` and `ρ ≠ 1`, xi and zeta have equal analytic multiplicities. -/
theorem riemannXiZeroMultiplicity_eq_riemannZetaZeroMultiplicity {ρ : ℂ} (hre : 0 ≤ ρ.re)
    (hρ1 : ρ ≠ 1) (hnt : ∀ n : ℕ, ρ ≠ -2 * (n + 1)) :
    riemannXiZeroMultiplicity ρ = RiemannZeta.riemannZetaZeroMultiplicity ρ := by
  unfold riemannXiZeroMultiplicity RiemannZeta.riemannZetaZeroMultiplicity analyticOrderNatAt
  rw [analyticOrderAt_riemannXi_eq_riemannZeta hre hρ1 hnt]

/-- Every xi-zero is nontrivial and therefore has the same analytic multiplicity as the
corresponding zeta-zero. -/
theorem riemannXiZeroMultiplicity_eq_riemannZetaZeroMultiplicity_of_zero {ρ : ℂ}
    (hρ : riemannXi ρ = 0) :
    riemannXiZeroMultiplicity ρ = RiemannZeta.riemannZetaZeroMultiplicity ρ := by
  have hre : 0 ≤ ρ.re := riemannXi_zero_re_nonneg hρ
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, riemannXi_one] at hρ
    norm_num only at hρ
  apply riemannXiZeroMultiplicity_eq_riemannZetaZeroMultiplicity hre hρ1
  intro n h
  rw [h] at hre
  simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.neg_im, Complex.im_ofNat, Complex.natCast_re, Complex.natCast_im] at hre
  nlinarith only [hre, Nat.cast_nonneg (α := ℝ) n]

/-- The imaginary-direction reciprocal-square xi-zero weight with analytic multiplicity. -/
noncomputable def riemannXiZeroMultiplicityWeight (s : ℂ) : ℝ :=
  if riemannXi s = 0 then riemannXiZeroMultiplicity s / (1 + s.im ^ 2) else 0

/-- The xi multiplicity weight is pointwise bounded by the completed zeta multiplicity weight. -/
theorem riemannXiZeroMultiplicityWeight_le_nontrivialZetaZeroMultiplicityWeightFull (s : ℂ) :
    riemannXiZeroMultiplicityWeight s ≤ RiemannZeta.nontrivialZetaZeroMultiplicityWeightFull s := by
  unfold riemannXiZeroMultiplicityWeight RiemannZeta.nontrivialZetaZeroMultiplicityWeightFull
  by_cases hs : riemannXi s = 0
  · rw [ite_eq_left hs]
    have hzeta : riemannZeta s = 0 := riemannZeta_zero_of_riemannXi_zero hs
    have hre : 0 ≤ s.re := riemannXi_zero_re_nonneg hs
    have hre1 : s.re ≤ 1 := riemannXi_zero_re_le_one hs
    rw [ite_eq_left ⟨hzeta, hre, hre1⟩]
    rw [riemannXiZeroMultiplicity_eq_riemannZetaZeroMultiplicity_of_zero hs]
  · rw [ite_eq_right hs]
    positivity

/-- The analytic-multiplicity reciprocal-square series over all xi-zeros is summable. -/
theorem summable_riemannXiZeroMultiplicityWeight : Summable riemannXiZeroMultiplicityWeight := by
  exact
    Summable.of_nonneg_of_le
      (fun s => by
        unfold riemannXiZeroMultiplicityWeight
        split <;> positivity)
      riemannXiZeroMultiplicityWeight_le_nontrivialZetaZeroMultiplicityWeightFull
      RiemannZeta.summable_nontrivialZetaZeroMultiplicityWeightFull

/-- The radial reciprocal-square xi-zero weight with analytic multiplicity, regularized at the
origin for use by genus-one Hadamard factors. -/
noncomputable def riemannXiZeroMultiplicityNormWeight (s : ℂ) : ℝ :=
  if riemannXi s = 0 then riemannXiZeroMultiplicity s / (1 + ‖s‖ ^ 2) else 0

/--
On RH, the radial multiplicity weight of a xi-zero has a one-dimensional critical-line form.

Input/assumptions: `hRH` is Riemann's hypothesis and `hs` is a xi-zero.
Conclusion: the radial denominator is `5/4 + (Im s)²`.
Content: substitute the critical-line squared-norm identity into the multiplicity weight.
Role: it is the per-zero normalization for comparing finite Hadamard sums with downstream zero
  masses.
-/
theorem riemannXiZeroMultiplicityNormWeight_eq_criticalLine_of_riemannHypothesis
    (hRH : RiemannHypothesis) {s : ℂ} (hs : riemannXi s = 0) :
    riemannXiZeroMultiplicityNormWeight s =
      riemannXiZeroMultiplicity s / ((5 : ℝ) / 4 + s.im ^ 2) := by
  unfold riemannXiZeroMultiplicityNormWeight
  rw [ite_eq_left hs, norm_sq_riemannXi_zero_eq_quarter_add_im_sq_of_riemannHypothesis hRH hs]
  ring_nf

/--
On RH, the radial xi-zero multiplicity weight loses at most the factor `4/5` versus the
imaginary-direction weight.

Input/assumptions: `hRH` is Riemann's hypothesis and `hs` is a xi-zero.
Conclusion: `4/5` times the imaginary-direction weight is bounded by the radial weight.
Content: on the critical line, `1 + ‖s‖² = 5/4 + (Im s)² ≤ (5/4)(1 + (Im s)²)`.
Role: together with the existing opposite inequality, this gives a uniform comparison between
the radial Hadamard series and downstream zero-weight series.
-/
theorem four_fifths_mul_riemannXiZeroMultiplicityWeight_le_normWeight_of_riemannHypothesis
    (hRH : RiemannHypothesis) {s : ℂ} (hs : riemannXi s = 0) :
    (4 / 5 : ℝ) * riemannXiZeroMultiplicityWeight s ≤ riemannXiZeroMultiplicityNormWeight s := by
  rw [show riemannXiZeroMultiplicityWeight s = riemannXiZeroMultiplicity s / (1 + s.im ^ 2)
      by
      unfold riemannXiZeroMultiplicityWeight
      rw [ite_eq_left hs],
    riemannXiZeroMultiplicityNormWeight_eq_criticalLine_of_riemannHypothesis hRH hs]
  have himsq : 0 ≤ s.im ^ 2 := sq_nonneg s.im
  have hdenom : 0 < 1 + s.im ^ 2 := by positivity
  have hcompare : (5 : ℝ) / 4 + s.im ^ 2 ≤ (5 / 4 : ℝ) * (1 + s.im ^ 2) := by nlinarith only [himsq]
  have hinv : 1 / ((5 / 4 : ℝ) * (1 + s.im ^ 2)) ≤ 1 / ((5 : ℝ) / 4 + s.im ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hcompare
  have hmult : 0 ≤ (riemannXiZeroMultiplicity s : ℝ) := by positivity
  calc
    (4 / 5 : ℝ) * (riemannXiZeroMultiplicity s / (1 + s.im ^ 2)) =
        (riemannXiZeroMultiplicity s : ℝ) * (1 / ((5 / 4 : ℝ) * (1 + s.im ^ 2))) :=
      by field_simp [hdenom.ne']
    _ ≤ (riemannXiZeroMultiplicity s : ℝ) * (1 / ((5 : ℝ) / 4 + s.im ^ 2)) :=
      mul_le_mul_of_nonneg_left hinv hmult
    _ = riemannXiZeroMultiplicity s / ((5 : ℝ) / 4 + s.im ^ 2) := by ring

/--
The `4/5` radial-weight comparison on a finite xi-zero ledger under GRH.

Input/assumptions: `hGRH` is GRH and `hρ` is membership in a finite radius ledger.
Conclusion: the ledger entry satisfies the uniform `4/5` comparison of zero weights.
Content: extract the xi-zero equation and use `hGRH.riemann`.
Role: this is the finite-sum-ready form of the radial-versus-vertical comparison.
-/
theorem four_fifths_mul_riemannXiZeroMultiplicityWeight_le_normWeight_of_mem_ledger
    (hGRH : GRH.GeneralizedRiemannHypothesis) {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    (4 / 5 : ℝ) * riemannXiZeroMultiplicityWeight ρ ≤ riemannXiZeroMultiplicityNormWeight ρ :=
  four_fifths_mul_riemannXiZeroMultiplicityWeight_le_normWeight_of_riemannHypothesis hGRH.riemann
    (riemannXi_zero_mem_closedBall_of_mem_ledger hρ).1

/-- The radial multiplicity weight is bounded by the imaginary-direction multiplicity weight. -/
theorem riemannXiZeroMultiplicityNormWeight_le_riemannXiZeroMultiplicityWeight (s : ℂ) :
    riemannXiZeroMultiplicityNormWeight s ≤ riemannXiZeroMultiplicityWeight s := by
  unfold riemannXiZeroMultiplicityNormWeight riemannXiZeroMultiplicityWeight
  by_cases hs : riemannXi s = 0
  · rw [ite_eq_left hs, ite_eq_left hs]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith [Complex.im_sq_le_normSq s]
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- The finite radial xi-zero multiplicity mass is monotone as the ledger radius grows. -/
theorem sum_riemannXiZeroMultiplicityNormWeight_mono {R S : ℝ} (hRS : R ≤ S) :
    ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicityNormWeight ρ ≤
      ∑ ρ ∈ riemannXiZerosInClosedBall S, riemannXiZeroMultiplicityNormWeight ρ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (riemannXiZerosInClosedBall_mono hRS)
  intro ρ _ _
  unfold riemannXiZeroMultiplicityNormWeight
  split <;> positivity

/-- The finite imaginary-direction xi-zero multiplicity mass is monotone as the ledger radius
grows. -/
theorem sum_riemannXiZeroMultiplicityWeight_mono {R S : ℝ} (hRS : R ≤ S) :
    ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicityWeight ρ ≤
      ∑ ρ ∈ riemannXiZerosInClosedBall S, riemannXiZeroMultiplicityWeight ρ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (riemannXiZerosInClosedBall_mono hRS)
  intro ρ _ _
  unfold riemannXiZeroMultiplicityWeight
  split <;> positivity

/-- The radial analytic-multiplicity reciprocal-square series over all xi-zeros is summable. -/
theorem summable_riemannXiZeroMultiplicityNormWeight :
    Summable riemannXiZeroMultiplicityNormWeight := by
  exact
    Summable.of_nonneg_of_le
      (fun s => by
        unfold riemannXiZeroMultiplicityNormWeight
        split <;> positivity)
      riemannXiZeroMultiplicityNormWeight_le_riemannXiZeroMultiplicityWeight
      summable_riemannXiZeroMultiplicityWeight

/--
Input: a radius `R`.
Conclusion: the radial multiplicity mass of its finite xi-zero ledger is bounded by the
kernel-checked global `tsum` of the same nonnegative weight.
Content: `Summable.sum_le_tsum` turns the finite ledger into a uniformly bounded family.
Role: together with monotonicity, this is the order-theoretic interface required to pass from
finite Hadamard products to a limiting zero contribution.
-/
theorem sum_riemannXiZeroMultiplicityNormWeight_le_tsum (R : ℝ) :
    ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicityNormWeight ρ ≤
      ∑' ρ : ℂ, riemannXiZeroMultiplicityNormWeight ρ := by
  apply summable_riemannXiZeroMultiplicityNormWeight.sum_le_tsum
  intro ρ _
  unfold riemannXiZeroMultiplicityNormWeight
  split <;> positivity

/--
Input: a radius `R`.
Conclusion: the imaginary-direction multiplicity mass of its finite xi-zero ledger is bounded
by the kernel-checked global `tsum` of that weight.
Content: the same finite-to-global summability comparison is applied to the vertical weight.
Role: this supplies the uniform bound needed when finite contour zero sums are enlarged.
-/
theorem sum_riemannXiZeroMultiplicityWeight_le_tsum (R : ℝ) :
    ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicityWeight ρ ≤
      ∑' ρ : ℂ, riemannXiZeroMultiplicityWeight ρ := by
  apply summable_riemannXiZeroMultiplicityWeight.sum_le_tsum
  intro ρ _
  unfold riemannXiZeroMultiplicityWeight
  split <;> positivity

/--
Conclusion: the radial finite-ledger mass family is bounded above.
Content: its global summable zero series is an explicit common upper bound.
Role: combined with `sum_riemannXiZeroMultiplicityNormWeight_mono`, this packages the finite
Hadamard ledgers as a bounded monotone family for the later radius-limit argument.
-/
theorem bddAbove_range_sum_riemannXiZeroMultiplicityNormWeight :
    BddAbove
      (Set.range fun R : ℝ =>
        ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicityNormWeight ρ) := by
  refine ⟨∑' ρ : ℂ, riemannXiZeroMultiplicityNormWeight ρ, ?_⟩
  rintro _ ⟨R, rfl⟩
  exact sum_riemannXiZeroMultiplicityNormWeight_le_tsum R

/--
Conclusion: the imaginary-direction finite-ledger mass family is bounded above.
Content: its global summable zero series is a common upper bound.
Role: this is the boundedness half of the finite-contour zero-mass limit interface.
-/
theorem bddAbove_range_sum_riemannXiZeroMultiplicityWeight :
    BddAbove
      (Set.range fun R : ℝ =>
        ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicityWeight ρ) := by
  refine ⟨∑' ρ : ℂ, riemannXiZeroMultiplicityWeight ρ, ?_⟩
  rintro _ ⟨R, rfl⟩
  exact sum_riemannXiZeroMultiplicityWeight_le_tsum R

/-- Every entry of a finite xi-zero ledger has strictly positive multiplicity. -/
theorem riemannXiZeroMultiplicity_pos_of_mem_ledger {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) : 0 < riemannXiZeroMultiplicity ρ := by
  unfold riemannXiZeroMultiplicity
  apply Nat.pos_of_ne_zero
  intro hnat
  have hzero : riemannXi ρ = 0 := (riemannXi_zero_mem_closedBall_of_mem_ledger hρ).1
  have horder : analyticOrderAt riemannXi ρ ≠ 0 :=
    (differentiable_riemannXi.analyticAt ρ).analyticOrderAt_ne_zero.mpr hzero
  apply horder
  rw [← Nat.cast_analyticOrderNatAt (riemannXi_analyticOrderAt_ne_top ρ), hnat]
  rfl

/-- The genus-one factor attached to one nonzero zero of
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`.

For a zero `ρ`, this is `(1 - s / ρ) exp(s / ρ)`, the factor used by the
genus-one Hadamard product. -/
noncomputable def riemannXiHadamardFactor (s ρ : ℂ) : ℂ :=
  (1 - s / ρ) * Complex.exp (s / ρ)

/-- Each genus-one factor is entire as a function of its first argument. -/
theorem differentiable_riemannXiHadamardFactor (ρ : ℂ) :
    Differentiable ℂ (fun s => riemannXiHadamardFactor s ρ) := by
  intro s
  unfold riemannXiHadamardFactor
  fun_prop

/-- The derivative of a genus-one factor has the cancellation expected from its exponential.

The formula is valid at `ρ = 0` as well under Lean's totalized division; ledger applications use
the preceding nonvanishing lemma to exclude that case. -/
theorem deriv_riemannXiHadamardFactor (s ρ : ℂ) :
    deriv (fun z => riemannXiHadamardFactor z ρ) s = -(s / ρ ^ 2) * Complex.exp (s / ρ) := by
  have hdiv : HasDerivAt (fun z : ℂ => z / ρ) (1 / ρ) s := (hasDerivAt_id s).div_const ρ
  have hlinear : HasDerivAt (fun z : ℂ => 1 - z / ρ) (-(1 / ρ)) s := hdiv.const_sub 1
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (z / ρ)) (Complex.exp (s / ρ) * (1 / ρ)) s :=
    (Complex.hasDerivAt_exp (s / ρ)).comp s hdiv
  unfold riemannXiHadamardFactor
  change deriv ((fun z : ℂ => 1 - z / ρ) * fun z => Complex.exp (z / ρ)) s = _
  rw [hlinear.mul hexp |>.deriv]
  simp only [div_eq_mul_inv, pow_two]
  ring

/-- A genus-one factor is nonzero away from its nonzero attached zero. -/
theorem riemannXiHadamardFactor_ne_zero {s ρ : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    riemannXiHadamardFactor s ρ ≠ 0 := by
  unfold riemannXiHadamardFactor
  apply mul_ne_zero
  · intro hlinear
    apply hs
    have hdiv : s / ρ = 1 := sub_eq_zero.mp hlinear |>.symm
    have hmul : s = 1 * ρ := (div_eq_iff hρ).mp hdiv
    simpa only [one_mul] using hmul
  · exact Complex.exp_ne_zero _

/-- For a nonzero attached zero, a genus-one factor vanishes exactly at that zero. -/
theorem riemannXiHadamardFactor_eq_zero_iff {s ρ : ℂ} (hρ : ρ ≠ 0) :
    riemannXiHadamardFactor s ρ = 0 ↔ s = ρ := by
  constructor
  · intro hfactor
    by_contra hs
    exact riemannXiHadamardFactor_ne_zero hρ hs hfactor
  · intro hs
    subst s
    simp only [riemannXiHadamardFactor]
    simp only [ne_eq, hρ, not_false_eq_true, div_self, sub_self, zero_mul]

/-- Away from its attached zero, the logarithmic derivative of a genus-one factor is
`1 / (s - ρ) + 1 / ρ`. -/
theorem logDeriv_riemannXiHadamardFactor {s ρ : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    logDeriv (fun z => riemannXiHadamardFactor z ρ) s = 1 / (s - ρ) + 1 / ρ := by
  rw [logDeriv_apply, deriv_riemannXiHadamardFactor]
  unfold riemannXiHadamardFactor
  have hlinear : 1 - s / ρ ≠ 0 := by
    intro h
    apply hs
    have hdiv : s / ρ = 1 := sub_eq_zero.mp h |>.symm
    simpa only [one_mul] using (div_eq_iff hρ).mp hdiv
  field_simp
  ring

/-- The finite genus-one Hadamard product over xi-zeros in the radius-`R` ledger. -/
noncomputable def riemannXiFiniteHadamardProduct (R : ℝ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ riemannXiZerosInClosedBall R, riemannXiHadamardFactor s ρ

/-- The multiplicity-aware finite factor for a xi-zero. -/
noncomputable def riemannXiMultiplicityHadamardFactor (s ρ : ℂ) : ℂ :=
  riemannXiHadamardFactor s ρ ^ riemannXiZeroMultiplicity ρ

/-- The finite Hadamard product that records the analytic multiplicity of every xi-zero. -/
noncomputable def riemannXiMultiplicityHadamardProduct (R : ℝ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ riemannXiZerosInClosedBall R, riemannXiMultiplicityHadamardFactor s ρ

/-- Every finite multiplicity-aware Hadamard product is entire. -/
theorem differentiable_riemannXiMultiplicityHadamardProduct (R : ℝ) :
    Differentiable ℂ (riemannXiMultiplicityHadamardProduct R) := by
  intro s
  unfold riemannXiMultiplicityHadamardProduct riemannXiMultiplicityHadamardFactor
  apply DifferentiableAt.fun_finsetProd
  intro ρ _
  exact ((differentiable_riemannXiHadamardFactor ρ).differentiableAt).pow _

/-- The finite multiplicity-aware product with the factor at `ρ` removed. -/
noncomputable def riemannXiMultiplicityHadamardCofactor (R : ℝ) (ρ s : ℂ) : ℂ :=
  ∏ σ ∈ (riemannXiZerosInClosedBall R).erase ρ, riemannXiMultiplicityHadamardFactor s σ

/-- A designated ledger factor splits off from the multiplicity-aware finite product. -/
theorem riemannXiMultiplicityHadamardProduct_eq_factor_mul_cofactor {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) (s : ℂ) :
    riemannXiMultiplicityHadamardProduct R s =
      riemannXiMultiplicityHadamardFactor s ρ * riemannXiMultiplicityHadamardCofactor R ρ s := by
  unfold riemannXiMultiplicityHadamardProduct riemannXiMultiplicityHadamardCofactor
  exact (Finset.mul_prod_erase _ _ hρ).symm

/-- The removed-factor cofactor is entire in its complex argument. -/
theorem differentiable_riemannXiMultiplicityHadamardCofactor (R : ℝ) (ρ : ℂ) :
    Differentiable ℂ (riemannXiMultiplicityHadamardCofactor R ρ) := by
  intro s
  unfold riemannXiMultiplicityHadamardCofactor riemannXiMultiplicityHadamardFactor
  apply DifferentiableAt.fun_finsetProd
  intro σ _
  exact ((differentiable_riemannXiHadamardFactor σ).differentiableAt).pow _

/-- At its removed ledger point, the cofactor has no zero. -/
theorem riemannXiMultiplicityHadamardCofactor_ne_zero {R : ℝ} (ρ : ℂ) :
    riemannXiMultiplicityHadamardCofactor R ρ ρ ≠ 0 := by
  unfold riemannXiMultiplicityHadamardCofactor riemannXiMultiplicityHadamardFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro σ hσ
  have hσledger : σ ∈ riemannXiZerosInClosedBall R := Finset.mem_erase.mp hσ |>.2
  have hne : ρ ≠ σ := (Finset.mem_erase.mp hσ |>.1).symm
  exact
    pow_ne_zero _
      (riemannXiHadamardFactor_ne_zero (riemannXiZero_ne_zero_of_mem_ledger hσledger) hne)

/-- The nonvanishing analytic unit in one multiplicity-aware genus-one factor. -/
noncomputable def riemannXiMultiplicityHadamardUnit (s ρ : ℂ) : ℂ :=
  ((-1 / ρ) * Complex.exp (s / ρ)) ^ riemannXiZeroMultiplicity ρ

/-- A multiplicity-aware factor is a zero power times its nonvanishing analytic unit. -/
theorem riemannXiMultiplicityHadamardFactor_eq_sub_pow_mul_unit {s ρ : ℂ} (hρ : ρ ≠ 0) :
    riemannXiMultiplicityHadamardFactor s ρ =
      (s - ρ) ^ riemannXiZeroMultiplicity ρ * riemannXiMultiplicityHadamardUnit s ρ := by
  unfold riemannXiMultiplicityHadamardFactor riemannXiMultiplicityHadamardUnit
  rw [← mul_pow]
  congr 1
  unfold riemannXiHadamardFactor
  field_simp
  ring

/-- The analytic unit in a multiplicity-aware factor is nonzero at a nonzero attached zero. -/
theorem riemannXiMultiplicityHadamardUnit_ne_zero {ρ : ℂ} (hρ : ρ ≠ 0) :
    riemannXiMultiplicityHadamardUnit ρ ρ ≠ 0 := by
  unfold riemannXiMultiplicityHadamardUnit
  exact
    pow_ne_zero _
      (mul_ne_zero (div_ne_zero (neg_ne_zero.mpr one_ne_zero) hρ) (Complex.exp_ne_zero _))

/-- The analytic unit remaining after removing the exact zero power from a finite product at `ρ`. -/
noncomputable def riemannXiMultiplicityHadamardProductUnit (R : ℝ) (ρ s : ℂ) : ℂ :=
  riemannXiMultiplicityHadamardUnit s ρ * riemannXiMultiplicityHadamardCofactor R ρ s

/-- A finite multiplicity-aware product has the expected local zero-power factorization. -/
theorem riemannXiMultiplicityHadamardProduct_eq_sub_pow_mul_unit {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) (s : ℂ) :
    riemannXiMultiplicityHadamardProduct R s =
      (s - ρ) ^ riemannXiZeroMultiplicity ρ * riemannXiMultiplicityHadamardProductUnit R ρ s := by
  rw [riemannXiMultiplicityHadamardProduct_eq_factor_mul_cofactor hρ]
  rw [riemannXiMultiplicityHadamardFactor_eq_sub_pow_mul_unit
      (riemannXiZero_ne_zero_of_mem_ledger hρ)]
  simp only [riemannXiMultiplicityHadamardProductUnit]
  ring

/-- The finite-product local unit is analytic at its removed ledger zero. -/
theorem differentiable_riemannXiMultiplicityHadamardProductUnit (R : ℝ) (ρ : ℂ) :
    Differentiable ℂ (riemannXiMultiplicityHadamardProductUnit R ρ) := by
  intro s
  unfold riemannXiMultiplicityHadamardProductUnit riemannXiMultiplicityHadamardUnit
  apply DifferentiableAt.mul
  · fun_prop
  · exact (differentiable_riemannXiMultiplicityHadamardCofactor R ρ) s

/-- The finite-product local unit does not vanish at its removed ledger zero. -/
theorem riemannXiMultiplicityHadamardProductUnit_ne_zero_of_mem_ledger {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    riemannXiMultiplicityHadamardProductUnit R ρ ρ ≠ 0 := by
  unfold riemannXiMultiplicityHadamardProductUnit
  apply mul_ne_zero
  · exact riemannXiMultiplicityHadamardUnit_ne_zero (riemannXiZero_ne_zero_of_mem_ledger hρ)
  · exact riemannXiMultiplicityHadamardCofactor_ne_zero ρ

/-- Near any point, `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`
is its zero power times a nonvanishing analytic factor. -/
theorem exists_riemannXi_local_zero_factor (ρ : ℂ) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧ riemannXi =ᶠ[nhds ρ] fun s => (s - ρ) ^ riemannXiZeroMultiplicity ρ * g s := by
  have h :=
    ((differentiable_riemannXi.analyticAt ρ).analyticOrderAt_ne_top).mp
      (riemannXi_analyticOrderAt_ne_top ρ)
  simpa only [ne_eq, riemannXiZeroMultiplicity, smul_eq_mul] using h

/-- The totalized quotient of xi by its finite multiplicity-aware Hadamard product.
At ledger zeros, division returns a totalized value rather than the analytic
extension; separate local factorization lemmas construct that extension. -/
noncomputable def riemannXiMultiplicityHadamardQuotient (R : ℝ) (s : ℂ) : ℂ :=
  riemannXi s / riemannXiMultiplicityHadamardProduct R s

/-- Away from its ledger, the multiplicity-aware finite product is nonzero. -/
theorem riemannXiMultiplicityHadamardProduct_ne_zero {R : ℝ} {s : ℂ}
    (hs : ∀ ρ ∈ riemannXiZerosInClosedBall R, s ≠ ρ) :
    riemannXiMultiplicityHadamardProduct R s ≠ 0 := by
  unfold riemannXiMultiplicityHadamardProduct riemannXiMultiplicityHadamardFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  exact
    pow_ne_zero _
      (riemannXiHadamardFactor_ne_zero (riemannXiZero_ne_zero_of_mem_ledger hρ) (hs ρ hρ))

/-- Away from the finite ledger, the pointwise finite Hadamard quotient is analytic. -/
theorem analyticAt_riemannXiMultiplicityHadamardQuotient_of_not_mem {R : ℝ} {s : ℂ}
    (hs : s ∉ riemannXiZerosInClosedBall R) :
    AnalyticAt ℂ (riemannXiMultiplicityHadamardQuotient R) s := by
  unfold riemannXiMultiplicityHadamardQuotient
  apply (differentiable_riemannXi.analyticAt s).div
  · exact (differentiable_riemannXiMultiplicityHadamardProduct R).analyticAt s
  · apply riemannXiMultiplicityHadamardProduct_ne_zero
    intro ρ hρ hsr
    exact hs (hsr ▸ hρ)

/-- At every ledger zero, the finite Hadamard quotient has an analytic punctured-neighborhood
extension.

The displayed extension is the quotient of the two nonvanishing local analytic units after the
common zero power has been cancelled. -/
theorem exists_analyticAt_riemannXiMultiplicityHadamardQuotient_extension {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧ riemannXiMultiplicityHadamardQuotient R =ᶠ[nhdsWithin ρ {ρ}ᶜ] g := by
  obtain ⟨g, hg, hgzero, hxi⟩ := exists_riemannXi_local_zero_factor ρ
  let u : ℂ → ℂ := riemannXiMultiplicityHadamardProductUnit R ρ
  refine
    ⟨g / u,
      hg.div
        (by
          simpa only [u] using
            (differentiable_riemannXiMultiplicityHadamardProductUnit R ρ).analyticAt ρ)
        ?_,
      ?_, ?_⟩
  · exact riemannXiMultiplicityHadamardProductUnit_ne_zero_of_mem_ledger hρ
  · exact div_ne_zero hgzero (riemannXiMultiplicityHadamardProductUnit_ne_zero_of_mem_ledger hρ)
  · filter_upwards [hxi.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hsne
    unfold riemannXiMultiplicityHadamardQuotient
    rw [hs, riemannXiMultiplicityHadamardProduct_eq_sub_pow_mul_unit hρ]
    have hpow : (s - ρ) ^ riemannXiZeroMultiplicity ρ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hsne)
    simpa only [u, Pi.div_apply] using
      mul_div_mul_left (c := (s - ρ) ^ riemannXiZeroMultiplicity ρ) (g s) (u s) hpow

/-- A chosen analytic local extension of the finite Hadamard quotient at one ledger zero. -/
noncomputable def riemannXiMultiplicityHadamardQuotientLocalExtension (R : ℝ) (ρ : ℂ)
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) : ℂ → ℂ :=
  (exists_analyticAt_riemannXiMultiplicityHadamardQuotient_extension hρ).choose

/-- The chosen local finite-quotient extension is analytic at its ledger zero. -/
theorem analyticAt_riemannXiMultiplicityHadamardQuotientLocalExtension {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    AnalyticAt ℂ (riemannXiMultiplicityHadamardQuotientLocalExtension R ρ hρ) ρ :=
  (exists_analyticAt_riemannXiMultiplicityHadamardQuotient_extension hρ).choose_spec.1

/-- A selected local finite-quotient extension is nonzero at its ledger zero. -/
theorem riemannXiMultiplicityHadamardQuotientLocalExtension_ne_zero {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    riemannXiMultiplicityHadamardQuotientLocalExtension R ρ hρ ρ ≠ 0 :=
  (exists_analyticAt_riemannXiMultiplicityHadamardQuotient_extension hρ).choose_spec.2.1

/-- On the punctured neighborhood of its ledger zero, the chosen extension agrees with the
pointwise finite quotient. -/
theorem riemannXiMultiplicityHadamardQuotient_eventuallyEq_localExtension {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    riemannXiMultiplicityHadamardQuotient R =ᶠ[nhdsWithin ρ {ρ}ᶜ]
      riemannXiMultiplicityHadamardQuotientLocalExtension R ρ hρ :=
  (exists_analyticAt_riemannXiMultiplicityHadamardQuotient_extension hρ).choose_spec.2.2

/-- The finite quotient with its removable values replaced by their chosen local extensions. -/
noncomputable def riemannXiMultiplicityHadamardEntireQuotient (R : ℝ) (s : ℂ) : ℂ :=
  if hs : s ∈ riemannXiZerosInClosedBall R then
    riemannXiMultiplicityHadamardQuotientLocalExtension R s hs s
  else riemannXiMultiplicityHadamardQuotient R s

/-- Off its finite zero ledger, the entire-quotient representative is definitionally the original
pointwise quotient. -/
theorem riemannXiMultiplicityHadamardEntireQuotient_eq_quotient_of_not_mem {R : ℝ} {s : ℂ}
    (hs : s ∉ riemannXiZerosInClosedBall R) :
    riemannXiMultiplicityHadamardEntireQuotient R s =
      riemannXiMultiplicityHadamardQuotient R s := by
  simp only [riemannXiMultiplicityHadamardEntireQuotient, dite_eq_right hs]

/-- Near a ledger zero, the globally patched quotient agrees with its selected local extension. -/
theorem riemannXiMultiplicityHadamardEntireQuotient_eventuallyEq_localExtension {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    riemannXiMultiplicityHadamardEntireQuotient R =ᶠ[nhds ρ]
      riemannXiMultiplicityHadamardQuotientLocalExtension R ρ hρ := by
  let S := riemannXiZerosInClosedBall R
  have havoid : ∀ᶠ s in nhds ρ, s ∉ S.erase ρ :=
    General.eventually_not_mem_finset_nhds_of_not_mem
      (by simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true])
  have hlocal :
    ∀ᶠ s in nhds ρ,
      s ∈ ({ρ}ᶜ : Set ℂ) →
        riemannXiMultiplicityHadamardQuotient R s =
          riemannXiMultiplicityHadamardQuotientLocalExtension R ρ hρ s :=
    eventually_nhdsWithin_iff.mp
      (riemannXiMultiplicityHadamardQuotient_eventuallyEq_localExtension hρ)
  filter_upwards [havoid, hlocal] with s hsavoid hs
  by_cases hmem : s ∈ S
  · have hsρ : s = ρ := by
      by_contra hne
      exact hsavoid (Finset.mem_erase.mpr ⟨hne, hmem⟩)
    subst s
    simp only [riemannXiMultiplicityHadamardEntireQuotient, dite_eq_left hρ]
  · have hsne : s ∈ ({ρ}ᶜ : Set ℂ) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show s ≠ ρ from fun h => hmem (h ▸ hρ))
    rw [riemannXiMultiplicityHadamardEntireQuotient_eq_quotient_of_not_mem hmem]
    exact hs hsne

/-- The globally patched finite Hadamard quotient is analytic at every ledger zero. -/
theorem analyticAt_riemannXiMultiplicityHadamardEntireQuotient_of_mem {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    AnalyticAt ℂ (riemannXiMultiplicityHadamardEntireQuotient R) ρ :=
  (analyticAt_riemannXiMultiplicityHadamardQuotientLocalExtension hρ).congr
    (riemannXiMultiplicityHadamardEntireQuotient_eventuallyEq_localExtension hρ).symm

/-- The globally patched finite Hadamard quotient is analytic away from its zero ledger. -/
theorem analyticAt_riemannXiMultiplicityHadamardEntireQuotient_of_not_mem {R : ℝ} {s : ℂ}
    (hs : s ∉ riemannXiZerosInClosedBall R) :
    AnalyticAt ℂ (riemannXiMultiplicityHadamardEntireQuotient R) s := by
  apply (analyticAt_riemannXiMultiplicityHadamardQuotient_of_not_mem hs).congr
  filter_upwards [General.eventually_not_mem_finset_nhds_of_not_mem hs] with z hz
  exact (riemannXiMultiplicityHadamardEntireQuotient_eq_quotient_of_not_mem hz).symm

/-- The finite Hadamard quotient, with all removable values filled in, is entire. -/
theorem analyticAt_riemannXiMultiplicityHadamardEntireQuotient (R : ℝ) (s : ℂ) :
    AnalyticAt ℂ (riemannXiMultiplicityHadamardEntireQuotient R) s := by
  by_cases hs : s ∈ riemannXiZerosInClosedBall R
  · exact analyticAt_riemannXiMultiplicityHadamardEntireQuotient_of_mem hs
  · exact analyticAt_riemannXiMultiplicityHadamardEntireQuotient_of_not_mem hs

/-- The patched finite quotient does not vanish at any zero removed by its finite product. -/
theorem riemannXiMultiplicityHadamardEntireQuotient_ne_zero_of_mem {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannXiZerosInClosedBall R) :
    riemannXiMultiplicityHadamardEntireQuotient R ρ ≠ 0 := by
  simp only [riemannXiMultiplicityHadamardEntireQuotient, dite_eq_left hρ]
  exact riemannXiMultiplicityHadamardQuotientLocalExtension_ne_zero hρ

/-- `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`
factors globally into the finite multiplicity-aware product and its patched
entire quotient. -/
theorem riemannXi_eq_multiplicityHadamardProduct_mul_entireQuotient (R : ℝ) (s : ℂ) :
    riemannXi s =
      riemannXiMultiplicityHadamardProduct R s *
        riemannXiMultiplicityHadamardEntireQuotient R s := by
  by_cases hs : s ∈ riemannXiZerosInClosedBall R
  · have hxi : riemannXi s = 0 := (riemannXi_zero_mem_closedBall_of_mem_ledger hs).1
    have hfactor : riemannXiMultiplicityHadamardFactor s s = 0 := by
      unfold riemannXiMultiplicityHadamardFactor
      have hbase : riemannXiHadamardFactor s s = 0 :=
        (riemannXiHadamardFactor_eq_zero_iff (riemannXiZero_ne_zero_of_mem_ledger hs)).mpr rfl
      rw [hbase]
      exact zero_pow (Nat.ne_of_gt (riemannXiZeroMultiplicity_pos_of_mem_ledger hs))
    have hproduct : riemannXiMultiplicityHadamardProduct R s = 0 := by
      rw [riemannXiMultiplicityHadamardProduct_eq_factor_mul_cofactor hs, hfactor]
      simp only [zero_mul]
    rw [hxi, hproduct]
    simp only [zero_mul]
  · rw [riemannXiMultiplicityHadamardEntireQuotient_eq_quotient_of_not_mem hs]
    unfold riemannXiMultiplicityHadamardQuotient
    have hproduct : riemannXiMultiplicityHadamardProduct R s ≠ 0 := by
      apply riemannXiMultiplicityHadamardProduct_ne_zero
      intro ρ hρ hsr
      exact hs (hsr ▸ hρ)
    field_simp

/-- At a nonzero value of `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`,
neither factor in the finite global Hadamard factorization vanishes. -/
theorem riemannXiMultiplicityHadamardFactors_ne_zero_of_riemannXi_ne_zero {R : ℝ} {s : ℂ}
    (hs : riemannXi s ≠ 0) :
    riemannXiMultiplicityHadamardProduct R s ≠ 0 ∧
      riemannXiMultiplicityHadamardEntireQuotient R s ≠ 0 := by
  constructor <;> intro hzero
  · apply hs
    rw [riemannXi_eq_multiplicityHadamardProduct_mul_entireQuotient R s, hzero]
    simp only [zero_mul]
  · apply hs
    rw [riemannXi_eq_multiplicityHadamardProduct_mul_entireQuotient R s, hzero]
    simp only [mul_zero]

/-- The logarithmic derivative of the multiplicity-aware finite product is the weighted zero sum.

The coefficient of each genus-one contribution is the analytic order of
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi` at that zero. -/
theorem logDeriv_riemannXiMultiplicityHadamardProduct_eq_sum {R : ℝ} {s : ℂ}
    (hs : ∀ ρ ∈ riemannXiZerosInClosedBall R, s ≠ ρ) :
    logDeriv (riemannXiMultiplicityHadamardProduct R) s =
      ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicity ρ * (1 / (s - ρ) + 1 / ρ) := by
  unfold riemannXiMultiplicityHadamardProduct riemannXiMultiplicityHadamardFactor
  rw [show
      (fun s =>
          ∏ ρ ∈ riemannXiZerosInClosedBall R,
            riemannXiHadamardFactor s ρ ^ riemannXiZeroMultiplicity ρ) =
        ∏ ρ ∈ riemannXiZerosInClosedBall R,
          (fun s => riemannXiHadamardFactor s ρ ^ riemannXiZeroMultiplicity ρ)
      from by
      funext s
      simp only [Finset.prod_apply]]
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (differentiable_riemannXiHadamardFactor ρ).differentiableAt]
    rw [logDeriv_riemannXiHadamardFactor (riemannXiZero_ne_zero_of_mem_ledger hρ) (hs ρ hρ)]
  · intro ρ hρ
    exact
      pow_ne_zero _
        (riemannXiHadamardFactor_ne_zero (riemannXiZero_ne_zero_of_mem_ledger hρ) (hs ρ hρ))
  · intro ρ _
    exact ((differentiable_riemannXiHadamardFactor ρ).differentiableAt).pow _

/-- **Finite Hadamard logarithmic-derivative identity for `riemannXi`.**

Away from xi-zeros, `ξ'/ξ` is the multiplicity-weighted finite zero sum plus the logarithmic
derivative of the entire quotient. This is the finite-radius identity whose quotient term must be
controlled uniformly before sending the radius to infinity. -/
theorem logDeriv_riemannXi_eq_finite_sum_add_logDeriv_entireQuotient {R : ℝ} {s : ℂ}
    (hs : riemannXi s ≠ 0) :
    logDeriv riemannXi s =
      (∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicity ρ * (1 / (s - ρ) + 1 / ρ)) +
        logDeriv (riemannXiMultiplicityHadamardEntireQuotient R) s := by
  obtain ⟨hproduct, hquotient⟩ :=
    riemannXiMultiplicityHadamardFactors_ne_zero_of_riemannXi_ne_zero (R := R) hs
  have heq :
    riemannXi = fun z =>
      riemannXiMultiplicityHadamardProduct R z *
        riemannXiMultiplicityHadamardEntireQuotient R z := by
    funext z
    exact riemannXi_eq_multiplicityHadamardProduct_mul_entireQuotient R z
  rw [heq,
    show
      (fun z =>
          riemannXiMultiplicityHadamardProduct R z *
            riemannXiMultiplicityHadamardEntireQuotient R z) =
        riemannXiMultiplicityHadamardProduct R * riemannXiMultiplicityHadamardEntireQuotient R
      from by
      funext z
      rfl,
    logDeriv_mul s hproduct hquotient ((differentiable_riemannXiMultiplicityHadamardProduct R) s)
      (analyticAt_riemannXiMultiplicityHadamardEntireQuotient R s).differentiableAt]
  have hledger : ∀ ρ ∈ riemannXiZerosInClosedBall R, s ≠ ρ := by
    intro ρ hρ hsr
    apply hs
    rw [hsr, (riemannXi_zero_mem_closedBall_of_mem_ledger hρ).1]
  rw [logDeriv_riemannXiMultiplicityHadamardProduct_eq_sum hledger]

/-- The constant term left after removing the radius-`R` finite Hadamard product. -/
noncomputable def riemannXiFiniteHadamardConstant (R : ℝ) : ℂ :=
  logDeriv (riemannXiMultiplicityHadamardEntireQuotient R) 0

/-- The finite Hadamard constant is independent of the radius: it is `ξ'/ξ` at the origin.

Every genus-one factor has logarithmic derivative zero at zero, so the complete finite zero sum
vanishes at that point. -/
theorem logDeriv_riemannXi_zero_eq_finiteHadamardConstant (R : ℝ) :
    logDeriv riemannXi 0 = riemannXiFiniteHadamardConstant R := by
  have hxi : riemannXi 0 ≠ 0 := by
    rw [riemannXi_zero]
    norm_num only
  rw [logDeriv_riemannXi_eq_finite_sum_add_logDeriv_entireQuotient (R := R) (s := 0) hxi]
  unfold riemannXiFiniteHadamardConstant
  have hsum :
    ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicity ρ * (1 / ((0 : ℂ) - ρ) + 1 / ρ) =
      0 := by
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hne : ρ ≠ 0 := riemannXiZero_ne_zero_of_mem_ledger hρ
    field_simp
    ring
  rw [hsum, zero_add]

/-- The radius-`R` entire quotient is zero-free on the closed ball from which its finite zero
ledger was extracted. -/
theorem riemannXiMultiplicityHadamardEntireQuotient_ne_zero_on_closedBall {R : ℝ} {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) R) :
    riemannXiMultiplicityHadamardEntireQuotient R s ≠ 0 := by
  intro hzero
  have hxi : riemannXi s = 0 := by
    rw [riemannXi_eq_multiplicityHadamardProduct_mul_entireQuotient R s, hzero]
    simp only [mul_zero]
  have hledger : s ∈ riemannXiZerosInClosedBall R :=
    mem_riemannXiZerosInClosedBall_iff.mpr ⟨hxi, hs⟩
  exact riemannXiMultiplicityHadamardEntireQuotient_ne_zero_of_mem hledger hzero

/-- The radius-`R` entire quotient is zero-free on the corresponding open ball. -/
theorem riemannXiMultiplicityHadamardEntireQuotient_ne_zero_on_ball {R : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (0 : ℂ) R) : riemannXiMultiplicityHadamardEntireQuotient R s ≠ 0 :=
  riemannXiMultiplicityHadamardEntireQuotient_ne_zero_on_closedBall
    (Metric.ball_subset_closedBall hs)

/-- On every positive radius disk, the finite entire quotient has a holomorphic primitive of its
logarithmic derivative whose real part is the logarithm of its norm. -/
theorem exists_hasDerivAt_logDeriv_riemannXiMultiplicityHadamardEntireQuotient {R : ℝ}
    (hR : 0 < R) :
    ∃ h : ℂ → ℂ,
      (∀ w ∈ Metric.ball (0 : ℂ) R,
          HasDerivAt h (logDeriv (riemannXiMultiplicityHadamardEntireQuotient R) w) w) ∧
        ∀ w ∈ Metric.ball (0 : ℂ) R,
          (h w).re = Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R w‖ := by
  apply RiemannZeta.exists_hasDerivAt_logDeriv_re_eq_log_norm hR
  · intro w _
    exact analyticAt_riemannXiMultiplicityHadamardEntireQuotient R w
  · intro w hw
    exact riemannXiMultiplicityHadamardEntireQuotient_ne_zero_on_ball hw

/-- A Borel--Carathéodory/Cauchy bound for the finite quotient's logarithmic derivative.

The only non-formal input is an upper bound for `log ‖quotient‖` on the radius-`R` disk and a
strict version at the center. Thus this theorem isolates exactly the remaining analytic estimate
needed to control the finite quotient term in the Hadamard limit. -/
theorem norm_logDeriv_riemannXiMultiplicityHadamardEntireQuotient_le_of_log_norm_bound {R M : ℝ}
    (hR : 0 < R) (hM0 : Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖ < M)
    (hM :
      ∀ w ∈ Metric.ball (0 : ℂ) R, Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R w‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖logDeriv (riemannXiMultiplicityHadamardEntireQuotient R) z‖ ≤
      4 * (M - Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖) * (R + ‖z‖) /
        (R - ‖z‖) ^ 2 := by
  obtain ⟨h, hhderiv, hhre⟩ :=
    exists_hasDerivAt_logDeriv_riemannXiMultiplicityHadamardEntireQuotient hR
  have hMc : (h 0).re < M := by
    rw [hhre 0 (Metric.mem_ball_self hR)]
    exact hM0
  have hRe : ∀ w ∈ Metric.ball (0 : ℂ) R, (h w).re ≤ M := by
    intro w hw
    rw [hhre w hw]
    exact hM w hw
  have hbound := RiemannZeta.norm_hasDerivAt_le_of_re_le hR hhderiv hMc hRe hz
  rw [hhre 0 (Metric.mem_ball_self hR)] at hbound
  simpa only [sub_zero] using hbound

/-- Under a disk bound for the finite quotient, the finite zero sum approximates `ξ'/ξ` with the
explicit Borel--Carathéodory error bound. -/
theorem norm_logDeriv_riemannXi_sub_finiteHadamardSum_le_of_log_norm_bound {R M : ℝ} (hR : 0 < R)
    (hM0 : Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖ < M)
    (hM :
      ∀ w ∈ Metric.ball (0 : ℂ) R, Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R w‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) (hxi : riemannXi z ≠ 0) :
    ‖logDeriv riemannXi z -
          ∑ ρ ∈ riemannXiZerosInClosedBall R, riemannXiZeroMultiplicity ρ * (1 / (z - ρ) + 1 / ρ)‖ ≤
      4 * (M - Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖) * (R + ‖z‖) /
        (R - ‖z‖) ^ 2 := by
  have hquotient :=
    norm_logDeriv_riemannXiMultiplicityHadamardEntireQuotient_le_of_log_norm_bound hR hM0 hM hz
  rw [logDeriv_riemannXi_eq_finite_sum_add_logDeriv_entireQuotient (R := R) (s := z) hxi]
  simpa only [add_sub_cancel_left] using hquotient

/-- For every fixed positive radius, the finite quotient has a bounded logarithmic norm on its
open disk. This is a compactness bound, not the radius-uniform estimate needed for the limit. -/
theorem exists_log_norm_bound_riemannXiMultiplicityHadamardEntireQuotient {R : ℝ} (hR : 0 < R) :
    ∃ M : ℝ,
      Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖ < M ∧
        ∀ w ∈ Metric.ball (0 : ℂ) R,
          Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R w‖ ≤ M := by
  let q : ℂ → ℂ := riemannXiMultiplicityHadamardEntireQuotient R
  have hcont : ContinuousOn (fun w : ℂ => Real.log ‖q w‖) (Metric.closedBall (0 : ℂ) R) := by
    change
      ContinuousOn (fun w : ℂ => Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R w‖)
        (Metric.closedBall (0 : ℂ) R)
    intro w hw
    have hne : riemannXiMultiplicityHadamardEntireQuotient R w ≠ 0 :=
      riemannXiMultiplicityHadamardEntireQuotient_ne_zero_on_closedBall hw
    exact
      (((Real.continuousAt_log (norm_ne_zero_iff.mpr hne)).comp continuous_norm.continuousAt).comp
          (analyticAt_riemannXiMultiplicityHadamardEntireQuotient R
              w).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hcont
  refine ⟨C + 1, ?_, ?_⟩
  · have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := Metric.mem_closedBall_self hR.le
    have himage :
      (fun w : ℂ => Real.log ‖q w‖) 0 ∈
        (fun w : ℂ => Real.log ‖q w‖) '' Metric.closedBall (0 : ℂ) R :=
      ⟨0, hzero, rfl⟩
    have := hC himage
    dsimp only [q] at this ⊢
    linarith
  · intro w hw
    have hclosed : w ∈ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hw
    have himage :
      (fun v : ℂ => Real.log ‖q v‖) w ∈
        (fun v : ℂ => Real.log ‖q v‖) '' Metric.closedBall (0 : ℂ) R :=
      ⟨w, hclosed, rfl⟩
    have := hC himage
    dsimp only [q] at this ⊢
    linarith

/-- At each positive radius, the finite Hadamard zero sum approximates `ξ'/ξ`
on the stated disk with a finite Borel–Carathéodory bound. This theorem does
not assert a bound uniform in the radius. -/
theorem exists_finiteHadamard_logDeriv_approximation_bound {R : ℝ} (hR : 0 < R) :
    ∃ M : ℝ,
      Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖ < M ∧
        (∀ w ∈ Metric.ball (0 : ℂ) R,
          Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R w‖ ≤ M) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) R,
          riemannXi z ≠ 0 →
            ‖logDeriv riemannXi z -
                  ∑ ρ ∈ riemannXiZerosInClosedBall R,
                    riemannXiZeroMultiplicity ρ * (1 / (z - ρ) + 1 / ρ)‖ ≤
              4 * (M - Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖) * (R + ‖z‖) /
                (R - ‖z‖) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_log_norm_bound_riemannXiMultiplicityHadamardEntireQuotient hR
  refine ⟨M, hM0, hM, ?_⟩
  intro z hz hxi
  exact norm_logDeriv_riemannXi_sub_finiteHadamardSum_le_of_log_norm_bound hR hM0 hM hz hxi

/-- Every multiplicity-aware finite xi Hadamard product is normalized to one at the origin. -/
theorem riemannXiMultiplicityHadamardProduct_zero (R : ℝ) :
    riemannXiMultiplicityHadamardProduct R 0 = 1 := by
  simp only [riemannXiMultiplicityHadamardProduct, riemannXiMultiplicityHadamardFactor,
    riemannXiHadamardFactor]
  simp only [zero_div, sub_zero, Complex.exp_zero, mul_one, one_pow, Finset.prod_const_one]

/--
Input: a finite zero-ledger radius `R`.
Conclusion: the associated entire Hadamard quotient takes the radius-independent value `1 / 2`
at the origin.
Content: evaluate the global finite factorization at zero, where every genus-one factor is one.
Role: this fixes the base value in the Borel--Carathéodory quotient estimate and removes a
spurious radius-dependent center term from the limiting interface.
-/
theorem riemannXiMultiplicityHadamardEntireQuotient_zero (R : ℝ) :
    riemannXiMultiplicityHadamardEntireQuotient R 0 = 1 / 2 := by
  have hfactor := riemannXi_eq_multiplicityHadamardProduct_mul_entireQuotient R 0
  rw [riemannXiMultiplicityHadamardProduct_zero, one_mul, riemannXi_zero] at hfactor
  exact hfactor.symm

/--
Input: a finite zero-ledger radius `R`.
Conclusion: the norm of its entire quotient at zero is exactly `1 / 2`.
Content: take norms in the preceding complex base-value identity.
Role: the logarithmic quotient estimates can use a fixed positive center norm.
-/
theorem norm_riemannXiMultiplicityHadamardEntireQuotient_zero (R : ℝ) :
    ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖ = (1 : ℝ) / 2 := by
  rw [riemannXiMultiplicityHadamardEntireQuotient_zero]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat],
    Complex.norm_real]
  rw [Real.norm_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)]

/--
Input: a finite zero-ledger radius `R`.
Conclusion: its quotient's center logarithmic norm is `-log 2`.
Content: normalize the fixed positive norm `1 / 2` using `Real.log_inv`.
Role: this is the radius-independent center term in the finite quotient derivative bound.
-/
theorem log_norm_riemannXiMultiplicityHadamardEntireQuotient_zero (R : ℝ) :
    Real.log ‖riemannXiMultiplicityHadamardEntireQuotient R 0‖ = -Real.log 2 := by
  rw [norm_riemannXiMultiplicityHadamardEntireQuotient_zero]
  have hhalf : (1 : ℝ) / 2 = (2 : ℝ)⁻¹ := by norm_num only
  rw [hhalf, Real.log_inv]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
