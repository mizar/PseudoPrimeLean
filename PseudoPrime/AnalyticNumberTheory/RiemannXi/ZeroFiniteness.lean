/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.Basic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroSummability
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import Mathlib.Order.Filter.Finite
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Xi zeros in compact sets

Xi is entire and nonzero at zero, so the identity theorem makes its zeros
discrete and their complement codiscrete. Compact sets therefore contain only
finitely many zeros. Finite zero ledgers, multiplicity weights, and local
Hadamard quotients support finite-radius logarithmic-derivative estimates.
-/

@[expose] public section

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
      rw [h]
      push_cast
      ring
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

/-- For every real radius `R`, the xi zeros in the closed ball about zero are finite.
The nonzero set is codiscrete and the closed ball is compact, so its complement in the ball
is finite. No positivity of `R` is needed. This constructs the finite zero ledger below. -/
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

/-- For any real `R` and complex `ρ`, ledger membership means exactly `ξ(ρ) = 0` and
`ρ ∈ closedBall 0 R`. Unfold the finite-set conversion to prove the equivalence.
This is the interface for extracting analytic and geometric facts from finite sums. -/
theorem mem_riemannXiZerosInClosedBall_iff {R : ℝ} {ρ : ℂ} :
    ρ ∈ riemannXiZerosInClosedBall R ↔ riemannXi ρ = 0 ∧ ρ ∈ Metric.closedBall (0 : ℂ) R := by
  rw [riemannXiZerosInClosedBall, Set.Finite.mem_toFinset]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]

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

/-- For any complex point `ρ`, the natural analytic vanishing order of xi at `ρ`.
The order is finite because xi is entire and not identically zero; it is positive at zeros
and zero at nonzeros. This exponent records repeated zeros in the finite Hadamard product. -/
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

/-- For a complex `s`, assign its xi-zero multiplicity divided by `1 + (Im s)²` when
`ξ(s) = 0`, and zero otherwise. The natural multiplicity is cast to the reals.
This is the summable vertical weight used to bound finite contour zero masses. -/
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

/-- The imaginary-direction xi-zero weight with analytic multiplicity is summable over
all complex points. Its terms are nonnegative and bounded by the known summable zeta-zero
multiplicity weight, using equality of the corresponding analytic orders.
This gives the common upper bound for finite vertical zero masses. -/
theorem summable_riemannXiZeroMultiplicityWeight : Summable riemannXiZeroMultiplicityWeight := by
  exact
    Summable.of_nonneg_of_le
      (fun s => by
        unfold riemannXiZeroMultiplicityWeight
        split <;> positivity)
      riemannXiZeroMultiplicityWeight_le_nontrivialZetaZeroMultiplicityWeightFull
      RiemannZeta.summable_nontrivialZetaZeroMultiplicityWeightFull

/-- For a complex `s`, assign its xi-zero multiplicity divided by `1 + ‖s‖²` at zeros,
and zero elsewhere. The denominator is everywhere positive. This radial multiplicity weight
controls the finite genus-one Hadamard ledgers and their radius limits. -/
noncomputable def riemannXiZeroMultiplicityNormWeight (s : ℂ) : ℝ :=
  if riemannXi s = 0 then riemannXiZeroMultiplicity s / (1 + ‖s‖ ^ 2) else 0

/-- For every complex `s`, the radial multiplicity weight is at most the vertical one.
At a zero, compare the positive denominators using `(Im s)² ≤ ‖s‖²` and the nonnegative
multiplicity; elsewhere both vanish. This transfers summability to the radial weight. -/
theorem riemannXiZeroMultiplicityNormWeight_le_riemannXiZeroMultiplicityWeight (s : ℂ) :
    riemannXiZeroMultiplicityNormWeight s ≤ riemannXiZeroMultiplicityWeight s := by
  unfold riemannXiZeroMultiplicityNormWeight riemannXiZeroMultiplicityWeight
  by_cases hs : riemannXi s = 0
  · rw [ite_eq_left hs, ite_eq_left hs]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith only [Complex.im_sq_le_normSq s]
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- The radial xi-zero multiplicity weight is summable over all complex points.
It is nonnegative and pointwise bounded by the summable vertical multiplicity weight.
This supplies a radius-independent bound for finite Hadamard zero masses. -/
theorem summable_riemannXiZeroMultiplicityNormWeight :
    Summable riemannXiZeroMultiplicityNormWeight := by
  exact
    Summable.of_nonneg_of_le
      (fun s => by
        unfold riemannXiZeroMultiplicityNormWeight
        split <;> positivity)
      riemannXiZeroMultiplicityNormWeight_le_riemannXiZeroMultiplicityWeight
      summable_riemannXiZeroMultiplicityWeight

end PseudoPrime.AnalyticNumberTheory.RiemannXi
