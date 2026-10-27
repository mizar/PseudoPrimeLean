/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ConductorPrimeFactors
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorVerticalGrowth
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CenteredHadamard
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedPoissonEulerBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveZeroTransfer
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PowerSumInterpolation

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.CompletedGenusZeroSums

/-! # Local logarithmic derivatives and Turan bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a function analytic at `z` and nonzero there.
Claim: its logarithmic derivative is analytic at `z`.
Proof: write the logarithmic derivative as the quotient of the analytic derivative by the original
function, whose denominator is nonzero at `z`.
Role: guarantees arbitrary local differentiability of the zero-free analytic remainder.
-/
theorem analyticAt_logDeriv_of_ne_zero {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => logDeriv g w) z := by
  have hfun : (fun w : ℂ => logDeriv g w) = fun w => deriv g w / g w := by
    funext w
    exact logDeriv_apply g w
  rw [hfun]
  exact hg.deriv.div hg hgz

/--
The logarithmic derivative of the affine zero factor `z - u` is the reciprocal distance to `u`.
The identity also holds at `z = u`, where both sides are zero by field division conventions.
-/
theorem logDeriv_sub_const_eq_inv (u z : ℂ) : logDeriv (fun w : ℂ => w - u) z = (z - u)⁻¹ := by
  rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  exact one_div _

/--
Inputs: an entire analytic function with a nonzero value and an open disk.

Claim: away from a discrete set, the logarithmic derivative of the function is the
divisor-weighted sum of the linear zero factors plus the logarithmic derivative of a zero-free
analytic factor.

Proof: apply the logarithmic derivative product rules to the local factorization and to its finite
factorized rational function.

Role: separates the local zero sum from the analytic remainder before taking higher derivatives.
-/
theorem exists_analytic_local_logDeriv_decomposition {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) (c : ℂ) (R : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
        (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
        logDeriv F =ᶠ[Filter.codiscreteWithin (Metric.ball c |R|)]
          (fun z =>
            (∑ᶠ u, (MeromorphicOn.divisor F (Metric.ball c |R|) u) • (z - u)⁻¹) +
              logDeriv g z) := by
  rcases exists_analytic_local_zero_factorization hFglobal z₀ hz₀ c R with ⟨g, hg, hgn, hfactor⟩
  let U := Metric.ball c |R|
  let d := MeromorphicOn.divisor F U
  let P := ∏ᶠ u, (fun z : ℂ => z - u) ^ d u
  have hfactor' : F =ᶠ[Filter.codiscreteWithin U] P * g := by
    simpa only [U, d, P, smul_eq_mul] using hfactor
  have hball : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    intro z _
    exact hFglobal z trivial
  have hfinite : d.support.Finite := hball.meromorphicOn.divisor_ball_support_finite
  have hLine : ∀ u : ℂ, MeromorphicOn (fun z : ℂ => z - u) U := by
    intro u
    let A : ℂ → ℂ := fun z => z - u
    have hA : AnalyticOnNhd ℂ A Set.univ := fun z _ => analyticAt_id.sub analyticAt_const
    exact fun z hz => (hA z trivial).meromorphicAt
  have hLineOrder : ∀ u : ℂ, ∀ z ∈ U, meromorphicOrderAt (fun w : ℂ => w - u) z ≠ ⊤ := by
    intro u z hz
    let A : ℂ → ℂ := fun w => w - u
    have hA : AnalyticOnNhd ℂ A Set.univ := fun w _ => analyticAt_id.sub analyticAt_const
    have hbase : analyticOrderAt A (u + 1) ≠ ⊤ := by
      have hAat : AnalyticAt ℂ A (u + 1) := hA (u + 1) trivial
      have hAnz : A (u + 1) ≠ 0 := by
        dsimp [A]
        have heq : (u + 1 : ℂ) - u = 1 := by ring
        rw [heq]
        norm_num only
      rw [hAat.analyticOrderAt_eq_zero.mpr hAnz]
      exact ENat.natCast_ne_top 0
    have horder (w : ℂ) : analyticOrderAt A w ≠ ⊤ :=
      hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hbase
    rw [(hA z trivial).meromorphicOrderAt_eq]
    intro heq
    exact horder z (ENat.map_eq_top_iff.mp heq)
  have hgOrder : ∀ z ∈ U, meromorphicOrderAt g z ≠ ⊤ := by
    intro z hz
    have hgz := hg z hz
    have hzero : analyticOrderAt g z = 0 := hgz.analyticOrderAt_eq_zero.mpr (hgn ⟨z, hz⟩)
    rw [hgz.meromorphicOrderAt_eq, hzero]
    exact mt ENat.map_eq_top_iff.mp (ENat.natCast_ne_top 0)
  have hPmero : MeromorphicOn P U := (Function.FactorizedRational.meromorphicNFOn d U).meromorphicOn
  have hPorder : ∀ z ∈ U, meromorphicOrderAt P z ≠ ⊤ := fun z _ =>
    Function.FactorizedRational.meromorphicOrderAt_ne_top d
  have hLogFactor := hPmero.logDeriv_mul_eventuallyEq hg.meromorphicOn hPorder hgOrder
  have hLogZeros := MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hfinite hLine hLineOrder
  have hLogEq := logDeriv_congr_codiscreteWithin Metric.isOpen_ball hfactor'
  refine ⟨g, hg, hgn, ?_⟩
  filter_upwards [hLogEq, hLogFactor, hLogZeros] with z hEq hMul hZeros
  calc
    logDeriv F z = logDeriv (P * g) z := hEq
    _ = logDeriv P z + logDeriv g z := by simpa only [Pi.add_apply] using hMul
    _ = (∑ᶠ u, d u • logDeriv (fun w : ℂ => w - u) z) + logDeriv g z := by
      dsimp only [P]
      rw [hZeros]
    _ = (∑ᶠ u, d u • (z - u)⁻¹) + logDeriv g z := by simp only [logDeriv_sub_const_eq_inv]
    _ = (∑ᶠ u, (MeromorphicOn.divisor F (Metric.ball c |R|) u) • (z - u)⁻¹) + logDeriv g z := by rfl

/--
Inputs: a nontrivial character and a disk in the complex plane.
Claim: the completed logarithmic derivative splits into its local divisor sum and a zero-free
analytic factor.
Proof: instantiate the generic analytic factorization at the nonzero completed value at one.
Role: preserves the completed-L interface used by the existing local zero estimates.
-/
theorem exists_completedLFunction_local_logDeriv_decomposition {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
        (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
        logDeriv
            (DirichletCharacter.completedLFunction
              χ) =ᶠ[Filter.codiscreteWithin (Metric.ball c |R|)]
          (fun z =>
            (∑ᶠ u,
                (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
                    u) •
                  (z - u)⁻¹) +
              logDeriv g z) := by
  let F := DirichletCharacter.completedLFunction χ
  have hF : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have h1nz : F 1 ≠ 0 := dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  obtain ⟨g, hg, hgn, hdecomp⟩ := exists_analytic_local_logDeriv_decomposition hF 1 h1nz c R
  refine ⟨g, hg, hgn, ?_⟩
  simpa only [F] using hdecomp

/--
Inputs: complex functions `f` and `g` that agree with respect to the cofinite filter within an
open set `U`, and an order `n`.
Claim: Their `n`th iterated derivatives also agree with respect to that filter.
Proof: Inductively apply preservation of cofinite agreement under differentiation on an open set.
Role: transfers the local logarithmic-derivative decomposition to higher derivatives.
-/
theorem iteratedDeriv_congr_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h : f =ᶠ[Filter.codiscreteWithin U] g) (n : ℕ) :
    iteratedDeriv n f =ᶠ[Filter.codiscreteWithin U] iteratedDeriv n g := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact ih.codiscreteWithin_deriv hU

/--
Inputs: an entire analytic function with a nonzero value, a disk, and a derivative order `n`.
Claim: the `n`th derivative of the function's logarithmic derivative is a local
inverse-distance power sum plus the same derivative of the zero-free analytic remainder.
Proof: differentiate the logarithmic derivative decomposition away from the finite divisor
support,
then use the reciprocal-factor formula and analyticity of the remainder's logarithmic derivative.
Role: supplies the local higher-order zero sum needed by Turan's power-sum estimate.
-/
theorem exists_analytic_local_iterated_logDeriv_decomposition {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) (c : ℂ) (R : ℝ) (n : ℕ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
        (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
        iteratedDeriv n (logDeriv F) =ᶠ[Filter.codiscreteWithin (Metric.ball c |R|)]
          (fun z =>
            (∑ᶠ u,
                ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ) *
                  ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) +
              iteratedDeriv n (logDeriv g) z) := by
  rcases exists_analytic_local_logDeriv_decomposition hFglobal z₀ hz₀ c R with ⟨g, hg, hgn, hdecomp⟩
  let U := Metric.ball c |R|
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun u => (d u : ℂ)
  have hball : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    intro z _
    exact hFglobal z trivial
  have hfiniteD : d.support.Finite := hball.meromorphicOn.divisor_ball_support_finite
  have hfiniteM : m.support.Finite := by
    apply hfiniteD.subset
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    exact Int.cast_ne_zero.mp hu
  have hsumEq (z : ℂ) : (∑ᶠ u, d u • (z - u)⁻¹) = ∑ᶠ u, m u * (z - u)⁻¹ := by
    apply finsum_congr
    intro u
    dsimp only [m]
    rw [zsmul_eq_mul]
  have hdecomp' :
    logDeriv F =ᶠ[Filter.codiscreteWithin U] (fun z => (∑ᶠ u, m u * (z - u)⁻¹) + logDeriv g z) := by
    filter_upwards [hdecomp] with z hz
    rw [hz, hsumEq]
  have hiter := iteratedDeriv_congr_codiscreteWithin Metric.isOpen_ball hdecomp' n
  let s := hfiniteM.toFinset
  have havoid := eventually_forall_ne_of_finset s U
  have hpower := iteratedDeriv_finsum_reciprocal_sum m hfiniteM n U
  have hUevent : ∀ᶠ z in Filter.codiscreteWithin U, z ∈ U := by
    apply
      Filter.Eventually.filter_mono
        ((codiscreteWithin_le_codiscrete_inf_principal U).trans inf_le_right)
    simp
  have hsfun : (fun z : ℂ => ∑ᶠ u, m u * (z - u)⁻¹) = ∑ u ∈ s, fun w : ℂ => m u * (w - u)⁻¹ := by
    funext z
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    · simp only [Finset.sum_apply]
    · intro u hu
      simp only [Function.mem_support] at hu
      have hmu : m u ≠ 0 := by
        intro hm
        apply hu
        simp only [hm, zero_mul]
      simpa only [s, Finset.mem_coe] using
        (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hmu)
  refine ⟨g, hg, hgn, ?_⟩
  change
    iteratedDeriv n (logDeriv F) =ᶠ[Filter.codiscreteWithin U]
      (fun z =>
        (∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) +
          iteratedDeriv n (logDeriv g) z)
  filter_upwards [hiter, hpower, havoid, hUevent] with z hIter hPower hAvoid hzU
  have hzeroAnalytic : AnalyticAt ℂ (fun w : ℂ => ∑ᶠ u, m u * (w - u)⁻¹) z := by
    rw [hsfun]
    apply Finset.analyticAt_sum s
    intro u hu
    have hzu : z - u ≠ 0 := sub_ne_zero.mpr (hAvoid u hu)
    exact (analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv hzu))
  have hgAnalytic : AnalyticAt ℂ (fun w : ℂ => logDeriv g w) z := by
    have hfun : (fun w : ℂ => logDeriv g w) = fun w => deriv g w / g w := by
      funext w
      exact logDeriv_apply g w
    rw [hfun]
    exact (hg z hzU).deriv.div (hg z hzU) (hgn ⟨z, hzU⟩)
  have hadd := iteratedDeriv_add (n := n) hzeroAnalytic.contDiffAt hgAnalytic.contDiffAt
  calc
    iteratedDeriv n (logDeriv F) z =
        iteratedDeriv n (fun w : ℂ => (∑ᶠ u, m u * (w - u)⁻¹) + logDeriv g w) z :=
      hIter
    _ =
        iteratedDeriv n (fun w : ℂ => ∑ᶠ u, m u * (w - u)⁻¹) z +
          iteratedDeriv n (fun w : ℂ => logDeriv g w) z :=
      hadd
    _ =
        (∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) +
          iteratedDeriv n (fun w : ℂ => logDeriv g w) z :=
      by rw [hPower]

/--
Inputs: a nontrivial character, a disk, and a derivative order.
Claim: the completed-L higher logarithmic derivative has the corresponding local zero-sum formula.
Proof: apply the generic analytic decomposition using the nonzero completed value at one.
Role: keeps the established completed-L interface for downstream local Turán estimates.
-/
theorem exists_completedLFunction_local_iterated_logDeriv_decomposition {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) (n : ℕ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
        (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
        iteratedDeriv n
            (logDeriv
              (DirichletCharacter.completedLFunction
                χ)) =ᶠ[Filter.codiscreteWithin (Metric.ball c |R|)]
          (fun z =>
            (∑ᶠ u,
                ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                        (Metric.ball c |R|) u :
                      ℤ) :
                    ℂ) *
                  ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) +
              iteratedDeriv n (logDeriv g) z) := by
  let F := DirichletCharacter.completedLFunction χ
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have h1nz : F 1 ≠ 0 := dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  obtain ⟨g, hg, hgn, hdecomp⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition hFglobal 1 h1nz c R n
  refine ⟨g, hg, hgn, ?_⟩
  simpa only [F] using hdecomp

/--
Inputs: a function analytic at `z` and a derivative order.
Claim: Its iterated derivative is also analytic at the same point.
Proof: Induct on the order following the definition of iterated derivatives.
Role: extends an identity on a punctured neighborhood to the center.
-/
private theorem analyticAt_iteratedDeriv_local {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/--
Inputs: a nontrivial character, a positive local radius, and a nonzero central value of the
completed `L` function.
Claim: The iterated logarithmic-derivative identity from the local zero factorization also holds
at the disk center.
Proof: Transfer the identity on the cofinite filter to a punctured neighborhood, then extend to
the center using analyticity and continuity of both sides.
Role: gives a pointwise form of the multiplicity-weighted zero power sum for Turán-type estimates.
-/
theorem exists_analytic_local_iterated_logDeriv_decomposition_at_center {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hc : F c ≠ 0) (n : ℕ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
        (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
        iteratedDeriv n (logDeriv F) c =
          (∑ᶠ u,
              ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ) *
                ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - u) ^ (-1 - n : ℤ))) +
            iteratedDeriv n (logDeriv g) c := by
  rcases exists_analytic_local_iterated_logDeriv_decomposition hFglobal z₀ hz₀ c R n with
    ⟨g, hg, hgn, hdecomp⟩
  let U := Metric.ball c |R|
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun u => (d u : ℂ)
  have hcU : c ∈ U := by
    rw [Metric.mem_ball, dist_self]
    exact hR
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro z hz
    exact hFglobal z trivial
  have hdivc : d c = 0 := by
    rw [show d c = MeromorphicOn.divisor F U c from rfl,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hFanalytic hcU,
      analyticOrderAt_eq_zero.mpr (Or.inr hc)]
    rfl
  have hball : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    intro z _
    exact hFglobal z trivial
  have hfiniteD : d.support.Finite := hball.meromorphicOn.divisor_ball_support_finite
  have hfiniteM : m.support.Finite := by
    apply hfiniteD.subset
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    exact Int.cast_ne_zero.mp hu
  let s := hfiniteM.toFinset
  have hsSupport : ∀ u, u ∈ m.support → u ∈ s := by
    intro u hu
    simpa only [s, Finset.mem_coe] using (Set.Finite.mem_toFinset hfiniteM).mpr hu
  have hsfun : (fun z : ℂ => ∑ᶠ u, m u * (z - u)⁻¹) = ∑ u ∈ s, fun w : ℂ => m u * (w - u)⁻¹ := by
    funext z
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    · simp only [Finset.sum_apply]
    · intro u hu
      simp only [Function.mem_support] at hu
      have hmu : m u ≠ 0 := by
        intro hm
        apply hu
        simp only [hm, zero_mul]
      exact hsSupport u (by simpa only [Function.mem_support] using hmu)
  have hsumAnalytic : AnalyticAt ℂ (fun z : ℂ => ∑ᶠ u, m u * (z - u)⁻¹) c := by
    rw [hsfun]
    apply Finset.analyticAt_sum s
    intro u hu
    have huSupport : u ∈ m.support :=
      (Set.Finite.mem_toFinset hfiniteM).mp (by simpa only [s, Finset.mem_coe] using hu)
    have hmu : m u ≠ 0 := by
      intro hm
      have hmu' : m u ≠ 0 := by simpa only [Function.mem_support] using huSupport
      exact hmu' hm
    have hdu : d u ≠ 0 := by
      intro h
      exact hmu (by simp only [m, h, Int.cast_zero])
    have hcu : c ≠ u := by
      intro h
      subst u
      exact hdu hdivc
    have hsub : c - u ≠ 0 := sub_ne_zero.mpr hcu
    exact (analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv hsub))
  have hlogF : AnalyticAt ℂ (logDeriv F) c := by
    rw [show logDeriv F = fun w => deriv F w / F w
        by
        funext w
        exact logDeriv_apply F w]
    exact hFanalytic c hcU |>.deriv.div (hFanalytic c hcU) hc
  have hlogg : AnalyticAt ℂ (logDeriv g) c := by
    rw [show logDeriv g = fun w => deriv g w / g w
        by
        funext w
        exact logDeriv_apply g w]
    exact
      (hg c (by simpa only [U] using hcU)).deriv.div (hg c (by simpa only [U] using hcU))
        (hgn ⟨c, by simpa only [U] using hcU⟩)
  have hleft : AnalyticAt ℂ (iteratedDeriv n (logDeriv F)) c :=
    analyticAt_iteratedDeriv_local hlogF n
  have hrem : AnalyticAt ℂ (iteratedDeriv n (logDeriv g)) c :=
    analyticAt_iteratedDeriv_local hlogg n
  have hsumPowerFun :
    (fun z : ℂ => ∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) =
      ∑ u ∈ s, fun z : ℂ => m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ)) := by
    funext z
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    · simp only [Finset.sum_apply]
    · intro u hu
      simp only [Function.mem_support] at hu
      have hmu : m u ≠ 0 := by
        intro hm
        apply hu
        simp only [hm, zero_mul]
      exact hsSupport u (by simpa only [Function.mem_support] using hmu)
  have hsumPowerAnalytic :
    AnalyticAt ℂ
      (fun z : ℂ => ∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) c := by
    rw [hsumPowerFun]
    apply Finset.analyticAt_sum s
    intro u hu
    have huSupport : u ∈ m.support :=
      (Set.Finite.mem_toFinset hfiniteM).mp (by simpa only [s, Finset.mem_coe] using hu)
    have hmu : m u ≠ 0 := by
      intro hm
      have hmu' : m u ≠ 0 := by simpa only [Function.mem_support] using huSupport
      exact hmu' hm
    have hdu : d u ≠ 0 := by
      intro h
      exact hmu (by simp only [m, h, Int.cast_zero])
    have hcu : c ≠ u := by
      intro h
      subst u
      exact hdu hdivc
    have hsub : c - u ≠ 0 := sub_ne_zero.mpr hcu
    have hzpow : AnalyticAt ℂ (fun z : ℂ => (z - u) ^ (-1 - n : ℤ)) c :=
      (analyticAt_id.sub analyticAt_const).zpow hsub
    exact analyticAt_const.mul (analyticAt_const.mul hzpow)
  have hright :
    AnalyticAt ℂ
      (fun z =>
        (∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) +
          iteratedDeriv n (logDeriv g) z)
      c := by
    exact hsumPowerAnalytic.add hrem
  have hdecomp' :
    iteratedDeriv n (logDeriv F) =ᶠ[Filter.codiscreteWithin U]
      (fun z =>
        (∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) +
          iteratedDeriv n (logDeriv g) z) := by
    filter_upwards [hdecomp] with z hz
    simpa only [m, d] using hz
  have hpunct :=
    hleft.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      hright.meromorphicAt (by simpa only [U] using hcU) (Metric.isOpen_ball.preperfect) hdecomp'
  have hval :=
    PseudoPrime.AnalyticNumberTheory.General.eq_of_eventuallyEq_nhdsNE_of_continuousAt
      hleft.continuousAt hright.continuousAt hpunct
  refine ⟨g, hg, hgn, ?_⟩
  simpa only [m, d] using hval

/--
Inputs: a nontrivial completed L-function, a nonzero center, and a positive local radius.
Claim: its higher logarithmic derivative at the center is the local divisor power sum plus an
analytic remainder derivative.
Proof: instantiate the generic entire-function identity using the completed value at one.
Role: preserves the completed-L interface for existing explicit-center estimates.
-/
theorem exists_completedLFunction_local_iterated_logDeriv_decomposition_at_center {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) (n : ℕ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
        (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
        iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) c =
          (∑ᶠ u,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
                      u :
                    ℤ) :
                  ℂ) *
                ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - u) ^ (-1 - n : ℤ))) +
            iteratedDeriv n (logDeriv g) c := by
  let F := DirichletCharacter.completedLFunction χ
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have h1nz : F 1 ≠ 0 := dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  obtain ⟨g, hg, hgn, hdecomp⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition_at_center hFglobal 1 h1nz hR hc n
  refine ⟨g, hg, hgn, ?_⟩
  simpa only [F] using hdecomp

/--
Inputs: a zero-free analytic function on a closed disk, a boundary bound for its logarithmic
derivative, and a derivative order.
Claim: Bound the iterated derivative of the logarithmic derivative at the center using the
boundary bound and a power of the radius.
Proof: Establish analyticity of the logarithmic derivative and apply Cauchy's higher-derivative
estimate.
Role: connects the analytic-factor term in the local zero factorization to an explicit upper
bound.
-/
theorem norm_iteratedDeriv_logDeriv_le_of_forall_sphere_norm_le {c : ℂ} {R C : ℝ} {g : ℂ → ℂ}
    (n : ℕ) (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hgn : ∀ z ∈ Metric.closedBall c R, g z ≠ 0)
    (hC : ∀ z ∈ Metric.sphere c R, ‖logDeriv g z‖ ≤ C) :
    ‖iteratedDeriv n (logDeriv g) c‖ ≤ n.factorial * C / R ^ n := by
  have ha : ∀ z ∈ Metric.closedBall c R, AnalyticAt ℂ (logDeriv g) z := by
    intro z hz
    have hfun : logDeriv g = fun w => deriv g w / g w := by
      funext w
      exact logDeriv_apply g w
    rw [hfun]
    exact (hg z hz).deriv.div (hg z hz) (hgn z hz)
  have hd : DifferentiableOn ℂ (logDeriv g) (Metric.closedBall c R) := by
    intro z hz
    exact (ha z hz).differentiableAt.differentiableWithinAt
  have hc : ContinuousOn (logDeriv g) (Metric.closedBall c R) := by
    intro z hz
    exact (ha z hz).continuousAt.continuousWithinAt
  exact
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
      (DiffContOnCl.mk_ball (hd.mono Metric.ball_subset_closedBall) hc) hC

/--
Inputs: a zero-free analytic function `g` on a disk.
Claim: `g'/g` has a primitive on the disk that vanishes at the center.
Proof: Show the logarithmic derivative is analytic and use existence of primitives for analytic
functions on a disk.
Role: enables a Borel–Carathéodory estimate for the logarithmic derivative of the local
zero-free factor.
-/
theorem exists_normalized_primitive_logDeriv_on_ball {c : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R)) (hgn : ∀ z ∈ Metric.ball c R, g z ≠ 0) :
    ∃ h : ℂ → ℂ, h c = 0 ∧ ∀ z ∈ Metric.ball c R, HasDerivAt h (logDeriv g z) z := by
  have hlog : DifferentiableOn ℂ (fun z : ℂ => logDeriv g z) (Metric.ball c R) := by
    intro z hz
    have hgz : g z ≠ 0 := hgn z hz
    have hfun : (fun w : ℂ => logDeriv g w) = fun w => deriv g w / g w := by
      funext w
      exact logDeriv_apply g w
    rw [hfun]
    exact (hg z hz).deriv.div (hg z hz) hgz |>.differentiableAt.differentiableWithinAt
  obtain ⟨h, hh0, hh⟩ := hlog.isExactOn_ball.with_val_at c 0
  exact ⟨h, hh0, hh⟩

/--
Inputs: a zero-free analytic function on a disk and a normalized primitive of its logarithmic
derivative.
Claim: On the disk, `g(z)=g(c) exp(h(z))`.
Proof: Show that the derivative of `g exp(-h)` vanishes, so this function is constant on the disk.
Role: bounds the real part of the primitive using an upper bound for the analytic factor and a
lower bound at the center.
-/
theorem eq_center_mul_exp_of_primitive_logDeriv_on_ball {c : ℂ} {R : ℝ} {g h : ℂ → ℂ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R)) (hgn : ∀ z ∈ Metric.ball c R, g z ≠ 0) (h0 : h c = 0)
    (hh : ∀ z ∈ Metric.ball c R, HasDerivAt h (logDeriv g z) z) :
    ∀ z ∈ Metric.ball c R, g z = g c * Complex.exp (h z) := by
  let F : ℂ → ℂ := fun z => g z * Complex.exp (-h z)
  have hderiv : ∀ z ∈ Metric.ball c R, deriv F z = 0 := by
    intro z hz
    have hgz := hgn z hz
    have hga := hg z hz
    have hG : HasDerivAt g (deriv g z) z := hga.differentiableAt.hasDerivAt
    have hE : HasDerivAt (fun w => Complex.exp (-h w)) (Complex.exp (-h z) * -logDeriv g z) z :=
      (hh z hz).neg.cexp
    have hF :
      HasDerivAt F (deriv g z * Complex.exp (-h z) + g z * (Complex.exp (-h z) * -logDeriv g z))
        z := by
      exact hG.mul hE
    have hcancel : g z * (-(deriv g z / g z)) = -(deriv g z) := by
      rw [mul_neg, mul_div_cancel₀ _ hgz]
    have hsum :
      deriv g z * Complex.exp (-h z) + g z * (Complex.exp (-h z) * -logDeriv g z) = 0 := by
      rw [logDeriv_apply g z]
      calc
        _ = deriv g z * Complex.exp (-h z) + (g z * (-(deriv g z / g z))) * Complex.exp (-h z) := by
          congr 1
          calc
            g z * (Complex.exp (-h z) * -(deriv g z / g z)) =
                g z * ((-(deriv g z / g z)) * Complex.exp (-h z)) :=
              by rw [mul_comm (Complex.exp (-h z))]
            _ = (g z * (-(deriv g z / g z))) * Complex.exp (-h z) := by rw [mul_assoc]
        _ = deriv g z * Complex.exp (-h z) + (-(deriv g z)) * Complex.exp (-h z) := by rw [hcancel]
        _ = 0 := by rw [← add_mul, add_neg_cancel, zero_mul]
    rw [hF.deriv, hsum]
  have hdiff : DifferentiableOn ℂ F (Metric.ball c R) := by
    intro z hz
    have hga := hg z hz
    have hG : HasDerivAt g (deriv g z) z := hga.differentiableAt.hasDerivAt
    have hE : HasDerivAt (fun w => Complex.exp (-h w)) (Complex.exp (-h z) * -logDeriv g z) z :=
      (hh z hz).neg.cexp
    have hF :
      HasDerivAt F (deriv g z * Complex.exp (-h z) + g z * (Complex.exp (-h z) * -logDeriv g z))
        z := by
      exact hG.mul hE
    exact hF.differentiableAt.differentiableWithinAt
  have hconst : ∀ x ∈ Metric.ball c R, ∀ y ∈ Metric.ball c R, F x = F y := by
    intro x hx y hy
    exact
      Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected hdiff hderiv hx
        hy
  intro z hz
  have hcenter : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have heq := hconst z hz c hcenter
  have heq' : g z * Complex.exp (-h z) = g c := by
    simpa only [F, h0, neg_zero, Complex.exp_zero, mul_one] using heq
  calc
    g z = (g z * Complex.exp (-h z)) * Complex.exp (h z) := by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = g c * Complex.exp (h z) := by rw [heq']

/--
Inputs: a primitive whose derivative on the disk is the logarithmic derivative of `g`.
Claim: The `(n+1)`st derivative of the primitive equals the `n`th derivative of the logarithmic
derivative.
Proof: Transfer the equality on the open disk to interior iterated derivatives and identify
these with ordinary derivatives on the open set.
Role: converts Cauchy estimates for the primitive into derivative estimates for the logarithmic
derivative.
-/
theorem iteratedDeriv_succ_eq_logDeriv_of_primitive_on_ball {c : ℂ} {R : ℝ} {g h : ℂ → ℂ} (n : ℕ)
    (hR : 0 < R) (hh : ∀ z ∈ Metric.ball c R, HasDerivAt h (logDeriv g z) z) :
    iteratedDeriv (n + 1) h c = iteratedDeriv n (logDeriv g) c := by
  have hderiv : Set.EqOn (deriv h) (logDeriv g) (Metric.ball c R) := by
    intro z hz
    exact (hh z hz).deriv
  have hwithin := iteratedDerivWithin_congr (n := n) hderiv
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  calc
    iteratedDeriv (n + 1) h c = iteratedDeriv n (deriv h) c := by rw [iteratedDeriv_succ']
    _ = iteratedDerivWithin n (deriv h) (Metric.ball c R) c :=
      (iteratedDerivWithin_of_isOpen Metric.isOpen_ball hc).symm
    _ = iteratedDerivWithin n (logDeriv g) (Metric.ball c R) c := hwithin hc
    _ = iteratedDeriv n (logDeriv g) c := iteratedDerivWithin_of_isOpen Metric.isOpen_ball hc

/--
Inputs: an upper bound for the function on a disk, a positive lower bound at the center, and the
exponential representation of a primitive.
Claim: Bound the real part of the primitive by the logarithm of the ratio of the function upper
bound to the central lower bound.
Proof: Express the norm of a complex exponential as the exponential of its real part and use
monotonicity of the real logarithm.
Role: transfers function bounds from finite Hadamard factorization to the primitive.
-/
theorem re_primitive_le_of_norm_bounds_on_ball {c : ℂ} {R A B : ℝ} {g h : ℂ → ℂ} (hA : 0 < A)
    (hB : 0 < B) (hG : ∀ z ∈ Metric.ball c R, ‖g z‖ ≤ A) (hlower : B ≤ ‖g c‖)
    (hEq : ∀ z ∈ Metric.ball c R, g z = g c * Complex.exp (h z)) :
    ∀ z ∈ Metric.ball c R, (h z).re ≤ Real.log (A / B) := by
  intro z hz
  have hnorm : ‖g z‖ = ‖g c‖ * Real.exp (h z).re := by rw [hEq z hz, norm_mul, Complex.norm_exp]
  have hprod : Real.exp (h z).re * B ≤ A := by
    calc
      Real.exp (h z).re * B = B * Real.exp (h z).re := mul_comm _ _
      _ ≤ ‖g c‖ * Real.exp (h z).re := mul_le_mul_of_nonneg_right hlower (le_of_lt (Real.exp_pos _))
      _ = ‖g z‖ := hnorm.symm
      _ ≤ A := hG z hz
  have hexp : Real.exp (h z).re ≤ A / B := (le_div_iff₀ hB).2 hprod
  exact (Real.le_log_iff_exp_le (div_pos hA hB)).2 hexp

/--
Inputs: a differentiable function on a disk centered at a point where it vanishes, and a uniform
upper bound on its real part.
Claim: Bound the function norm inside the disk using the real-part bound and distance from the
center.
Proof: Translate the disk to center `0` and apply the Borel–Carathéodory theorem.
Role: turns a real-part estimate for the primitive of a logarithmic derivative into a norm
estimate.
-/
theorem norm_le_of_re_le_on_ball_of_zero_center {c : ℂ} {R M : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hRe : ∀ z ∈ Metric.ball c R, (f z).re ≤ M) (hfc : f c = 0) {z : ℂ} (hz : z ∈ Metric.ball c R) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  let F : ℂ → ℂ := fun w => f (c + w)
  have hmap : Set.MapsTo (fun w : ℂ => c + w) (Metric.ball 0 R) (Metric.ball c R) := by
    intro w hw
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
  have htrans : DifferentiableOn ℂ F (Metric.ball 0 R) := by
    exact
      hf.fun_comp
        (fun w _ => (differentiableAt_const c).add differentiableAt_id |>.differentiableWithinAt)
        hmap
  have hReF : Set.MapsTo F (Metric.ball 0 R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    exact hRe (c + w) (hmap hw)
  have hFzero : F 0 = 0 := by simp only [F, add_zero, hfc]
  have hz0 : z - c ∈ Metric.ball (0 : ℂ) R := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
  have hbound := Complex.borelCaratheodory_zero hM htrans hReF hR hz0 hFzero
  calc
    ‖f z‖ = ‖f (c + (z - c))‖ := by
      congr 1
      rw [← add_sub_assoc, add_sub_cancel_left]
    _ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := hbound

/--
Inputs: a function analytic on a disk of radius `R`, an upper bound on its real part, and `r < R`.
Claim: Bound its iterated derivative at the center using Borel–Carathéodory and Cauchy's estimate.
Proof: Bound the function on the circle of radius `r` and apply Cauchy's higher-derivative
estimate.
Role: puts derivatives of the logarithmic-derivative primitive in a form usable for zero
detection.
-/
theorem norm_iteratedDeriv_le_of_re_le_on_ball {c : ℂ} {R r M : ℝ} {f : ℂ → ℂ} (n : ℕ) (hR : 0 < R)
    (hr : 0 < r) (hrr : r < R) (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hRe : ∀ z ∈ Metric.ball c R, (f z).re ≤ M) (hfc : f c = 0) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * (2 * M * r / (R - r)) / r ^ n := by
  have hdiff : DifferentiableOn ℂ f (Metric.closedBall c r) := by
    intro z hz
    have hzR : z ∈ Metric.ball c R := Metric.closedBall_subset_ball hrr hz
    exact ((hf z hzR).differentiableAt (Metric.isOpen_ball.mem_nhds hzR)).differentiableWithinAt
  have hcont : ContinuousOn f (Metric.closedBall c r) := by
    intro z hz
    have hzR : z ∈ Metric.ball c R := Metric.closedBall_subset_ball hrr hz
    exact
      ((hf z hzR).differentiableAt
            (Metric.isOpen_ball.mem_nhds hzR)).continuousAt |>.continuousWithinAt
  have hsphere : ∀ z ∈ Metric.sphere c r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro z hz
    have hzc : ‖z - c‖ = r := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp hz
    have hzball : z ∈ Metric.ball c R :=
      Metric.closedBall_subset_ball hrr (Metric.sphere_subset_closedBall hz)
    have hbc := norm_le_of_re_le_on_ball_of_zero_center hR hM hf hRe hfc hzball
    rw [hzc] at hbc
    exact hbc
  exact
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      (DiffContOnCl.mk_ball (hdiff.mono Metric.ball_subset_closedBall) hcont) hsphere

/--
Inputs: an analytic zero-free function on a disk, a uniform upper bound, a lower bound at the
center, and an inner radius.
Claim: Bound the central iterated derivatives of the logarithmic derivative using these bounds
and radii.
Proof: Construct a primitive of the logarithmic derivative and apply, in sequence, its
exponential representation, a real-part bound, and Cauchy's estimate.
Role: explicitly bounds the derivative error from the analytic factor in a local zero
factorization.
-/
theorem norm_iteratedDeriv_logDeriv_le_of_norm_bounds_on_ball {c : ℂ} {R r A B : ℝ} {g : ℂ → ℂ}
    (n : ℕ) (hR : 0 < R) (hr : 0 < r) (hrr : r < R) (hA : 0 < A) (hB : 0 < B) (hBA : B < A)
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R)) (hgn : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hG : ∀ z ∈ Metric.ball c R, ‖g z‖ ≤ A) (hlower : B ≤ ‖g c‖) :
    ‖iteratedDeriv n (logDeriv g) c‖ ≤
      (n + 1).factorial * (2 * Real.log (A / B) * r / (R - r)) / r ^ (n + 1) := by
  obtain ⟨h, h0, hh⟩ := exists_normalized_primitive_logDeriv_on_ball hg hgn
  have hEq := eq_center_mul_exp_of_primitive_logDeriv_on_ball hR hg hgn h0 hh
  have hM : 0 < Real.log (A / B) := Real.log_pos ((one_lt_div hB).2 hBA)
  have hRe := re_primitive_le_of_norm_bounds_on_ball hA hB hG hlower hEq
  have hiter := iteratedDeriv_succ_eq_logDeriv_of_primitive_on_ball (c := c) (R := R) n hR hh
  have hdifferentiable : DifferentiableOn ℂ h (Metric.ball c R) := by
    intro z hz
    exact (hh z hz).differentiableAt.differentiableWithinAt
  rw [← hiter]
  exact norm_iteratedDeriv_le_of_re_le_on_ball (n + 1) hR hr hrr hM hdifferentiable hRe h0

/--
Inputs: a function analytic on a closed disk and a uniform bound on its difference from its
central value.
Claim: Bound each positive-order iterated derivative at the center using the difference bound
and disk radius.
Proof: Apply Cauchy's derivative estimate to the function minus its central value; the
derivative of the constant term vanishes.
Role: transfers a central-difference estimate from a finite-radius Hadamard factorization to
higher derivatives.
-/
theorem norm_iteratedDeriv_le_of_forall_ball_norm_sub_center_le {c : ℂ} {R C : ℝ} {f : ℂ → ℂ}
    (n : ℕ) (hn : 0 < n) (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hC : ∀ z ∈ Metric.closedBall c R, ‖f z - f c‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n := by
  let F : ℂ → ℂ := fun z => f z - f c
  have hFanalytic : AnalyticOnNhd ℂ F (Metric.closedBall c R) := by
    intro z hz
    change AnalyticAt ℂ (fun w => f w - f c) z
    exact (hf z hz).sub analyticAt_const
  have hd : DifferentiableOn ℂ F (Metric.closedBall c R) := by
    intro z hz
    exact (hFanalytic z hz).differentiableAt.differentiableWithinAt
  have hc : ContinuousOn F (Metric.closedBall c R) := by
    intro z hz
    exact (hFanalytic z hz).continuousAt.continuousWithinAt
  have hbound : ∀ z ∈ Metric.sphere c R, ‖F z‖ ≤ C := by
    intro z hz
    exact hC z (Metric.sphere_subset_closedBall hz)
  have hmain :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
      (DiffContOnCl.mk_ball (hd.mono Metric.ball_subset_closedBall) hc) hbound
  have hderiv : iteratedDeriv n F c = iteratedDeriv n f c := by
    have hF : F = fun z => -f c + f z := by
      funext z
      dsimp [F]
      ring
    rw [hF]
    exact iteratedDeriv_const_add hn (-f c)
  rw [← hderiv]
  exact hmain

/--
Inputs: an entire function nonzero at the center and a zero in a positive-radius disk of radius
at most `1`.
Claim: Bound below the inverse-distance power sum over disk zeros counted with multiplicity by
an explicit Turán denominator.
Proof: Convert the finite local zero support to multiplicity weights and apply Turán's estimate
to normalized inverse distances, which are at least `1`.
Role: obtains a zero-detection lower bound from the central logarithmic-derivative decomposition.
-/
theorem exists_analytic_local_zero_turan_bound {F : ℂ → ℂ} (hFglobal : AnalyticOnNhd ℂ F Set.univ)
    {c : ℂ} {R : ℝ} (hR : 0 < |R|) (hRsmall : |R| ≤ 1) (hc : F c ≠ 0)
    (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support) (M : ℕ) :
    ∃ s : Finset ℂ,
      (∀ u, u ∈ s ↔ (MeromorphicOn.divisor F (Metric.ball c |R|)) u ≠ 0) ∧
        0 < s.card ∧
        (∀ u ∈ s, u ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) u ≠ 0) ∧
        ∃ l ∈ Finset.range s.card,
          ‖∑ u ∈ s, ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ)‖ /
              (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
            ‖∑ u ∈ s,
                ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ) *
                  (c - u)⁻¹ ^ (M + 1 + l)‖ := by
  classical
  let U := Metric.ball c |R|
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun u => (d u : ℂ)
  have hcU : c ∈ U := by
    rw [Metric.mem_ball, dist_self]; exact hR
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro z hz
    exact hFglobal z trivial
  have hball : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    intro z _
    exact hFglobal z trivial
  have hfiniteD : d.support.Finite := hball.meromorphicOn.divisor_ball_support_finite
  have hfiniteM : m.support.Finite := by
    apply hfiniteD.subset
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    exact Int.cast_ne_zero.mp hu
  let s := hfiniteM.toFinset
  have hspos : 0 < s.card := by
    apply Finset.card_pos.mpr
    rcases hzeros with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hdu : d u ≠ 0 := hu
    have hmu : m u ≠ 0 := by
      intro hm
      have : (d u : ℂ) = 0 := hm
      exact hdu (Int.cast_eq_zero.mp this)
    exact (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hmu)
  have hsum (f : ℂ → ℂ) : (∑ u ∈ s, m u * f u) = ∑ᶠ u, m u * f u := by
    symm
    apply finsum_eq_sum_of_support_subset _ (s := s)
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    have hmu : m u ≠ 0 := by
      intro hm
      apply hu
      simp only [hm, zero_mul]
    exact (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hmu)
  have hfreq : ∀ u ∈ s, (1 : ℝ) ≤ ‖(c - u)⁻¹‖ := by
    intro u hu
    have huSupport : u ∈ m.support :=
      (Set.Finite.mem_toFinset hfiniteM).mp (by simpa only [s] using hu)
    have hmu : m u ≠ 0 := by simpa only [Function.mem_support] using huSupport
    have hdu : d u ≠ 0 := by
      intro h
      exact hmu (by simp only [m, h, Int.cast_zero])
    have huball : u ∈ U := d.supportWithinDomain hdu
    have hsub : c - u ≠ 0 := by
      intro h
      have huEq : u = c := (sub_eq_zero.mp h).symm
      subst u
      have hdivc : d c = 0 := by
        rw [show d c = MeromorphicOn.divisor F U c from rfl,
          MeromorphicOn.AnalyticOnNhd.divisor_apply hFanalytic hcU,
          analyticOrderAt_eq_zero.mpr (Or.inr hc)]
        rfl
      exact hdu hdivc
    have hdist : ‖c - u‖ < |R| := by
      have h := (Metric.mem_ball.mp (by simpa only [U] using huball))
      rw [dist_eq_norm] at h
      simpa only [norm_sub_rev] using h
    have hnormpos : 0 < ‖c - u‖ := norm_pos_iff.mpr hsub
    have hnormlt : ‖c - u‖ < 1 := lt_of_lt_of_le hdist hRsmall
    rw [norm_inv]
    simpa only [one_div] using (one_le_div₀ hnormpos).2 (le_of_lt hnormlt)
  have hTuran :=
    exists_finset_weighted_power_sum_norm_ge_turan s m (fun u => (c - u)⁻¹) M hspos hfreq
  obtain ⟨l, hl, hbound⟩ := hTuran
  refine ⟨s, ?_, hspos, ?_, l, hl, ?_⟩
  · intro u
    simpa only [s, Set.Finite.mem_toFinset, Function.mem_support, m, d] using
      (Int.cast_ne_zero :
        ((MeromorphicOn.divisor F U u : ℤ) : ℂ) ≠ 0 ↔ MeromorphicOn.divisor F U u ≠ 0)
  · intro u hu
    have huSupport : u ∈ m.support :=
      (Set.Finite.mem_toFinset hfiniteM).mp (by simpa only [s] using hu)
    have hmu : m u ≠ 0 := by simpa only [Function.mem_support] using huSupport
    have hdu : d u ≠ 0 := by
      intro h
      exact hmu (by simp only [m, h, Int.cast_zero])
    exact ⟨d.supportWithinDomain hdu, hdu⟩
  · simpa only [m] using hbound

/--
Inputs: a nontrivial character, a nonzero completed-L center, and a zero in the local divisor.
Claim: the completed-L divisor satisfies the local Turán power-sum lower bound.
Proof: instantiate the generic analytic-function result for the completed L-function.
Role: preserves the interface used by existing completed-L derivative estimates.
-/
theorem exists_completedLFunction_local_zero_turan_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < |R|) (hRsmall : |R| ≤ 1)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hzeros :
      ∃ u,
        u ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |R|)).support)
    (M : ℕ) :
    ∃ s : Finset ℂ,
      (∀ u,
          u ∈ s ↔
            (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|))
                u ≠
              0) ∧
        0 < s.card ∧
        (∀ u ∈ s,
          u ∈ Metric.ball c |R| ∧
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|) u ≠
              0) ∧
        ∃ l ∈ Finset.range s.card,
          ‖∑ u ∈ s,
                  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                        (Metric.ball c |R|) u :
                      ℤ) :
                    ℂ)‖ /
              (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
            ‖∑ u ∈ s,
                ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                        (Metric.ball c |R|) u :
                      ℤ) :
                    ℂ) *
                  (c - u)⁻¹ ^ (M + 1 + l)‖ := by
  let F := DirichletCharacter.completedLFunction χ
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  obtain ⟨s, hs, hspos, hdomain, l, hl, hbound⟩ :=
    exists_analytic_local_zero_turan_bound hFglobal hR hRsmall hc hzeros M
  refine ⟨s, ?_, hspos, ?_, l, hl, hbound⟩
  · intro u
    simpa only [F] using hs u
  · intro u hu
    simpa only [F] using hdomain u hu

/--
Inputs: a globally analytic function, a nonzero center, and a zero in its local divisor support.
Claim: some reciprocal power sum over the complete local divisor support has a lower bound scaled
by the disk radius.
Proof: make the integer divisor multiplicities into complex weights, use their nonnegative total
mass, and apply the finite weighted reciprocal Turán estimate on the disk.
Role: supplies a positive, radius-sensitive zero term on the same support used by local
factorization.
-/
theorem exists_analytic_local_zero_scaled_reciprocal_power_sum {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) {c : ℂ} {R : ℝ} (hR : 0 < |R|) (hc : F c ≠ 0)
    (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support) (M : ℕ) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        (∀ u, u ∈ s ↔ (MeromorphicOn.divisor F (Metric.ball c |R|)) u ≠ 0) ∧
          0 < s.card ∧
          (∀ u ∈ s, u ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) u ≠ 0) ∧
          1 / (2 ^ (M + 2 * s.card) * |R| ^ (M + 1 + l)) ≤
            ‖∑ᶠ u,
                ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ) *
                  (c - u)⁻¹ ^ (M + 1 + l)‖ := by
  classical
  let U := Metric.ball c |R|
  let d : ℂ → ℤ := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun u => (d u : ℂ)
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro z hz
    exact hFglobal z trivial
  have hFclosed : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    intro z hz
    exact hFglobal z trivial
  have hfiniteD : d.support.Finite := hFclosed.meromorphicOn.divisor_ball_support_finite
  have hfiniteM : m.support.Finite := by
    apply hfiniteD.subset
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    exact Int.cast_ne_zero.mp hu
  let s := hfiniteM.toFinset
  have hsupportToDivisor : ∀ u ∈ s, d u ≠ 0 := by
    intro u hu
    have hmu : m u ≠ 0 := by
      have hmem := (Set.Finite.mem_toFinset hfiniteM).mp hu
      simpa only [Function.mem_support] using hmem
    intro hzero
    apply hmu
    simp only [m, hzero, Int.cast_zero]
  have hspos : 0 < s.card := by
    apply Finset.card_pos.mpr
    rcases hzeros with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hdu : d u ≠ 0 := hu
    have hmu : m u ≠ 0 := by
      intro hm
      exact hdu (Int.cast_eq_zero.mp hm)
    exact (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hmu)
  have hsum (f : ℂ → ℂ) : (∑ u ∈ s, m u * f u) = ∑ᶠ u, m u * f u := by
    symm
    apply finsum_eq_sum_of_support_subset _ (s := s)
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    have hmu : m u ≠ 0 := by
      intro hm
      apply hu
      simp only [hm, zero_mul]
    exact (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hmu)
  have hnonneg : ∀ u ∈ s, 0 ≤ d u := by
    intro u _
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFanalytic u
  obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp hspos
  have hdupos : 0 < d u₀ := by
    exact lt_of_le_of_ne (hnonneg u₀ hu₀) (Ne.symm (hsupportToDivisor u₀ hu₀))
  have hmassInt : 1 ≤ ∑ u ∈ s, d u := by
    have hsingle : d u₀ ≤ ∑ u ∈ s, d u := by
      apply Finset.single_le_sum
      · intro u hu
        exact hnonneg u hu
      · exact hu₀
    omega
  have hsumCast : (∑ u ∈ s, (d u : ℂ)) = ((∑ u ∈ s, d u : ℤ) : ℂ) := by
    push_cast
    rfl
  have hmass : (1 : ℝ) ≤ ‖∑ u ∈ s, (d u : ℂ)‖ := by
    rw [hsumCast, Complex.norm_intCast]
    rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ ∑ u ∈ s, d u by omega))]
    exact_mod_cast hmassInt
  have hcenterNe : ∀ u ∈ s, c ≠ u := by
    intro u hu heq
    subst u
    have hdivzero : d c = 0 := by
      rw [show d c = MeromorphicOn.divisor F U c from rfl,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hFanalytic
          (Metric.mem_ball.mpr
            (by
              simp only [dist_self]; exact hR)),
        analyticOrderAt_eq_zero.mpr (Or.inr hc)]
      rfl
    have hdivNe : d c ≠ 0 := hsupportToDivisor c hu
    exact hdivNe hdivzero
  have hdistance : ∀ u ∈ s, 0 < ‖c - u‖ ∧ ‖c - u‖ ≤ |R| := by
    intro u hu
    have hduNe : d u ≠ 0 := hsupportToDivisor u hu
    have huU : u ∈ U := (MeromorphicOn.divisor F U).supportWithinDomain hduNe
    have huBall : dist u c < |R| := Metric.mem_ball.mp huU
    rw [dist_eq_norm] at huBall
    constructor
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (hcenterNe u hu))
    · exact le_of_lt (by simpa only [norm_sub_rev] using huBall)
  obtain ⟨l, hl, hbound⟩ :=
    exists_finset_weighted_reciprocal_power_sum_norm_ge_of_disk s c m M hspos |R| hR hdistance
  have hden : 0 < 2 ^ (M + 2 * s.card) * |R| ^ (M + 1 + l) := by positivity
  have hscaled :
    1 / (2 ^ (M + 2 * s.card) * |R| ^ (M + 1 + l)) ≤ ‖∑ u ∈ s, m u * (c - u)⁻¹ ^ (M + 1 + l)‖ := by
    have hnum : (1 : ℝ) ≤ ‖∑ u ∈ s, m u‖ := by simpa only [m] using hmass
    have hdiv := div_le_div_of_nonneg_right hnum hden.le
    exact hdiv.trans hbound
  have hscaled' :
    1 / (2 ^ (M + 2 * s.card) * |R| ^ (M + 1 + l)) ≤ ‖∑ᶠ u, m u * (c - u)⁻¹ ^ (M + 1 + l)‖ := by
    rw [← hsum]
    exact hscaled
  refine ⟨s, l, hl, ?_, hspos, ?_, ?_⟩
  · intro u
    simpa only [s, Set.Finite.mem_toFinset, Function.mem_support, m, d, U] using
      (Int.cast_ne_zero :
        ((MeromorphicOn.divisor F U u : ℤ) : ℂ) ≠ 0 ↔ MeromorphicOn.divisor F U u ≠ 0)
  · intro u hu
    have huSupport : u ∈ m.support :=
      (Set.Finite.mem_toFinset hfiniteM).mp (by simpa only [s] using hu)
    have hmu : m u ≠ 0 := by simpa only [Function.mem_support] using huSupport
    have hdu : d u ≠ 0 := by
      intro hzero
      exact hmu (by simp only [m, hzero, Int.cast_zero])
    exact ⟨(MeromorphicOn.divisor F U).supportWithinDomain hdu, hdu⟩
  · simpa only [m, d, U] using hscaled'

/--
Inputs: a globally analytic function, a nonzero value at the center, and a zero in the local disk.

Claim: after repeating each local zero according to its analytic divisor order, a zero of maximal
reciprocal-distance norm controls one of the first total-multiplicity many reciprocal power sums.

Proof: enumerate the divisor support, replace each nonnegative divisor order by its natural
multiplicity, and apply the finite repeated-node maximum estimate.

Role: supplies the local zero term needed for a maximum-node logarithmic-derivative detection
bound without discarding zero multiplicities.
-/
theorem exists_analytic_local_zero_max_reciprocal_power_sum {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) {c : ℂ} {R : ℝ} (hR : 0 < |R|) (hc : F c ≠ 0)
    (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support) :
    ∃ s : Finset ℂ,
      (∀ v, v ∈ s ↔ MeromorphicOn.divisor F (Metric.ball c |R|) v ≠ 0) ∧
        ∃ u ∈ s,
          (∀ v ∈ s,
              0 < (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat →
                ‖(c - v)⁻¹‖ ≤ ‖(c - u)⁻¹‖) ∧
            1 / |R| ≤ ‖(c - u)⁻¹‖ ∧
            ∃ k ∈ Finset.range (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat),
              (∀ v ∈ s, v ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) v ≠ 0) ∧
                (1 /
                      (4 *
                        ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat : ℕ) :
                          ℝ))) *
                    ‖(c - u)⁻¹‖ ^ (k + 1) ≤
                  ‖∑ᶠ v,
                      ((MeromorphicOn.divisor F (Metric.ball c |R|) v : ℤ) : ℂ) *
                        (c - v)⁻¹ ^ (k + 1)‖ := by
  classical
  let U := Metric.ball c |R|
  let d : ℂ → ℤ := MeromorphicOn.divisor F U
  let weight : ℂ → ℂ := fun v => (d v : ℂ)
  let multiplicity : ℂ → ℕ := fun v => (d v).toNat
  let node : ℂ → ℂ := fun v => (c - v)⁻¹
  obtain ⟨s, _, _, hs, hspos, hdomain, _⟩ :=
    exists_analytic_local_zero_scaled_reciprocal_power_sum hFglobal hR hc hzeros 0
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro z hz
    exact hFglobal z trivial
  have hnonneg : ∀ v ∈ s, 0 ≤ d v := by
    intro v hv
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFanalytic v
  have hdivnonzero : ∀ v ∈ s, d v ≠ 0 := by
    intro v hv
    exact (hs v).mp hv
  have hpositiveMass : 0 < ∑ v ∈ s, multiplicity v := by
    obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp hspos
    have hdivpos : 0 < d v₀ := lt_of_le_of_ne (hnonneg v₀ hv₀) (Ne.symm (hdivnonzero v₀ hv₀))
    have hmultpos : 0 < multiplicity v₀ := by
      dsimp only [multiplicity]
      have hcast := Int.toNat_of_nonneg (le_of_lt hdivpos)
      exact_mod_cast hcast.symm ▸ hdivpos
    have hsingle : multiplicity v₀ ≤ ∑ v ∈ s, multiplicity v := by
      apply Finset.single_le_sum
      · intro v hv
        exact Nat.zero_le _
      · exact hv₀
    omega
  have hmultCast : ∀ v ∈ s, (multiplicity v : ℂ) = weight v := by
    intro v hv
    dsimp only [multiplicity, weight]
    exact_mod_cast Int.toNat_of_nonneg (hnonneg v hv)
  have hcenterNe : ∀ v ∈ s, c ≠ v := by
    intro v hv heq
    subst v
    have hdivzero : d c = 0 := by
      rw [show d c = MeromorphicOn.divisor F U c from rfl,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hFanalytic
          (Metric.mem_ball.mpr
            (by
              simp only [dist_self]; exact hR)),
        analyticOrderAt_eq_zero.mpr (Or.inr hc)]
      rfl
    exact (hdivnonzero c hv) hdivzero
  have hsum (k : ℕ) :
    (∑ v ∈ s, weight v * node v ^ (k + 1)) = ∑ᶠ v, weight v * node v ^ (k + 1) := by
    symm
    apply finsum_eq_sum_of_support_subset _ (s := s)
    intro v hv
    simp only [Function.mem_support] at hv ⊢
    have hweight : weight v ≠ 0 := by
      intro hzero
      apply hv
      simp only [hzero, zero_mul]
    exact (hs v).mpr (Int.cast_ne_zero.mp hweight)
  obtain ⟨u, hu, huMult, hmax, k, hk, hbound⟩ :=
    exists_finset_weighted_max_node_power_sum_norm_ge s multiplicity node hpositiveMass
  have hsumWeighted :
    (∑ v ∈ s, (multiplicity v : ℂ) * node v ^ (k + 1)) = ∑ v ∈ s, weight v * node v ^ (k + 1) := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [hmultCast v hv]
  rw [hsumWeighted, hsum] at hbound
  have hdomain' : ∀ v ∈ s, v ∈ U ∧ d v ≠ 0 := by
    intro v hv
    simpa only [U, d] using (hdomain v hv)
  have hmax' :
    ∀ v ∈ s,
      0 < (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat → ‖(c - v)⁻¹‖ ≤ ‖(c - u)⁻¹‖ := by
    intro v hv hmult
    exact hmax v hv (by simpa only [multiplicity, U, d] using hmult)
  have hdist : ‖c - u‖ < |R| := by
    have h := Metric.mem_ball.mp (by simpa only [U] using (hdomain u hu).1)
    rw [dist_eq_norm] at h
    simpa only [norm_sub_rev] using h
  have hnormpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hcenterNe u hu))
  have hrad : 1 / |R| ≤ ‖(c - u)⁻¹‖ := by
    rw [norm_inv]
    simpa only [one_div] using (inv_le_inv₀ hR hnormpos).2 hdist.le
  refine ⟨s, hs, u, hu, hmax', hrad, k, hk, hdomain', ?_⟩
  simpa only [U, d, node, multiplicity] using hbound

/--
Inputs: a globally analytic function, a nonzero center value, and a specified zero in the local
divisor support.

Claim: the selected maximal reciprocal-distance node has norm at least that of the specified zero,
and one of the first total-multiplicity many weighted power sums has the corresponding lower bound.

Proof: expose the support equivalence from the local maximum-node estimate and use positivity of
the analytic divisor order at the specified zero.

Role: preserves the identity of a zero supplied by a height window while passing to the maximal
node used in derivative detection.
-/
theorem exists_analytic_local_zero_max_reciprocal_power_sum_of_mem {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) {c : ℂ} {R : ℝ} (hR : 0 < |R|) (hc : F c ≠ 0) (ρ : ℂ)
    (hρ : MeromorphicOn.divisor F (Metric.ball c |R|) ρ ≠ 0) :
    ∃ s : Finset ℂ,
      (∀ v, v ∈ s ↔ MeromorphicOn.divisor F (Metric.ball c |R|) v ≠ 0) ∧
        ρ ∈ s ∧
        ∃ u ∈ s,
          (∀ v ∈ s,
              0 < (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat →
                ‖(c - v)⁻¹‖ ≤ ‖(c - u)⁻¹‖) ∧
            ‖(c - ρ)⁻¹‖ ≤ ‖(c - u)⁻¹‖ ∧
            1 / |R| ≤ ‖(c - u)⁻¹‖ ∧
            ∃ k ∈ Finset.range (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat),
              (1 /
                    (4 *
                      ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat : ℕ) : ℝ))) *
                  ‖(c - u)⁻¹‖ ^ (k + 1) ≤
                ‖∑ᶠ v,
                    ((MeromorphicOn.divisor F (Metric.ball c |R|) v : ℤ) : ℂ) *
                      (c - v)⁻¹ ^ (k + 1)‖ := by
  let U := Metric.ball c |R|
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro z hz
    exact hFglobal z trivial
  have hρnonneg : 0 ≤ MeromorphicOn.divisor F U ρ :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFanalytic ρ
  have hρpos : 0 < MeromorphicOn.divisor F U ρ := lt_of_le_of_ne hρnonneg (Ne.symm hρ)
  have hρmult : 0 < (MeromorphicOn.divisor F U ρ).toNat := by
    have hcast : ((MeromorphicOn.divisor F U ρ).toNat : ℤ) = MeromorphicOn.divisor F U ρ :=
      Int.toNat_of_nonneg hρnonneg
    exact_mod_cast hcast.symm ▸ hρpos
  obtain ⟨s, hs, u, hu, hmax, hrad, k, hk, hdomain, hbound⟩ :=
    exists_analytic_local_zero_max_reciprocal_power_sum hFglobal hR hc ⟨ρ, hρ⟩
  have hρmem : ρ ∈ s := (hs ρ).mpr hρ
  refine ⟨s, hs, hρmem, u, hu, hmax, hmax ρ hρmem hρmult, hrad, k, hk, ?_⟩
  simpa only [U] using hbound

/--
Inputs: a positive scale `η`, a nonzero center value, and a specified local zero within distance
`3η` of the center.

Claim: for some derivative-compatible exponent below the total local multiplicity, the weighted
reciprocal power sum is at least `1 / (4N)` times `(1 / (3η))^(k+1)`, where `N` is the total
multiplicity in the disk.

Proof: choose a maximal reciprocal-distance node among all repeated divisor occurrences, compare
it with the specified zero, and raise their nonnegative norm inequality to the selected power.

Role: gives the quantitative near-zero main term required by the positive detection estimate.
-/
theorem exists_analytic_local_zero_power_sum_lower_bound_of_near {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) {c : ℂ} {η : ℝ} (hη : 0 < η) (hc : F c ≠ 0) (ρ : ℂ)
    (hρ : MeromorphicOn.divisor F (Metric.ball c |80 * η|) ρ ≠ 0) (hclose : ‖c - ρ‖ ≤ 3 * η) :
    ∃ s : Finset ℂ,
      ∃ u ∈ s,
        ∃ k ∈ Finset.range (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat),
          (1 /
                (4 *
                  ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) :
                    ℝ))) *
              (1 / (3 * η)) ^ (k + 1) ≤
            ‖∑ᶠ v,
                ((MeromorphicOn.divisor F (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
                  (c - v)⁻¹ ^ (k + 1)‖ := by
  have hR : 0 < |80 * η| := by
    rw [abs_of_pos (mul_pos (by norm_num) hη)]
    positivity
  obtain ⟨s, _, _, u, hu, _, hρmax, _, k, hk, hbound⟩ :=
    exists_analytic_local_zero_max_reciprocal_power_sum_of_mem hFglobal hR hc ρ hρ
  have hFanalytic : AnalyticOnNhd ℂ F (Metric.ball c |80 * η|) := by
    intro z hz
    exact hFglobal z trivial
  have hρnonneg : 0 ≤ MeromorphicOn.divisor F (Metric.ball c |80 * η|) ρ :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFanalytic ρ
  have hρpos : 0 < MeromorphicOn.divisor F (Metric.ball c |80 * η|) ρ :=
    lt_of_le_of_ne hρnonneg (Ne.symm hρ)
  have hρneq : c - ρ ≠ 0 := by
    intro heq
    have hdivzero : MeromorphicOn.divisor F (Metric.ball c |80 * η|) c = 0 := by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hFanalytic
          (Metric.mem_ball.mpr
            (by
              simp only [dist_self]; positivity)),
        analyticOrderAt_eq_zero.mpr (Or.inr hc)]
      rfl
    have hρeq : ρ = c := (sub_eq_zero.mp heq).symm
    subst ρ
    exact hρ hdivzero
  have hρnormpos : 0 < ‖c - ρ‖ := norm_pos_iff.mpr hρneq
  have hρinv : 1 / (3 * η) ≤ ‖(c - ρ)⁻¹‖ := by
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hρnormpos hclose
  have huinv : 1 / (3 * η) ≤ ‖(c - u)⁻¹‖ := le_trans hρinv hρmax
  have hpow : (1 / (3 * η)) ^ (k + 1) ≤ ‖(c - u)⁻¹‖ ^ (k + 1) :=
    pow_le_pow_left₀ (by positivity) huinv _
  have htotal : 0 < ∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat :=
    Nat.zero_lt_of_lt (Finset.mem_range.mp hk)
  have htotalReal :
    0 < ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) : ℝ) := by
    exact_mod_cast htotal
  have hfactor :
    0 <
      1 /
        (4 * ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) : ℝ)) := by
    positivity
  refine ⟨s, u, hu, k, hk, ?_⟩
  calc
    _ ≤
        (1 / (4 * ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) : ℝ)) *
          ‖(c - u)⁻¹‖ ^ (k + 1)) :=
      by exact mul_le_mul_of_nonneg_left hpow hfactor.le
    _ ≤ _ := hbound

/--
Inputs: a positive scale, a specified local zero within `3η`, and a positive integer block scale.

Claim: the multiplicity-weighted local reciprocal power sum has a lower bound at an exponent
between the block scale and the block scale times the total local multiplicity.

Proof: retain the specified zero in the finite divisor support, apply the weighted maximum-node
block estimate, and identify its finite sum with the divisor-supported sum.

Role: carries a known near zero into a shifted power block without requiring a gap to the other
local zeros.
-/
theorem exists_analytic_local_zero_power_sum_block_lower_bound_of_near {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) {c : ℂ} {η : ℝ} (hη : 0 < η) (hc : F c ≠ 0) (ρ : ℂ)
    (hρ : MeromorphicOn.divisor F (Metric.ball c |80 * η|) ρ ≠ 0) (hclose : ‖c - ρ‖ ≤ 3 * η)
    (K : ℕ) :
    ∃ s : Finset ℂ,
      (∀ v, v ∈ s ↔ MeromorphicOn.divisor F (Metric.ball c |80 * η|) v ≠ 0) ∧
        ρ ∈ s ∧
        (∀ v ∈ s,
          v ∈ Metric.ball c |80 * η| ∧ MeromorphicOn.divisor F (Metric.ball c |80 * η|) v ≠ 0) ∧
        ∃ k ∈ Finset.range (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat),
          K ≤ K * (k + 1) ∧
            K * (k + 1) ≤
              K * (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat) ∧
            (1 /
                  (4 *
                    ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) :
                      ℝ))) *
                (1 / (3 * η)) ^ (K * (k + 1)) ≤
              ‖∑ᶠ v,
                  ((MeromorphicOn.divisor F (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
                    (c - v)⁻¹ ^ (K * (k + 1))‖ := by
  classical
  have hR : 0 < |80 * η| := by
    rw [abs_of_pos (mul_pos (by norm_num) hη)]
    positivity
  obtain ⟨s, hs, hρmem, _⟩ :=
    exists_analytic_local_zero_max_reciprocal_power_sum_of_mem hFglobal hR hc ρ hρ
  let U := Metric.ball c |80 * η|
  let d : ℂ → ℤ := MeromorphicOn.divisor F U
  let weight : ℂ → ℂ := fun v => (d v : ℂ)
  let multiplicity : ℂ → ℕ := fun v => (d v).toNat
  let node : ℂ → ℂ := fun v => (c - v)⁻¹
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro z hz
    exact hFglobal z trivial
  have hnonneg : ∀ v ∈ s, 0 ≤ d v := by
    intro v hv
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFanalytic v
  have hρnonneg : 0 ≤ d ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFanalytic ρ
  have hρpos : 0 < d ρ := lt_of_le_of_ne hρnonneg (Ne.symm hρ)
  have hρmult : 0 < multiplicity ρ := by
    dsimp only [multiplicity]
    have hcast := Int.toNat_of_nonneg (le_of_lt hρpos)
    exact_mod_cast hcast.symm ▸ hρpos
  have hmass : 0 < ∑ v ∈ s, multiplicity v := by
    have hsingle : multiplicity ρ ≤ ∑ v ∈ s, multiplicity v :=
      Finset.single_le_sum (fun v hv => Nat.zero_le _) hρmem
    omega
  have hmultCast : ∀ v ∈ s, (multiplicity v : ℂ) = weight v := by
    intro v hv
    dsimp only [multiplicity, weight, d]
    exact_mod_cast Int.toNat_of_nonneg (hnonneg v hv)
  have hρneq : c - ρ ≠ 0 := by
    intro heq
    have hdivzero : d c = 0 := by
      rw [show d c = MeromorphicOn.divisor F U c from rfl,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hFanalytic
          (Metric.mem_ball.mpr
            (by
              simp only [dist_self]; positivity)),
        analyticOrderAt_eq_zero.mpr (Or.inr hc)]
      rfl
    have hρeq : ρ = c := (sub_eq_zero.mp heq).symm
    subst ρ
    exact hρ hdivzero
  have hρnormpos : 0 < ‖c - ρ‖ := norm_pos_iff.mpr hρneq
  have hρinv : 1 / (3 * η) ≤ ‖node ρ‖ := by
    dsimp only [node]
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hρnormpos hclose
  obtain ⟨k, hk, hKlow, hKhigh, hbound⟩ :=
    exists_finset_weighted_power_sum_norm_ge_fixed_multiple_block_of_near s multiplicity node hmass
      (le_refl _) ρ hρmem hρmult K (1 / (3 * η)) (by positivity) hρinv
  have hsum (p : ℕ) : (∑ v ∈ s, weight v * node v ^ p) = ∑ᶠ v, weight v * node v ^ p := by
    symm
    apply finsum_eq_sum_of_support_subset _ (s := s)
    intro v hv
    simp only [Function.mem_support] at hv ⊢
    have hweight : weight v ≠ 0 := by
      intro hzero
      apply hv
      simp only [hzero, zero_mul]
    exact (hs v).mpr (Int.cast_ne_zero.mp hweight)
  have hsumWeighted (p : ℕ) :
    (∑ v ∈ s, (multiplicity v : ℂ) * node v ^ p) = ∑ v ∈ s, weight v * node v ^ p := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [hmultCast v hv]
  rw [hsumWeighted, hsum] at hbound
  have hdomain' : ∀ v ∈ s, v ∈ U ∧ d v ≠ 0 := by
    intro v hv
    constructor
    · have hvSupport : v ∈ (MeromorphicOn.divisor F U).support := by exact (hs v).mp hv
      exact (MeromorphicOn.divisor F U).supportWithinDomain hvSupport
    · exact (hs v).mp hv
  refine ⟨s, ?_, hρmem, ?_, k, hk, hKlow, hKhigh, ?_⟩
  · intro v
    simpa only [U, d] using hs v
  · intro v hv
    simpa only [U, d] using hdomain' v hv
  · simpa only [U, d, weight, node] using hbound

/--
Inputs: a primitive completed-function local zero, a rectangle containing the local divisor
support, and a natural upper bound for the rectangle's multiplicity count.

Claim: the near-zero weighted power sum has a lower bound at an exponent between `K` and `K * C`.

Proof: apply the local block estimate and use the divisor-support multiplicity comparison to
replace its local total multiplicity by the supplied rectangle count bound.

Role: connects the fixed-multiple power-sum estimate to the local zero-counting interface.
-/
theorem exists_completedLFunction_local_zero_power_sum_fixed_multiple_block_of_near {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {η : ℝ} (hη : 0 < η)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) (ρ : ℂ)
    (hρ :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|) ρ ≠
        0)
    (hclose : ‖c - ρ‖ ≤ 3 * η) (K : ℕ) (z w : ℂ)
    (hbox :
      ∀
        v ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |80 * η|)).support,
        v ∈ dirichletCompletedLFunctionRectangleBox z w)
    (C : ℕ) (hcount : completedZeroMultiplicityCountInRectangle χ hχ z w ≤ (C : ℝ)) :
    ∃ s : Finset ℂ,
      (∀ v,
          v ∈ s ↔
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
                v ≠
              0) ∧
        ρ ∈ s ∧
        (∀ v ∈ s,
          v ∈ Metric.ball c |80 * η| ∧
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
                v ≠
              0) ∧
        ∃
          k ∈
            Finset.range
              (∑ v ∈ s,
                (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                    (Metric.ball c |80 * η|) v).toNat),
          K ≤ K * (k + 1) ∧
            K * (k + 1) ≤ K * C ∧
            (1 /
                  (4 *
                    ((∑ v ∈ s,
                          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                              (Metric.ball c |80 * η|) v).toNat :
                        ℕ) :
                      ℝ))) *
                (1 / (3 * η)) ^ (K * (k + 1)) ≤
              ‖∑ᶠ v,
                  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                          (Metric.ball c |80 * η|) v :
                        ℤ) :
                      ℂ) *
                    (c - v)⁻¹ ^ (K * (k + 1))‖ := by
  classical
  obtain ⟨s, hs, hρmem, hdomain, k, hk, hKlow, hKhigh, hbound⟩ :=
    exists_analytic_local_zero_power_sum_block_lower_bound_of_near
      (fun u _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u) hη hc ρ hρ
      hclose K
  let hfinite := completedLFunction_local_zero_support_finite χ hχ c (80 * η)
  have hsEq : s = hfinite.toFinset := by
    apply Finset.ext
    intro v
    rw [Set.Finite.mem_toFinset]
    rw [hs v]
    simp only [Function.mem_support]
  have hmass :=
    completedLFunction_local_divisor_support_multiplicity_le_rectangle_count χ hχ c (80 * η) z w
      hbox
  have hmass' :
    (∑ v ∈ s,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
              v).toNat :
          ℝ)) ≤
      (C : ℝ) := by
    rw [hsEq]
    exact hmass.trans hcount
  have hmassNat :
    ∑ v ∈ s,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
            v).toNat ≤
      C := by
    exact_mod_cast hmass'
  refine ⟨s, hs, hρmem, hdomain, k, hk, hKlow, ?_, hbound⟩
  have hklt :
    k <
      ∑ v ∈ s,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
            v).toNat :=
    Finset.mem_range.mp hk
  have hindex :
    k + 1 ≤
      ∑ v ∈ s,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
            v).toNat :=
    Nat.succ_le_iff.mpr hklt
  exact Nat.mul_le_mul_left K (hindex.trans hmassNat)

/--
Inputs: a globally analytic function, its nonzero center value, a local zero within `3η`, and a
positive block scale.

Claim: a derivative order whose successor lies in the block from `K` through `K` times the local
total multiplicity has both the near-zero power-sum lower bound and the exact local-factor
decomposition.

Proof: apply the shifted local power-sum estimate and evaluate the local logarithmic-derivative
decomposition at the corresponding derivative order.

Role: connects the shifted finite power block to the analytic derivative used by zero detection.
-/
theorem exists_analytic_local_zero_power_sum_block_derivative_decomposition_of_near {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {η : ℝ} (hη : 0 < η)
    (hc : F c ≠ 0) (ρ : ℂ) (hρ : MeromorphicOn.divisor F (Metric.ball c |80 * η|) ρ ≠ 0)
    (hclose : ‖c - ρ‖ ≤ 3 * η) (K : ℕ) (hK : 0 < K) :
    ∃ s : Finset ℂ,
      (∀ v, v ∈ s ↔ MeromorphicOn.divisor F (Metric.ball c |80 * η|) v ≠ 0) ∧
        ρ ∈ s ∧
        (∀ v ∈ s,
          v ∈ Metric.ball c |80 * η| ∧ MeromorphicOn.divisor F (Metric.ball c |80 * η|) v ≠ 0) ∧
        ∃ n : ℕ,
          K ≤ n + 1 ∧
            n + 1 ≤ K * (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat) ∧
            (1 /
                  (4 *
                    ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) :
                      ℝ))) *
                (1 / (3 * η)) ^ (n + 1) ≤
              ‖∑ᶠ v,
                  ((MeromorphicOn.divisor F (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
                    (c - v)⁻¹ ^ (n + 1)‖ ∧
            ∃ g : ℂ → ℂ,
              AnalyticOnNhd ℂ g (Metric.ball c |80 * η|) ∧
                (∀ u : Metric.ball c |80 * η|, g u ≠ 0) ∧
                iteratedDeriv n (logDeriv F) c =
                  (∑ᶠ u,
                      ((MeromorphicOn.divisor F (Metric.ball c |80 * η|) u : ℤ) : ℂ) *
                        ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - u) ^ (-1 - n : ℤ))) +
                    iteratedDeriv n (logDeriv g) c := by
  obtain ⟨s, hs, hρmem, hdomain, k, hk, hKlow, hKhigh, hbound⟩ :=
    exists_analytic_local_zero_power_sum_block_lower_bound_of_near hFglobal hη hc ρ hρ hclose K
  let n := K * (k + 1) - 1
  have hnplus : n + 1 = K * (k + 1) := by
    dsimp only [n]
    omega
  obtain ⟨g, hg, hgn, hcenter⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition_at_center hFglobal z₀ hz₀ (R := 80 * η)
      (by positivity) hc n
  have hbound' :
    (1 / (4 * ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) : ℝ))) *
        (1 / (3 * η)) ^ (n + 1) ≤
      ‖∑ᶠ v,
          ((MeromorphicOn.divisor F (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
            (c - v)⁻¹ ^ (n + 1)‖ := by
    rw [hnplus]
    exact hbound
  refine ⟨s, hs, hρmem, hdomain, n, ?_, ?_, hbound', g, hg, hgn, hcenter⟩
  · dsimp only [n]
    omega
  · dsimp only [n]
    omega

/--
Inputs: a nontrivial completed Dirichlet `L` function, a counted near zero, and an upper bound for
the multiplicity of the containing rectangle.

Claim: one completed logarithmic-derivative order lies in the fixed-multiple block and has both
the near-zero power-sum lower bound and the exact local-factor decomposition.

Proof: use the rectangle multiplicity bound to cap the local block, then instantiate the generic
center decomposition for the completed function.

Role: exposes the shifted local derivative data at the interface used by the zero-density proof.
-/
theorem exists_completedLFunction_local_zero_power_sum_block_derivative_decomposition_of_near
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {η : ℝ} (hη : 0 < η)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) (ρ : ℂ)
    (hρ :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|) ρ ≠
        0)
    (hclose : ‖c - ρ‖ ≤ 3 * η) (K : ℕ) (hK : 0 < K) (z w : ℂ)
    (hbox :
      ∀
        v ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |80 * η|)).support,
        v ∈ dirichletCompletedLFunctionRectangleBox z w)
    (C : ℕ) (hcount : completedZeroMultiplicityCountInRectangle χ hχ z w ≤ (C : ℝ)) :
    ∃ s : Finset ℂ,
      (∀ v,
          v ∈ s ↔
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
                v ≠
              0) ∧
        ρ ∈ s ∧
        (∀ v ∈ s,
          v ∈ Metric.ball c |80 * η| ∧
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
                v ≠
              0) ∧
        ∃ n : ℕ,
          K ≤ n + 1 ∧
            n + 1 ≤ K * C ∧
            (1 /
                  (4 *
                    ((∑ v ∈ s,
                          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                              (Metric.ball c |80 * η|) v).toNat :
                        ℕ) :
                      ℝ))) *
                (1 / (3 * η)) ^ (n + 1) ≤
              ‖∑ᶠ v,
                  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                          (Metric.ball c |80 * η|) v :
                        ℤ) :
                      ℂ) *
                    (c - v)⁻¹ ^ (n + 1)‖ ∧
            ∃ g : ℂ → ℂ,
              AnalyticOnNhd ℂ g (Metric.ball c |80 * η|) ∧
                (∀ u : Metric.ball c |80 * η|, g u ≠ 0) ∧
                iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) c =
                  (∑ᶠ u,
                      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                              (Metric.ball c |80 * η|) u :
                            ℤ) :
                          ℂ) *
                        ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - u) ^ (-1 - n : ℤ))) +
                    iteratedDeriv n (logDeriv g) c := by
  obtain ⟨s, hs, hρmem, hdomain, k, hk, hKlow, hKhigh, hbound⟩ :=
    exists_completedLFunction_local_zero_power_sum_fixed_multiple_block_of_near χ hχ hη hc ρ hρ
      hclose K z w hbox C hcount
  let n := K * (k + 1) - 1
  have hnplus : n + 1 = K * (k + 1) := by
    dsimp only [n]
    omega
  have h1nz : DirichletCharacter.completedLFunction χ 1 ≠ 0 :=
    dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  have hFglobal : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun u _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u
  obtain ⟨g, hg, hgn, hcenter⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition_at_center hFglobal 1 h1nz (R := 80 * η)
      (by positivity) hc n
  have hbound' :
    (1 /
          (4 *
            ((∑ v ∈ s,
                  (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                      (Metric.ball c |80 * η|) v).toNat :
                ℕ) :
              ℝ))) *
        (1 / (3 * η)) ^ (n + 1) ≤
      ‖∑ᶠ v,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
                  v :
                ℤ) :
              ℂ) *
            (c - v)⁻¹ ^ (n + 1)‖ := by
    rw [hnplus]
    exact hbound
  refine ⟨s, hs, hρmem, hdomain, n, ?_, ?_, hbound', g, hg, hgn, hcenter⟩
  · dsimp only [n]
    omega
  · dsimp only [n]
    omega

/--
Inputs: an entire function, a nonzero center, and a zero in a disk of radius at most `1`.
Claim: The Turán lower bound for the inverse-distance power sum appears in the central higher
logarithmic derivative after subtracting the zero-free factor's contribution.
Proof: Match Turán's exponent `M+1+l` with derivative order `M+l` and rewrite the local zero sum
over its finite support.
Role: permits separate estimation of the analytic-factor error for zero detection.
-/
theorem exists_analytic_local_zero_turan_derivative_decomposition {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hRsmall : |R| ≤ 1) (hc : F c ≠ 0)
    (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support) (M : ℕ) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ∃ g : ℂ → ℂ,
          (∀ u, u ∈ s ↔ (MeromorphicOn.divisor F (Metric.ball c |R|)) u ≠ 0) ∧
            0 < s.card ∧
            (∀ u ∈ s, u ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) u ≠ 0) ∧
            AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
            (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
            ‖∑ u ∈ s, ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ)‖ /
                (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
              ‖∑ᶠ u,
                  ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ) *
                    (c - u)⁻¹ ^ (M + 1 + l)‖ ∧
            iteratedDeriv (M + l) (logDeriv F) c =
              ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
                  (∑ᶠ u,
                    ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ) *
                      (c - u)⁻¹ ^ (M + 1 + l)) +
                iteratedDeriv (M + l) (logDeriv g) c := by
  classical
  obtain ⟨s, hs, hspos, hdomain, ⟨l, hl, hbound⟩⟩ :=
    exists_analytic_local_zero_turan_bound hFglobal hR hRsmall hc hzeros M
  obtain ⟨g, hg, hgn, hcenter⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition_at_center hFglobal z₀ hz₀ hR hc (M + l)
  let U := Metric.ball c |R|
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun u => (d u : ℂ)
  have hsum (f : ℂ → ℂ) : (∑ u ∈ s, m u * f u) = ∑ᶠ u, m u * f u := by
    symm
    apply finsum_eq_sum_of_support_subset _ (s := s)
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    have hmu : m u ≠ 0 := by
      intro hzero
      apply hu
      simp only [hzero, zero_mul]
    exact hs u |>.2 (Int.cast_ne_zero.mp hmu)
  have hbound' :
    ‖∑ u ∈ s, m u‖ / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
      ‖∑ᶠ u, m u * (c - u)⁻¹ ^ (M + 1 + l)‖ := by
    have hsumPower := hsum (fun u => (c - u)⁻¹ ^ (M + 1 + l))
    rw [hsumPower] at hbound
    simpa only [m, d] using hbound
  have hpower :
    (∑ᶠ u, m u * (c - u) ^ (-1 - (M + l : ℕ) : ℤ)) = ∑ᶠ u, m u * (c - u)⁻¹ ^ (M + 1 + l) := by
    apply finsum_congr
    intro u
    rw [zpow_neg_one_sub_add_eq_inv_pow]
  have hcenter' :
    iteratedDeriv (M + l) (logDeriv F) c =
      ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) * (∑ᶠ u, m u * (c - u)⁻¹ ^ (M + 1 + l)) +
        iteratedDeriv (M + l) (logDeriv g) c := by
    have hfactor :
      (∑ᶠ u,
          m u *
            (((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) * (c - u) ^ (-1 - (M + l : ℕ) : ℤ))) =
        ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
          (∑ᶠ u, m u * (c - u) ^ (-1 - (M + l : ℕ) : ℤ)) := by
      calc
        _ =
            ∑ᶠ u,
              ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
                (m u * (c - u) ^ (-1 - (M + l : ℕ) : ℤ)) :=
          by
          apply finsum_congr
          intro u
          calc
            _ =
                (m u * ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ))) *
                  (c - u) ^ (-1 - (M + l : ℕ) : ℤ) :=
              (mul_assoc _ _ _).symm
            _ =
                (((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) * m u) *
                  (c - u) ^ (-1 - (M + l : ℕ) : ℤ) :=
              by rw [mul_comm (m u)]
            _ = _ := mul_assoc _ _ _
        _ = _ := (mul_finsum _ _).symm
    rw [hcenter, hfactor, hpower]
  refine ⟨s, l, hl, g, hs, hspos, hdomain, hg, hgn, ?_, hcenter'⟩
  simpa only [m, d, U] using hbound'

/--
Inputs: a globally analytic function, nonzero center and reference values, and a zero in a local
disk.

Claim: some derivative order among the first total local multiplicity many orders has a
maximum-node reciprocal power-sum lower bound and an exact decomposition into the zero sum and a
zero-free analytic-factor remainder.

Proof: apply the repeated-node maximum estimate to divisor orders, then use the local logarithmic
derivative factorization at the selected derivative order.

Role: carries the multiplicity-sensitive positive zero term into the derivative estimate used by
the zero-detection argument.
-/
theorem exists_analytic_local_zero_max_turan_derivative_decomposition {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hc : F c ≠ 0) (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support) :
    ∃ s : Finset ℂ,
      (∀ v, v ∈ s ↔ MeromorphicOn.divisor F (Metric.ball c |R|) v ≠ 0) ∧
        ∃ u ∈ s,
          (∀ v ∈ s,
              0 < (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat →
                ‖(c - v)⁻¹‖ ≤ ‖(c - u)⁻¹‖) ∧
            1 / |R| ≤ ‖(c - u)⁻¹‖ ∧
            ∃ k ∈ Finset.range (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat),
              ∃ g : ℂ → ℂ,
                (∀ v ∈ s,
                    v ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) v ≠ 0) ∧
                  AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
                  (∀ v : Metric.ball c |R|, g v ≠ 0) ∧
                  (1 /
                        (4 *
                          ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat : ℕ) :
                            ℝ))) *
                      ‖(c - u)⁻¹‖ ^ (k + 1) ≤
                    ‖∑ᶠ v,
                        ((MeromorphicOn.divisor F (Metric.ball c |R|) v : ℤ) : ℂ) *
                          (c - v)⁻¹ ^ (k + 1)‖ ∧
                  iteratedDeriv k (logDeriv F) c =
                    ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
                        (∑ᶠ v,
                          ((MeromorphicOn.divisor F (Metric.ball c |R|) v : ℤ) : ℂ) *
                            (c - v)⁻¹ ^ (k + 1)) +
                      iteratedDeriv k (logDeriv g) c := by
  classical
  obtain ⟨s, hs, u, hu, hmax, hrad, k, hk, hdomain, hbound⟩ :=
    exists_analytic_local_zero_max_reciprocal_power_sum hFglobal hR hc hzeros
  obtain ⟨g, hg, hgn, hcenter⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition_at_center hFglobal z₀ hz₀ hR hc k
  let U := Metric.ball c |R|
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun v => (d v : ℂ)
  have hpower : (∑ᶠ v, m v * (c - v) ^ (-1 - (k : ℕ) : ℤ)) = ∑ᶠ v, m v * (c - v)⁻¹ ^ (k + 1) := by
    apply finsum_congr
    intro v
    rw [zpow_neg_one_sub_nat_eq_inv_pow]
  have hcenter' :
    iteratedDeriv k (logDeriv F) c =
      ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (∑ᶠ v, m v * (c - v)⁻¹ ^ (k + 1)) +
        iteratedDeriv k (logDeriv g) c := by
    have hfactor :
      (∑ᶠ v, m v * (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (c - v) ^ (-1 - (k : ℕ) : ℤ))) =
        ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (∑ᶠ v, m v * (c - v) ^ (-1 - (k : ℕ) : ℤ)) := by
      calc
        _ = ∑ᶠ v, ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (m v * (c - v) ^ (-1 - (k : ℕ) : ℤ)) := by
          apply finsum_congr
          intro v
          calc
            _ = (m v * ((-1 : ℂ) ^ k * (k.factorial : ℂ))) * (c - v) ^ (-1 - (k : ℕ) : ℤ) :=
              (mul_assoc _ _ _).symm
            _ = (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * m v) * (c - v) ^ (-1 - (k : ℕ) : ℤ) := by
              rw [mul_comm (m v)]
            _ = _ := mul_assoc _ _ _
        _ = _ := (mul_finsum _ _).symm
    rw [hcenter, hfactor, hpower]
  refine ⟨s, hs, u, hu, hmax, hrad, k, hk, g, ?_, hg, hgn, ?_, hcenter'⟩
  · intro v hv
    simpa only [U, d] using hdomain v hv
  · simpa only [U, d, m] using hbound

/--
Inputs: a globally analytic function, a nonzero center and reference point, and a zero in the
local divisor support.
Claim: one derivative order has a radius-scaled positive zero-sum lower bound and an exact
decomposition into that zero sum and a zero-free analytic-factor remainder.
Proof: combine the scaled reciprocal power-sum estimate with the local logarithmic-derivative
factorization, matching exponent `M+1+l` to derivative order `M+l`.
Role: connects the near-zero scale to the analytic remainder estimate used in zero detection.
-/
theorem exists_analytic_local_zero_scaled_turan_derivative_decomposition {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hc : F c ≠ 0) (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support)
    (M : ℕ) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ∃ g : ℂ → ℂ,
          (∀ u, u ∈ s ↔ (MeromorphicOn.divisor F (Metric.ball c |R|)) u ≠ 0) ∧
            0 < s.card ∧
            (∀ u ∈ s, u ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) u ≠ 0) ∧
            AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
            (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
            1 / (2 ^ (M + 2 * s.card) * |R| ^ (M + 1 + l)) ≤
              ‖∑ᶠ u,
                  ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ) *
                    (c - u)⁻¹ ^ (M + 1 + l)‖ ∧
            iteratedDeriv (M + l) (logDeriv F) c =
              ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
                  (∑ᶠ u,
                    ((MeromorphicOn.divisor F (Metric.ball c |R|) u : ℤ) : ℂ) *
                      (c - u)⁻¹ ^ (M + 1 + l)) +
                iteratedDeriv (M + l) (logDeriv g) c := by
  classical
  obtain ⟨s, l, hl, hs, hspos, hdomain, hbound⟩ :=
    exists_analytic_local_zero_scaled_reciprocal_power_sum hFglobal hR hc hzeros M
  obtain ⟨g, hg, hgn, hcenter⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition_at_center hFglobal z₀ hz₀ hR hc (M + l)
  let U := Metric.ball c |R|
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun u => (d u : ℂ)
  have hpower :
    (∑ᶠ u, m u * (c - u) ^ (-1 - (M + l : ℕ) : ℤ)) = ∑ᶠ u, m u * (c - u)⁻¹ ^ (M + 1 + l) := by
    apply finsum_congr
    intro u
    rw [zpow_neg_one_sub_add_eq_inv_pow]
  have hcenter' :
    iteratedDeriv (M + l) (logDeriv F) c =
      ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) * (∑ᶠ u, m u * (c - u)⁻¹ ^ (M + 1 + l)) +
        iteratedDeriv (M + l) (logDeriv g) c := by
    have hfactor :
      (∑ᶠ u,
          m u *
            (((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) * (c - u) ^ (-1 - (M + l : ℕ) : ℤ))) =
        ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
          (∑ᶠ u, m u * (c - u) ^ (-1 - (M + l : ℕ) : ℤ)) := by
      calc
        _ =
            ∑ᶠ u,
              ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
                (m u * (c - u) ^ (-1 - (M + l : ℕ) : ℤ)) :=
          by
          apply finsum_congr
          intro u
          calc
            _ =
                (m u * ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ))) *
                  (c - u) ^ (-1 - (M + l : ℕ) : ℤ) :=
              (mul_assoc _ _ _).symm
            _ =
                (((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) * m u) *
                  (c - u) ^ (-1 - (M + l : ℕ) : ℤ) :=
              by rw [mul_comm (m u)]
            _ = _ := mul_assoc _ _ _
        _ = _ := (mul_finsum _ _).symm
    rw [hcenter, hfactor, hpower]
  refine ⟨s, l, hl, g, hs, hspos, hdomain, hg, hgn, ?_, hcenter'⟩
  simpa only [m, d, U] using hbound

/--
Inputs: a nontrivial completed L-function, a zero in a local disk, and a nonzero center.
Claim: the completed logarithmic derivative has a Turán lower-bound decomposition with its local
zero-free analytic factor.
Proof: instantiate the generic analytic-function result.
Role: preserves the interface used by completed-L derivative and gamma-transfer estimates.
-/
theorem exists_completedLFunction_local_zero_turan_derivative_decomposition {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < |R|) (hRsmall : |R| ≤ 1)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hzeros :
      ∃ u,
        u ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |R|)).support)
    (M : ℕ) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ∃ g : ℂ → ℂ,
          (∀ u,
              u ∈ s ↔
                (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                      (Metric.ball c |R|))
                    u ≠
                  0) ∧
            0 < s.card ∧
            (∀ u ∈ s,
              u ∈ Metric.ball c |R| ∧
                MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
                    u ≠
                  0) ∧
            AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
            (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
            ‖∑ u ∈ s,
                    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                          (Metric.ball c |R|) u :
                        ℤ) :
                      ℂ)‖ /
                (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
              ‖∑ᶠ u,
                  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                          (Metric.ball c |R|) u :
                        ℤ) :
                      ℂ) *
                    (c - u)⁻¹ ^ (M + 1 + l)‖ ∧
            iteratedDeriv (M + l) (logDeriv (DirichletCharacter.completedLFunction χ)) c =
              ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
                  (∑ᶠ u,
                    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                            (Metric.ball c |R|) u :
                          ℤ) :
                        ℂ) *
                      (c - u)⁻¹ ^ (M + 1 + l)) +
                iteratedDeriv (M + l) (logDeriv g) c := by
  let F := DirichletCharacter.completedLFunction χ
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have h1nz : F 1 ≠ 0 := dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  obtain ⟨s, l, hl, g, hs, hspos, hdomain, hg, hgn, hbound, hdecomp⟩ :=
    exists_analytic_local_zero_turan_derivative_decomposition hFglobal 1 h1nz hR hRsmall hc hzeros M
  exact
    ⟨s, l, hl, g, by simpa only [F] using hs, hspos,
      (by
        intro u hu; simpa only [F] using hdomain u hu),
      hg, hgn, by simpa only [F] using hbound, by simpa only [F] using hdecomp⟩

/--
Inputs: complex numbers `D`, `S`, and `E` with `D` equal to `(-1)^n n!` times `S` plus `E`, a
lower bound for `‖S‖`, and an upper bound for `‖E‖`.
Claim: `‖D‖` is at least `n!` times the lower bound for the power sum minus the error bound.
Proof: Apply the reverse triangle inequality and use that the coefficient has norm `n!`.
Role: transfers the Turán lower bound for a zero power sum to a lower bound for a
logarithmic-derivative derivative.
-/
theorem norm_derivative_lower_bound_of_zero_sum_decomposition {n : ℕ} {D S E : ℂ} {L R : ℝ}
    (hdecomp : D = ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * S + E) (hlower : L ≤ ‖S‖)
    (herror : ‖E‖ ≤ R) : L * (n.factorial : ℝ) - R ≤ ‖D‖ := by
  let a : ℂ := (-1 : ℂ) ^ n * (n.factorial : ℂ)
  let v : ℂ := a * S
  have hEq : D = v + E := by simpa only [v, a] using hdecomp
  have hsub : v = D - E := by
    rw [hEq]; simp only [add_sub_cancel_right]
  have hfactor : ‖a‖ = (n.factorial : ℝ) := by
    dsimp only [a]
    rw [norm_mul, norm_pow, norm_neg, norm_one, Complex.norm_natCast]
    simp only [one_pow, one_mul]
  have hnorm : ‖v‖ = (n.factorial : ℝ) * ‖S‖ := by
    dsimp only [v]
    rw [norm_mul, hfactor]
  have htriangle : ‖v‖ ≤ ‖D‖ + ‖E‖ := by
    rw [hsub]
    exact norm_sub_le D E
  have hscale : L * (n.factorial : ℝ) ≤ (n.factorial : ℝ) * ‖S‖ := by
    calc
      L * (n.factorial : ℝ) = (n.factorial : ℝ) * L := by ring
      _ ≤ (n.factorial : ℝ) * ‖S‖ :=
        mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg (n.factorial))
  calc
    L * (n.factorial : ℝ) - R ≤ (n.factorial : ℝ) * ‖S‖ - R := sub_le_sub_right hscale R
    _ = ‖v‖ - R := by rw [hnorm]
    _ ≤ ‖D‖ + ‖E‖ - R := by exact sub_le_sub_right htriangle R
    _ ≤ ‖D‖ := by linarith only [herror]

/--
Inputs: a global analytic function, a zero within `3η` of the center, a positive block scale, and
an upper bound for the local zero-free factor's logarithmic-derivative derivatives.
Claim: some derivative order at or above the block scale has the shifted power-sum lower bound,
multiplied by its factorial, minus the factor remainder.
Proof: apply the shifted block decomposition and transfer its power-sum estimate by the reverse
triangle inequality.
Role: connects the shifted power block to a quantitative derivative-detection estimate.
-/
theorem exists_analytic_local_zero_power_sum_block_forces_derivative_lower_bound {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {η : ℝ} (hη : 0 < η)
    (hc : F c ≠ 0) (ρ : ℂ) (hρ : MeromorphicOn.divisor F (Metric.ball c |80 * η|) ρ ≠ 0)
    (hclose : ‖c - ρ‖ ≤ 3 * η) (K : ℕ) (hK : 0 < K) (remainder : ℕ → ℝ)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |80 * η|) →
          (∀ v : Metric.ball c |80 * η|, g v ≠ 0) →
          ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      (∀ v, v ∈ s ↔ MeromorphicOn.divisor F (Metric.ball c |80 * η|) v ≠ 0) ∧
        ∃ u ∈ s,
          ∃ n : ℕ,
            K ≤ n + 1 ∧
              n + 1 ≤ K * (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat) ∧
              (1 /
                      (4 *
                        ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) :
                          ℝ))) *
                    (1 / (3 * η)) ^ (n + 1) *
                    (n.factorial : ℝ) -
                  remainder n ≤
                ‖iteratedDeriv n (logDeriv F) c‖ := by
  obtain ⟨s, hs, hρmem, hdomain, n, hnK, hnMass, hsumLower, g, hg, hgn, hdecomp⟩ :=
    exists_analytic_local_zero_power_sum_block_derivative_decomposition_of_near hFglobal z₀ hz₀ hη
      hc ρ hρ hclose K hK
  let U := Metric.ball c |80 * η|
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun v => (d v : ℂ)
  have hpower : (∑ᶠ v, m v * (c - v) ^ (-1 - (n : ℕ) : ℤ)) = ∑ᶠ v, m v * (c - v)⁻¹ ^ (n + 1) := by
    apply finsum_congr
    intro v
    rw [zpow_neg_one_sub_nat_eq_inv_pow]
  have hcenter' :
    iteratedDeriv n (logDeriv F) c =
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (∑ᶠ v, m v * (c - v)⁻¹ ^ (n + 1)) +
        iteratedDeriv n (logDeriv g) c := by
    have hfactor :
      (∑ᶠ v, m v * (((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (c - v) ^ (-1 - (n : ℕ) : ℤ))) =
        ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (∑ᶠ v, m v * (c - v) ^ (-1 - (n : ℕ) : ℤ)) := by
      calc
        _ = ∑ᶠ v, ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (m v * (c - v) ^ (-1 - (n : ℕ) : ℤ)) := by
          apply finsum_congr
          intro v
          calc
            _ = (m v * ((-1 : ℂ) ^ n * (n.factorial : ℂ))) * (c - v) ^ (-1 - (n : ℕ) : ℤ) :=
              (mul_assoc _ _ _).symm
            _ = (((-1 : ℂ) ^ n * (n.factorial : ℂ)) * m v) * (c - v) ^ (-1 - (n : ℕ) : ℤ) := by
              rw [mul_comm (m v)]
            _ = _ := mul_assoc _ _ _
        _ = _ := (mul_finsum _ _).symm
    rw [hdecomp, hfactor, hpower]
  have hderivative :=
    norm_derivative_lower_bound_of_zero_sum_decomposition hcenter' hsumLower (hremainder n g hg hgn)
  refine ⟨s, hs, ρ, hρmem, n, hnK, hnMass, ?_⟩
  simpa only [U, d, m] using hderivative

/--
Inputs: a nonprincipal completed Dirichlet `L` function, a nearby local zero, a rectangle
containing the local divisor support, and an upper bound for its multiplicity count.
Claim: one derivative order lies between `K` and `K*C`, with the shifted power-sum lower bound
minus the local-factor remainder.
Proof: specialize the analytic-function estimate and use the rectangle multiplicity comparison to
bound the local total multiplicity by `C`.
Role: exposes a derivative-detection estimate with an explicit order range for zero-density work.
-/
theorem exists_completedLFunction_local_zero_power_sum_block_forces_derivative_lower_bound {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {η : ℝ} (hη : 0 < η)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) (ρ : ℂ)
    (hρ :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|) ρ ≠
        0)
    (hclose : ‖c - ρ‖ ≤ 3 * η) (K : ℕ) (hK : 0 < K) (z w : ℂ)
    (hbox :
      ∀
        v ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |80 * η|)).support,
        v ∈ dirichletCompletedLFunctionRectangleBox z w)
    (C : ℕ) (hcount : completedZeroMultiplicityCountInRectangle χ hχ z w ≤ (C : ℝ))
    (remainder : ℕ → ℝ)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |80 * η|) →
          (∀ v : Metric.ball c |80 * η|, g v ≠ 0) →
          ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      ∃ u ∈ s,
        ∃ n : ℕ,
          K ≤ n + 1 ∧
            n + 1 ≤ K * C ∧
            (1 /
                    (4 *
                      ((∑ v ∈ s,
                            (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                                (Metric.ball c |80 * η|) v).toNat :
                          ℕ) :
                        ℝ))) *
                  (1 / (3 * η)) ^ (n + 1) *
                  (n.factorial : ℝ) -
                remainder n ≤
              ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) c‖ := by
  have hglobal : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun v _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt v
  obtain ⟨s, hs, u, hu, n, hnK, hnMass, hderiv⟩ :=
    exists_analytic_local_zero_power_sum_block_forces_derivative_lower_bound hglobal 1
      (dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ) hη hc ρ hρ hclose K hK remainder
      hremainder
  let hfinite := completedLFunction_local_zero_support_finite χ hχ c (80 * η)
  have hsEq : s = hfinite.toFinset := by
    apply Finset.ext
    intro v
    rw [Set.Finite.mem_toFinset]
    rw [hs v]
    simp only [Function.mem_support]
  have hmass :=
    completedLFunction_local_divisor_support_multiplicity_le_rectangle_count χ hχ c (80 * η) z w
      hbox
  have hmass' :
    (∑ v ∈ s,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
              v).toNat :
          ℝ)) ≤
      (C : ℝ) := by
    rw [hsEq]
    exact hmass.trans hcount
  have hmassNat :
    ∑ v ∈ s,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
            v).toNat ≤
      C := by
    exact_mod_cast hmass'
  refine ⟨s, u, hu, n, hnK, ?_, hderiv⟩
  exact hnMass.trans (Nat.mul_le_mul_left K hmassNat)

/--
Inputs: a globally analytic function, a nonzero center value, a zero within `3η`, and upper bounds
for the local zero-free factor's logarithmic-derivative derivatives.

Claim: for some order below the local total multiplicity, the derivative norm is at least
`(k! / (4N)) * (1 / (3η))^(k+1)` minus the remainder bound.

Proof: use the near-zero repeated-node power-sum estimate and the exact local logarithmic
derivative decomposition at the same order, then remove the remainder by the reverse triangle
inequality.

Role: provides the quantitative near-zero derivative estimate used by positive detection.
-/
theorem exists_analytic_local_zero_near_forces_derivative_lower_bound {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {η : ℝ} (hη : 0 < η)
    (hc : F c ≠ 0) (ρ : ℂ) (hρ : MeromorphicOn.divisor F (Metric.ball c |80 * η|) ρ ≠ 0)
    (hclose : ‖c - ρ‖ ≤ 3 * η) (remainder : ℕ → ℝ)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |80 * η|) →
          (∀ v : Metric.ball c |80 * η|, g v ≠ 0) →
          ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      ∃ u ∈ s,
        ∃ k ∈ Finset.range (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat),
          ∃ g : ℂ → ℂ,
            AnalyticOnNhd ℂ g (Metric.ball c |80 * η|) ∧
              (∀ v : Metric.ball c |80 * η|, g v ≠ 0) ∧
              (1 /
                    (4 *
                      ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) :
                        ℝ))) *
                  (1 / (3 * η)) ^ (k + 1) ≤
                ‖∑ᶠ v,
                    ((MeromorphicOn.divisor F (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
                      (c - v)⁻¹ ^ (k + 1)‖ ∧
              ((1 /
                      (4 *
                        ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |80 * η|) v).toNat : ℕ) :
                          ℝ))) *
                    (1 / (3 * η)) ^ (k + 1) *
                    (k.factorial : ℝ) -
                  remainder k) ≤
                ‖iteratedDeriv k (logDeriv F) c‖ := by
  obtain ⟨s, u, hu, k, hk, hsumLower⟩ :=
    exists_analytic_local_zero_power_sum_lower_bound_of_near hFglobal hη hc ρ hρ hclose
  have hRpos : 0 < 80 * η := mul_pos (by norm_num) hη
  have hRabs : 0 < |80 * η| := abs_pos.mpr (ne_of_gt hRpos)
  obtain ⟨g, hg, hgn, hcenter⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition_at_center hFglobal z₀ hz₀ (R := 80 * η)
      hRabs hc k
  let U := Metric.ball c |80 * η|
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun v => (d v : ℂ)
  have hpower : (∑ᶠ v, m v * (c - v) ^ (-1 - (k : ℕ) : ℤ)) = ∑ᶠ v, m v * (c - v)⁻¹ ^ (k + 1) := by
    apply finsum_congr
    intro v
    rw [zpow_neg_one_sub_nat_eq_inv_pow]
  have hcenter' :
    iteratedDeriv k (logDeriv F) c =
      ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (∑ᶠ v, m v * (c - v)⁻¹ ^ (k + 1)) +
        iteratedDeriv k (logDeriv g) c := by
    have hfactor :
      (∑ᶠ v, m v * (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (c - v) ^ (-1 - (k : ℕ) : ℤ))) =
        ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (∑ᶠ v, m v * (c - v) ^ (-1 - (k : ℕ) : ℤ)) := by
      calc
        _ = ∑ᶠ v, ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (m v * (c - v) ^ (-1 - (k : ℕ) : ℤ)) := by
          apply finsum_congr
          intro v
          calc
            _ = (m v * ((-1 : ℂ) ^ k * (k.factorial : ℂ))) * (c - v) ^ (-1 - (k : ℕ) : ℤ) :=
              (mul_assoc _ _ _).symm
            _ = (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * m v) * (c - v) ^ (-1 - (k : ℕ) : ℤ) := by
              rw [mul_comm (m v)]
            _ = _ := mul_assoc _ _ _
        _ = _ := (mul_finsum _ _).symm
    rw [hcenter, hfactor, hpower]
  have hderivative :=
    norm_derivative_lower_bound_of_zero_sum_decomposition hcenter' hsumLower (hremainder k g hg hgn)
  refine ⟨s, u, hu, k, hk, g, ?_, hgn, ?_, hderivative⟩
  · simpa only [U] using hg
  · simpa only [U, d, m] using hsumLower

/--
Inputs: a nonprincipal character, a zero of its completed `L` function within `3η` of the center,
and an upper bound for the local zero-free factor.

Claim: some derivative order below the local total multiplicity has the explicit near-zero lower
bound after subtracting the factor remainder.

Proof: specialize the analytic-function result using the completed `L` function and its value at
`1`, which is nonzero for a nonprincipal character.

Role: exposes the near-zero derivative estimate to the primitive-character density argument.
-/
theorem exists_completedLFunction_local_zero_near_forces_derivative_lower_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {η : ℝ} (hη : 0 < η) (ρ : ℂ)
    (hρ :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|) ρ ≠
        0)
    (hclose : ‖c - ρ‖ ≤ 3 * η) (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (remainder : ℕ → ℝ)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |80 * η|) →
          (∀ v : Metric.ball c |80 * η|, g v ≠ 0) →
          ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      ∃ u ∈ s,
        ∃
          k ∈
            Finset.range
              (∑ v ∈ s,
                (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                    (Metric.ball c |80 * η|) v).toNat),
          ∃ g : ℂ → ℂ,
            AnalyticOnNhd ℂ g (Metric.ball c |80 * η|) ∧
              (∀ v : Metric.ball c |80 * η|, g v ≠ 0) ∧
              (1 /
                    (4 *
                      ((∑ v ∈ s,
                            (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                                (Metric.ball c |80 * η|) v).toNat :
                          ℕ) :
                        ℝ))) *
                  (1 / (3 * η)) ^ (k + 1) ≤
                ‖∑ᶠ v,
                    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                            (Metric.ball c |80 * η|) v :
                          ℤ) :
                        ℂ) *
                      (c - v)⁻¹ ^ (k + 1)‖ ∧
              ((1 /
                      (4 *
                        ((∑ v ∈ s,
                              (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                                  (Metric.ball c |80 * η|) v).toNat :
                            ℕ) :
                          ℝ))) *
                    (1 / (3 * η)) ^ (k + 1) *
                    (k.factorial : ℝ) -
                  remainder k) ≤
                ‖iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) c‖ := by
  let F := DirichletCharacter.completedLFunction χ
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have h1nz : F 1 ≠ 0 := dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  obtain ⟨s, u, hu, k, hk, g, hg, hgn, hsumLower, hderivative⟩ :=
    exists_analytic_local_zero_near_forces_derivative_lower_bound hFglobal 1 h1nz hη hc ρ hρ hclose
      remainder hremainder
  exact
    ⟨s, u, hu, k, hk, g, (by simpa only [F] using hg), hgn, (by simpa only [F] using hsumLower),
      (by simpa only [F] using hderivative)⟩

/--
Inputs: a globally analytic function with a local zero, lower bounds for all derivatives at the
center, and upper bounds for the zero-free-factor remainder.

Claim: some derivative order below the total local multiplicity has a lower bound obtained from
the maximal reciprocal-distance zero term, minus the analytic-factor remainder.

Proof: combine the multiplicity-preserving maximum-node decomposition with the reverse-triangle
estimate for its derivative identity.

Role: makes the new maximum-node power sum available as a quantitative derivative-detection
statement.
-/
theorem exists_analytic_local_zero_max_forces_derivative_lower_bound {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hc : F c ≠ 0) (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support)
    (lower remainder : ℕ → ℝ) (hderivative : ∀ n, lower n ≤ ‖iteratedDeriv n (logDeriv F) c‖)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      (∀ v, v ∈ s ↔ MeromorphicOn.divisor F (Metric.ball c |R|) v ≠ 0) ∧
        ∃ u ∈ s,
          (∀ v ∈ s,
              0 < (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat →
                ‖(c - v)⁻¹‖ ≤ ‖(c - u)⁻¹‖) ∧
            1 / |R| ≤ ‖(c - u)⁻¹‖ ∧
            ∃ k ∈ Finset.range (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat),
              ∃ g : ℂ → ℂ,
                (∀ v ∈ s,
                    v ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) v ≠ 0) ∧
                  AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
                  (∀ v : Metric.ball c |R|, g v ≠ 0) ∧
                  max (lower k)
                      (1 /
                            (4 *
                              ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball c |R|) v).toNat :
                                  ℕ) :
                                ℝ)) *
                          ‖(c - u)⁻¹‖ ^ (k + 1) *
                          (k.factorial : ℝ) -
                        remainder k) ≤
                    ‖iteratedDeriv k (logDeriv F) c‖ := by
  obtain ⟨s, hs, u, hu, hmax, hrad, k, hk, g, hdomain, hg, hgn, hbound, hdecomp⟩ :=
    exists_analytic_local_zero_max_turan_derivative_decomposition hFglobal z₀ hz₀ hR hc hzeros
  have hlower :=
    norm_derivative_lower_bound_of_zero_sum_decomposition hdecomp hbound (hremainder k g hg hgn)
  refine ⟨s, hs, u, hu, hmax, hrad, k, hk, g, hdomain, hg, hgn, ?_⟩
  exact max_le (hderivative k) hlower

/--
Inputs: a nonprincipal Dirichlet character, a local zero of its completed `L` function, derivative
lower bounds, and upper bounds for the local zero-free factor.

Claim: one derivative order below the total local zero multiplicity satisfies both the supplied
derivative bound and the maximum-node lower bound after remainder subtraction.

Proof: instantiate the general analytic-function result using the entire completed `L` function
and its nonvanishing value at `1`.

Role: exposes the multiplicity-preserving maximum-node detection estimate for completed Dirichlet
`L` functions.
-/
theorem exists_completedLFunction_local_zero_max_derivative_lower_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hzeros :
      ∃ u,
        u ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |R|)).support)
    (lower remainder : ℕ → ℝ)
    (hderivative :
      ∀ n, lower n ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) c‖)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      (∀ v,
          v ∈ s ↔
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|) v ≠
              0) ∧
        ∃ u ∈ s,
          (∀ v ∈ s,
              0 <
                  (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                      (Metric.ball c |R|) v).toNat →
                ‖(c - v)⁻¹‖ ≤ ‖(c - u)⁻¹‖) ∧
            1 / |R| ≤ ‖(c - u)⁻¹‖ ∧
            ∃
              k ∈
                Finset.range
                  (∑ v ∈ s,
                    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                        (Metric.ball c |R|) v).toNat),
              ∃ g : ℂ → ℂ,
                (∀ v ∈ s,
                    v ∈ Metric.ball c |R| ∧
                      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                          (Metric.ball c |R|) v ≠
                        0) ∧
                  AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
                  (∀ v : Metric.ball c |R|, g v ≠ 0) ∧
                  max (lower k)
                      (1 /
                            (4 *
                              ((∑ v ∈ s,
                                    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                                        (Metric.ball c |R|) v).toNat :
                                  ℕ) :
                                ℝ)) *
                          ‖(c - u)⁻¹‖ ^ (k + 1) *
                          (k.factorial : ℝ) -
                        remainder k) ≤
                    ‖iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) c‖ := by
  let F := DirichletCharacter.completedLFunction χ
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have h1nz : F 1 ≠ 0 := dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  obtain ⟨s, hs, u, hu, hmax, hrad, k, hk, g, hdomain, hg, hgn, hbound⟩ :=
    exists_analytic_local_zero_max_forces_derivative_lower_bound hFglobal 1 h1nz hR hc hzeros lower
      remainder hderivative hremainder
  exact
    ⟨s,
      (by
        intro v; simpa only [F] using hs v),
      u, hu,
      (by
        intro v hv hmult; simpa only [F] using hmax v hv hmult),
      hrad, k, hk, g,
      (by
        intro v hv; simpa only [F] using hdomain v hv),
      hg, hgn, (by simpa only [F] using hbound)⟩

theorem exists_analytic_local_zero_forces_derivative_lower_bound {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hRsmall : |R| ≤ 1) (hc : F c ≠ 0)
    (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support) (M : ℕ)
    (remainder : ℕ → ℝ)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ∃ g : ℂ → ℂ,
          (∀ u, u ∈ s ↔ (MeromorphicOn.divisor F (Metric.ball c |R|)) u ≠ 0) ∧
            (∀ u ∈ s, u ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) u ≠ 0) ∧
            AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
            (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
            ((1 / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k)) *
                  ((M + l).factorial : ℝ) -
                remainder (M + l)) ≤
              ‖iteratedDeriv (M + l) (logDeriv F) c‖ := by
  classical
  obtain ⟨s, l, hl, g, hs, hspos, hdomain, hg, hgn, hbound, hdecomp⟩ :=
    exists_analytic_local_zero_turan_derivative_decomposition hFglobal z₀ hz₀ hR hRsmall hc hzeros M
  let U := Metric.ball c |R|
  let d : ℂ → ℤ := MeromorphicOn.divisor F U
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro z hz
    exact hFglobal z trivial
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hspos
  have hnonneg : ∀ v ∈ s, 0 ≤ d v := by
    intro v hv
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFanalytic v
  have hdupos : 0 < d u := by
    have hduNonzero := (hdomain u hu).2
    exact lt_of_le_of_ne (hnonneg u hu) (Ne.symm hduNonzero)
  have hsum : 1 ≤ ∑ v ∈ s, d v := by
    have hsingle : d u ≤ ∑ v ∈ s, d v := by
      apply Finset.single_le_sum
      · intro v hv
        exact hnonneg v hv
      · exact hu
    omega
  have hnumCast : (∑ v ∈ s, (d v : ℂ)) = ((∑ v ∈ s, d v : ℤ) : ℂ) := by
    push_cast
    rfl
  have hnumNorm : ‖∑ v ∈ s, (d v : ℂ)‖ = ((∑ v ∈ s, d v : ℤ) : ℝ) := by
    rw [hnumCast, Complex.norm_intCast,
      abs_of_nonneg (by exact_mod_cast (show 0 ≤ ∑ v ∈ s, d v by omega))]
  have hnum : (1 : ℝ) ≤ ‖∑ v ∈ s, (d v : ℂ)‖ := by
    rw [hnumNorm]
    exact_mod_cast hsum
  have hden : 0 < ∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.turan_factor_pos s.card M
      hspos
  have hsumLower :
    (1 / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k)) ≤
      ‖∑ᶠ u, ((MeromorphicOn.divisor F U u : ℤ) : ℂ) * (c - u)⁻¹ ^ (M + 1 + l)‖ := by
    have hnumdiv := div_le_div_of_nonneg_right hnum (le_of_lt hden)
    exact hnumdiv.trans hbound
  have herror := hremainder (M + l) g hg hgn
  have hderiv := norm_derivative_lower_bound_of_zero_sum_decomposition hdecomp hsumLower herror
  exact ⟨s, l, hl, g, hs, hdomain, hg, hgn, hderiv⟩

/--
Inputs: a globally analytic function, a nonzero reference point and center, a local divisor zero,
and an upper bound for the zero-free factor's derivative remainder.
Claim: some derivative of the logarithmic derivative has a lower bound with the disk-radius scale
retained in its zero term.
Proof: combine the scaled local derivative decomposition with the supplied remainder estimate and
the reverse triangle inequality.
Role: turns the radius-sensitive reciprocal power sum into a positive detection threshold once
the analytic-factor error is smaller than that threshold.
-/
theorem exists_analytic_local_zero_scaled_forces_derivative_lower_bound {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 < |R|)
    (hc : F c ≠ 0) (hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball c |R|)).support) (M : ℕ)
    (remainder : ℕ → ℝ)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ∃ g : ℂ → ℂ,
          (∀ u, u ∈ s ↔ (MeromorphicOn.divisor F (Metric.ball c |R|)) u ≠ 0) ∧
            0 < s.card ∧
            (∀ u ∈ s, u ∈ Metric.ball c |R| ∧ MeromorphicOn.divisor F (Metric.ball c |R|) u ≠ 0) ∧
            AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
            (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
            (1 / (2 ^ (M + 2 * s.card) * |R| ^ (M + 1 + l)) * ((M + l).factorial : ℝ) -
                remainder (M + l)) ≤
              ‖iteratedDeriv (M + l) (logDeriv F) c‖ := by
  classical
  obtain ⟨s, l, hl, g, hs, hspos, hdomain, hg, hgn, hsumLower, hdecomp⟩ :=
    exists_analytic_local_zero_scaled_turan_derivative_decomposition hFglobal z₀ hz₀ hR hc hzeros M
  have herror := hremainder (M + l) g hg hgn
  have hderiv := norm_derivative_lower_bound_of_zero_sum_decomposition hdecomp hsumLower herror
  exact ⟨s, l, hl, g, hs, hspos, hdomain, hg, hgn, hderiv⟩

/--
Inputs: a nontrivial completed L-function, a local zero and center, and an analytic-factor error
bound.
Claim: the completed logarithmic derivative has the local Turán lower bound.
Proof: instantiate the generic entire-function result at the completed L-function.
Role: preserves the completed-L interface consumed by gamma-factor transfer estimates.
-/
theorem exists_completedLFunction_local_zero_forces_derivative_lower_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < |R|) (hRsmall : |R| ≤ 1)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hzeros :
      ∃ u,
        u ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |R|)).support)
    (M : ℕ) (remainder : ℕ → ℝ)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ∃ g : ℂ → ℂ,
          (∀ u,
              u ∈ s ↔
                (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                      (Metric.ball c |R|))
                    u ≠
                  0) ∧
            (∀ u ∈ s,
              u ∈ Metric.ball c |R| ∧
                MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
                    u ≠
                  0) ∧
            AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
            (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
            ((1 / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k)) *
                  ((M + l).factorial : ℝ) -
                remainder (M + l)) ≤
              ‖iteratedDeriv (M + l) (logDeriv (DirichletCharacter.completedLFunction χ)) c‖ := by
  let F := DirichletCharacter.completedLFunction χ
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have h1nz : F 1 ≠ 0 := dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  obtain ⟨s, l, hl, g, hs, hdomain, hg, hgn, hbound⟩ :=
    exists_analytic_local_zero_forces_derivative_lower_bound hFglobal 1 h1nz hR hRsmall hc hzeros M
      remainder hremainder
  refine ⟨s, l, hl, g, ?_, ?_, hg, hgn, ?_⟩
  · intro u
    simpa only [F] using hs u
  · intro u hu
    simpa only [F] using hdomain u hu
  · simpa only [F] using hbound

/--
Purpose: packages the finite local zero factorization and its derivative lower bound.
Definition: existentially records the divisor support set, its selected index, the zero-free
analytic remainder, and the resulting lower bound at order `M + l`.
Inputs: a nontrivial character, a center and radius, a base derivative order `M`, and an error
bound.
Output: Turán data for the completed `L` function on the specified ball.
Role: provides a compact result type for passing local zero detection into family estimates.
-/
abbrev CompletedLFunctionLocalDerivativeLowerBoundData {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℂ) (R : ℝ) (M : ℕ) (remainder : ℕ → ℝ) : Prop :=
  ∃ s : Finset ℂ,
    ∃ l ∈ Finset.range s.card,
      ∃ g : ℂ → ℂ,
        (∀ u,
            u ∈ s ↔
              (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|))
                  u ≠
                0) ∧
          (∀ u ∈ s,
            u ∈ Metric.ball c |R| ∧
              MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
                  u ≠
                0) ∧
          AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
          (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
          ((1 / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k)) *
                ((M + l).factorial : ℝ) -
              remainder (M + l)) ≤
            ‖iteratedDeriv (M + l) (logDeriv (DirichletCharacter.completedLFunction χ)) c‖

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: explicit-center completed-L Turán data, its counted zero height, and a remainder bound.
Claim: the Turán derivative lower bound transfers to the ordinary L-function after subtracting
the uniform gamma correction.
Content: the explicit center has real part in `[1,5/4]` and the zero's imaginary part, so the
uniform high-order gamma estimate applies at the same height.
Role: produces the derivative magnitude that the Euler-tail large sieve counts.
-/
theorem ordinary_derivative_lower_bound_of_completed_local_data {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} {ρ c : ℂ} {R : ℝ}
    (hσlower : (29 / 30 : ℝ) ≤ σ) (hσupper : σ ≤ 1) (hσlt : σ < 1) (hT : 0 ≤ T)
    (hρlower : -T ≤ ρ.im) (hρupper : ρ.im ≤ T) (hcre : c.re = 2 - σ) (hcim : c.im = ρ.im) (M : ℕ)
    (remainder : ℕ → ℝ)
    (hdata : CompletedLFunctionLocalDerivativeLowerBoundData χ c R M remainder) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∃ s : Finset ℂ,
          ∃ l ∈ Finset.range s.card,
            ∃ g : ℂ → ℂ,
              (∀ u,
                  u ∈ s ↔
                    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                        (Metric.ball c |R|) u) ≠
                      0) ∧
                (∀ u ∈ s,
                  u ∈ Metric.ball c |R| ∧
                    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                        (Metric.ball c |R|) u ≠
                      0) ∧
                AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
                (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
                ((1 / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k)) *
                      ((M + l).factorial : ℝ) -
                    remainder (M + l) -
                    ((M + l).factorial : ℝ) * C * (Real.log (4 * T + 4) + 1) /
                      (1 / 4 : ℝ) ^ (M + l)) ≤
                  ‖iteratedDeriv (M + l) (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
  obtain ⟨s, l, hl, g, hs, hdomain, hg, hgn, hcompleted⟩ := hdata
  have hslo : 1 ≤ c.re := by
    rw [hcre]
    linarith only [hσupper]
  have hshi : c.re ≤ 5 / 4 := by
    rw [hcre]
    nlinarith only [hσlower]
  have hsstrict : 1 < c.re := by
    rw [hcre]
    linarith only [hσlt]
  have hsi : |c.im| ≤ T := by
    rw [hcim]
    exact abs_le.mpr ⟨hρlower, hρupper⟩
  obtain ⟨C, hC, htransfer⟩ :=
    exists_uniform_gamma_subtraction_for_ordinary_LFunction_derivative (M + l)
  have hordinary := htransfer hχ hsstrict hslo hshi hT hsi hcompleted
  exact ⟨C, hC, s, l, hl, g, hs, hdomain, hg, hgn, hordinary⟩

/--
Inputs: a nontrivial character, positive completed-zero count, a base derivative order, and a
remainder bound uniform over all local centers and radii.
Claim: some zero in the counted rectangle supplies local Turán derivative data in a ball of radius
at most one with nonzero center.
Content: use the local support output of the positive-count theorem, then apply the existing
completed-function derivative lower bound on that ball.
Proof: normalize the positive radius to the absolute-value convention used by the local theorem.
Role: connects completed-zero counting directly to a derivative-value input for the family large
sieve.
-/
theorem exists_completedZeroCount_local_derivative_lower_bound_of_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hσ : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T)
    (M : ℕ) (remainder : ℕ → ℝ)
    (hremainder :
      ∀ (c : ℂ) (R : ℝ) n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          ∃ R : ℝ,
            0 < R ∧
              R ≤ 1 ∧
              DirichletCharacter.completedLFunction χ c ≠ 0 ∧
              CompletedLFunctionLocalDerivativeLowerBoundData χ c R M remainder := by
  obtain ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hR, hRle, hc, hsupport⟩ :=
    exists_completedZeroCount_local_support_of_pos χ hχ hσ hT hcount
  have hR' : 0 < |R| := by simpa only [abs_of_pos hR] using hR
  have hRsmall : |R| ≤ 1 := by simpa only [abs_of_pos hR] using hRle
  have hzeros :
    ∃ u,
      u ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c |R|)).support :=
    ⟨ρ, hsupport⟩
  have hdata :=
    exists_completedLFunction_local_zero_forces_derivative_lower_bound χ hχ hR' hRsmall hc hzeros M
      remainder (fun n g hg hgn => hremainder c R n g hg hgn)
  exact ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hR, hRle, hc, hdata⟩

/--
Inputs: a nontrivial character, positive completed-zero count with `3/4 ≤ σ ≤ 1`, a base
derivative order, and a remainder bound valid on every zero-free local analytic factor.
Claim: a counted zero yields Turán derivative data at the explicit center `re c = 2 - σ` and
radius `4(1 - σ)`.
Content: unlike the arbitrary-neighborhood version, the center's real part and local radius are
fixed by `σ`; the derivative order may still depend on the local divisor support.
Proof: use the explicit local-support theorem and apply the completed-function derivative bound
with the supplied uniform remainder estimate.
Role: provides the most controlled local input currently available for a uniform zero-density
argument.
-/
theorem exists_completedZeroCount_explicit_local_derivative_lower_bound_of_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hσlower : (3 / 4 : ℝ) ≤ σ)
    (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T)
    (M : ℕ) (remainder : ℕ → ℝ)
    (hremainder :
      ∀ (c : ℂ) (R : ℝ) n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          ∃ R : ℝ,
            R = 4 * (1 - σ) ∧
              0 < R ∧
              R ≤ 1 ∧
              c.re = 2 - σ ∧
              c.im = ρ.im ∧
              DirichletCharacter.completedLFunction χ c ≠ 0 ∧
              CompletedLFunctionLocalDerivativeLowerBoundData χ c R M remainder := by
  obtain
    ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hRdef, hR, hRle, hcre, hcim, hc, hsupport⟩ :=
    exists_completedZeroCount_explicit_local_support_of_pos χ hχ hσlower hσupper hT hcount
  have hR' : 0 < |R| := by simpa only [abs_of_pos hR] using hR
  have hRsmall : |R| ≤ 1 := by simpa only [abs_of_pos hR] using hRle
  have hzeros :
    ∃ u,
      u ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c |R|)).support :=
    ⟨ρ, hsupport⟩
  have hdata :=
    exists_completedLFunction_local_zero_forces_derivative_lower_bound χ hχ hR' hRsmall hc hzeros M
      remainder (fun n g hg hgn => hremainder c R n g hg hgn)
  exact ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hRdef, hR, hRle, hcre, hcim, hc, hdata⟩

/--
Inputs: a nontrivial character, positive zero count with `29/30 ≤ σ ≤ 1`, a base derivative order,
and a remainder bound uniform over zero-free local analytic factors.
Claim: the explicit-center Turán derivative data and a conductor-height logarithmic bound for its
local divisor support are available at the same zero and center.
Content: this bounds the variable support cardinality that determines the derivative order range.
Proof: combine the explicit derivative lower-bound theorem with the real-part-two Jensen estimate.
Role: packages the local zero detection and its finite-order cost for a later family estimate.
-/
theorem exists_completedZeroCount_explicit_local_derivative_lower_bound_with_card_bound_of_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hq : 1 < q)
    (hσlower : (29 / 30 : ℝ) ≤ σ) (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T)
    (M : ℕ) (remainder : ℕ → ℝ)
    (hremainder :
      ∀ (c : ℂ) (R : ℝ) n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          ∃ R : ℝ,
            R = 4 * (1 - σ) ∧
              0 < R ∧
              R ≤ 1 ∧
              c.re = 2 - σ ∧
              c.im = ρ.im ∧
              DirichletCharacter.completedLFunction χ c ≠ 0 ∧
              CompletedLFunctionLocalDerivativeLowerBoundData χ c R M remainder ∧
              (((completedLFunction_local_zero_support_finite χ hχ c R).toFinset.card : ℕ) : ℝ) ≤
                Real.log (2 * max (1 : ℝ) (2 * (q : ℝ) * (‖(2 + Complex.I * c.im : ℂ)‖ + 3 / 2))) /
                  Real.log (9 / 8) := by
  obtain ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hRdef, hR, hRle, hcre, hcim, hc, hdata⟩ :=
    exists_completedZeroCount_explicit_local_derivative_lower_bound_of_pos χ hχ
      (le_trans (by norm_num only : (3 / 4 : ℝ) ≤ 29 / 30) hσlower) hσupper hT hcount M remainder
      hremainder
  have hσlt : σ < 1 := by
    have hpos : 0 < 4 * (1 - σ) := by
      rw [← hRdef]; exact hR
    nlinarith only [hpos]
  have hcard :=
    completedLFunction_explicit_local_divisor_support_card_le_log_bound χ hχ hq hσlower hσlt c hcre
  have hcard' :
    (((completedLFunction_local_zero_support_finite χ hχ c R).toFinset.card : ℕ) : ℝ) ≤
      Real.log (2 * max (1 : ℝ) (2 * (q : ℝ) * (‖(2 + Complex.I * c.im : ℂ)‖ + 3 / 2))) /
        Real.log (9 / 8) := by
    subst R
    exact hcard
  exact
    ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hRdef, hR, hRle, hcre, hcim, hc, hdata, hcard'⟩

/--
Inputs: complex numbers `D`, `S`, and `E` with `D` equal to `(-1)^n n!` times `S` plus `E`, a
lower bound for `‖D‖`, and an upper bound for `‖E‖`.
Claim: The norm of the power sum is at least the difference between the derivative lower bound
and the error bound, divided by `n!`.
Proof: Use the triangle inequality to subtract the error and transfer the lower bound using the
coefficient norm `n!`.
Role: connects the local zero factorization and analytic-factor estimate to a power-sum lower
bound for zero detection.
-/
theorem norm_zero_sum_lower_bound_of_derivative_decomposition {n : ℕ} {D S E : ℂ} {L R : ℝ}
    (hdecomp : D = ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * S + E) (hlower : L ≤ ‖D‖)
    (herror : ‖E‖ ≤ R) : (L - R) / (n.factorial : ℝ) ≤ ‖S‖ := by
  let a : ℂ := (-1 : ℂ) ^ n * (n.factorial : ℂ)
  let v : ℂ := a * S
  have hEq : D = v + E := by simpa only [v, a] using hdecomp
  have htriangle : ‖D‖ ≤ ‖v‖ + ‖E‖ := by
    rw [hEq]
    exact norm_add_le v E
  have hv : L - R ≤ ‖v‖ := by linarith only [hlower, herror, htriangle]
  have hfactor : ‖a‖ = (n.factorial : ℝ) := by
    dsimp only [a]
    rw [norm_mul, norm_pow, norm_neg, norm_one, Complex.norm_natCast]
    simp only [one_pow, one_mul]
  have hF : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnorm : ‖v‖ = (n.factorial : ℝ) * ‖S‖ := by
    dsimp only [v]
    rw [norm_mul, hfactor]
  apply (div_le_iff₀ hF).2
  calc
    L - R ≤ ‖v‖ := hv
    _ = (n.factorial : ℝ) * ‖S‖ := hnorm
    _ = ‖S‖ * (n.factorial : ℝ) := mul_comm _ _

/--
Inputs: the completed `L` function of a nontrivial character, a zero in the disk, derivative
lower bounds at every order, and upper bounds for logarithmic-derivative derivatives of the
zero-free local factor.
Claim: At the order selected by the Turán decomposition, the multiplicity-weighted local zero
power sum has an explicit lower bound.
Proof: Extract the existing Turán-type local decomposition and pass the analytic-factor error
bound to the coefficient-removal lemma.
Role: provides an interface for detecting local zeros from derivative estimates.
-/
theorem exists_completedLFunction_local_zero_turan_detected_lower_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < |R|) (hRsmall : |R| ≤ 1)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hzeros :
      ∃ u,
        u ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |R|)).support)
    (M : ℕ) (lower remainder : ℕ → ℝ)
    (hderivative :
      ∀ n, lower n ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) c‖)
    (hremainder :
      ∀ n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ∃ g : ℂ → ℂ,
          (∀ u,
              u ∈ s ↔
                (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                      (Metric.ball c |R|))
                    u ≠
                  0) ∧
            0 < s.card ∧
            (∀ u ∈ s,
              u ∈ Metric.ball c |R| ∧
                MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
                    u ≠
                  0) ∧
            AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
            (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
            ‖∑ u ∈ s,
                    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                          (Metric.ball c |R|) u :
                        ℤ) :
                      ℂ)‖ /
                (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
              ‖∑ᶠ u,
                  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                          (Metric.ball c |R|) u :
                        ℤ) :
                      ℂ) *
                    (c - u)⁻¹ ^ (M + 1 + l)‖ ∧
            (lower (M + l) - remainder (M + l)) / ((M + l).factorial : ℝ) ≤
              ‖∑ᶠ u,
                  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                          (Metric.ball c |R|) u :
                        ℤ) :
                      ℂ) *
                    (c - u)⁻¹ ^ (M + 1 + l)‖ := by
  obtain ⟨s, l, hl, g, hs, hspos, hdomain, hg, hgn, hbound, hdecomp⟩ :=
    exists_completedLFunction_local_zero_turan_derivative_decomposition χ hχ hR hRsmall hc hzeros M
  have hzeroSum :=
    norm_zero_sum_lower_bound_of_derivative_decomposition hdecomp (hderivative (M + l))
      (hremainder (M + l) g hg hgn)
  exact ⟨s, l, hl, g, hs, hspos, hdomain, hg, hgn, hbound, hzeroSum⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
