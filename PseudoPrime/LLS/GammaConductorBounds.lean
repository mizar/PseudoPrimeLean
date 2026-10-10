/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorSumComparison
public import PseudoPrime.LLS.GammaKernelMass
public import PseudoPrime.LLS.SmallIndexGammaNumerics

/-! # Gamma-kernel bounds retaining primitive conductors

A positive numerical certificate gives a least-prime bound in terms of the
exact conductor-logarithm sum, with arbitrarily small ambient error.
The index-four specialization supplies the small-index conductor comparison.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A gamma-kernel numerical certificate bounds least outside primes while
retaining the sum of primitive-conductor logarithms. Its mass majorant is
4710471/10000000; the certificate implies the actual-mass certificate.
GRH then gives the conductor coefficient sqrt c / (h-1), with any positive
ambient logarithmic allowance, uniformly over subgroups of index h. -/
theorem gamma_prime_bound_of_conductor_certificate
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 1 < h) {l c ε : ℝ}
    (hl : 0 < l) (hc : 0 < c) (hε : 0 < ε) (hden : 0 < (h : ℝ) - 1 - h * Real.exp (-l))
    (hcert :
      l * (((h : ℝ) - 1) * (4710471 / 10000000)) ^ 2 < c * ((h : ℝ) - 1 - h * Real.exp (-l)) ^ 2) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ),
              H.index = h →
                ∃ p : ℕ,
                  IsLeast (primesOutside q H) p ∧
                    (p : ℝ) ≤
                      (Real.sqrt c / ((h : ℝ) - 1) * subgroupConductorLogSum H + ε * Real.log q) ^
                        2 := by
  have hf : gammaMellinKernel.function = fun s : ℂ ↦ Complex.Gamma (s + 1 / 2) := rfl
  have hv := gamma_endpoint_of_function gammaMellinKernel hf
  have hi :
    (∫ u in (0 : ℝ)..l, (gammaMellinKernel.transform u).re / Real.sqrt u) = 1 - Real.exp (-l) := by
    rw [← integral_gammaKernelProfile hl]
    apply intervalIntegral.integral_congr_Ioo_of_le hl.le
    intro u hu
    exact
      congrArg (fun r : ℝ ↦ r / Real.sqrt u) (gamma_transform_of_function gammaMellinKernel hf hu.1)
  have hcoef :
    (h : ℝ) * (∫ u in (0 : ℝ)..l, (gammaMellinKernel.transform u).re / Real.sqrt u) -
        (gammaMellinKernel.function (1 / 2)).re =
      (h : ℝ) - 1 - h * Real.exp (-l) := by
    rw [hi, hv]
    ring
  apply MellinKernel.least_prime_bound_of_conductor_certificate gammaMellinKernel hg hh hl hc hε
  · rw [hcoef]
    exact hden
  · rw [hcoef]
    have hhR : (1 : ℝ) < h := by exact_mod_cast hh
    have hm : gammaMellinKernel.mass ≤ (4710471 / 10000000 : ℝ) :=
      gammaMellinKernel_mass_le.trans (by norm_num only)
    have hu := mul_le_mul_of_nonneg_left hm (sub_pos.mpr hhR).le
    have hs :=
      mul_self_le_mul_self
        (mul_nonneg (sub_pos.mpr hhR).le (MellinKernel.mass_pos gammaMellinKernel).le) hu
    have hs' :
      (((h : ℝ) - 1) * gammaMellinKernel.mass) ^ 2 ≤
        (((h : ℝ) - 1) * (4710471 / 10000000)) ^ 2 := by
      simpa only [← pow_two] using hs
    exact (mul_le_mul_of_nonneg_left hs' hl.le).trans_lt hcert

/-- Under GRH, the refined index-4 gamma certificate gives the exact
conductor-sum coefficient sqrt(6571 / 10000) / 3, with any positive ambient
logarithmic allowance. The common threshold is uniform in all subgroups
of that index and all primitive conductors. -/
theorem gamma_conductor_bound_of_index_four
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ),
              H.index = 4 →
                ∃ p : ℕ,
                  IsLeast (primesOutside q H) p ∧
                    (p : ℝ) ≤
                      (Real.sqrt (6571 / 10000) / ((4 : ℝ) - 1) * subgroupConductorLogSum H +
                          ε * Real.log q) ^
                        2 := by
  apply
    gamma_prime_bound_of_conductor_certificate hg 4 (by norm_num only) (l := (11 / 6 : ℝ)) (c :=
      (6571 / 10000 : ℝ)) (by norm_num only) (by norm_num only) hε
  · have he := gamma_four_small_denominator_exp_bound
    norm_num only
    linarith only [he]
  · have hc := gamma_four_small_denominator_coefficient
    norm_num only at hc ⊢
    exact hc

end PseudoPrime.LLS.PaperStatements
