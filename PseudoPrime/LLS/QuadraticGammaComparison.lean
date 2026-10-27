/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSubgroupComparison
public import PseudoPrime.NumberTheory.QuadraticCharacterKernel

/-! # Gamma comparisons for nonprincipal quadratic characters at the original level -/

@[expose] public section

namespace PseudoPrime.LLS

open PseudoPrime.LLS.PaperStatements in
/-- Under GRH at q≥20000, a nonprincipal quadratic character trivial on eligible
primes through lambda*x satisfies the explicit index-two Gamma inequality.
Its unit kernel has index two; the signed primitive average bounds the conductor cost by log(q).
The original-level finite modulus loss is retained, including the excluded prime two.
This is the analytic input for direct quadratic witness bounds at level 4n. -/
theorem gamma_inequality_of_quadratic_prime_trivial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 20000 ≤ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 1 ≤ x)
    (hl : 0 ≤ lambda) (hcut : 1 ≤ lambda * x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → χ p = 1) :
    (1 - 2 * Real.exp (-lambda)) * Real.sqrt x ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 39 * x ^ (1 / 4 : ℝ) + 39 +
        (10002 * Real.log q + 10004) / Real.sqrt x +
        2 * (Real.log q * Real.log (lambda * x) / (Real.log 2 * Real.sqrt x)) := by
  let H := χ.toUnitHom.ker
  have hi : H.index = 2 := NumberTheory.index_ker_toUnitHom_of_quadratic_ne_one χ hquad hne
  have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p := by
    intro p hp hd hb
    have hu : IsUnit (p : ZMod q) :=
      (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd)
    refine ⟨hu.unit, ?_, IsUnit.unit_spec hu⟩
    change χ.toUnitHom hu.unit = 1
    apply Units.ext
    simpa only [MulChar.coe_toUnitHom, IsUnit.unit_spec, Units.val_one] using hsmall p hp hd hb
  have hcmp := gamma_noSmallPrimes_explicit_inequality hq H hGRH hx hl hcut ht
  have hc := subgroupConductorLogSum_le H
  norm_num only [hi] at hcmp hc
  have hm := mul_le_mul_of_nonneg_left hc (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hcmp, hm]

end PseudoPrime.LLS
