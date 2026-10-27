/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedEulerIdentity

/-! # Exact ramified correction in the signed Gamma prefix -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- If the character is one on every unit in the prefix, its local correction
is exactly the common Mangoldt weight summed over nonunits. A character
vanishes on nonunits, so no correction is silently discarded. This reduces
the signed prefix loss to ramified inputs before prime-power grouping. -/
theorem gamma_prefix_correction_eq_nonunit_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (B : Finset ℕ)
    (hB : ∀ n ∈ B, Nat.Coprime n q → χ n = 1) :
    (∑ n ∈ B, (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n) =
      ∑ n ∈ B, if Nat.Coprime n q then 0 else Analysis.gammaResolventMangoldtWeight n := by
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hu : Nat.Coprime n q
  · rw [ite_eq_left hu, hB n hn hu, Complex.one_re, sub_self, zero_mul]
  · have hnu : ¬IsUnit (n : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using hu
    rw [ite_eq_right hu, χ.map_nonunit hnu, Complex.zero_re, sub_zero, one_mul]

/-- For primitive conductor data under individual RH and a prefix whose units
all have character value one, the zero-mass prefix inequality has precisely
the noncoprime correction. Apply the established signed prefix inequality and
the exact correction identity. This exposes the ramified loss for local bounds. -/
theorem gammaResolvent_zeroMass_le_ramified_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (B : Finset ℕ) (hB : ∀ n ∈ B, Nat.Coprime n q → χ n = 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) ≤
      (11783423 / 25000000 : ℝ) * Real.log q +
            (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) -
          2 * (∑ n ∈ B, Analysis.gammaResolventMangoldtWeight n) +
        ∑ n ∈ B, if Nat.Coprime n q then 0 else Analysis.gammaResolventMangoldtWeight n := by
  have h := gammaResolvent_zeroMass_le_signed_prefix hq hRH hp hne hinv B
  rw [gamma_prefix_correction_eq_nonunit_sum χ B hB] at h
  exact h

/-- At a positive power of a prime, the ramified correction is present exactly
when that prime divides the conductor. Coprimality of a positive prime power
is equivalent to coprimality of its base. This identifies the local prime
condition for grouping the prefix correction into conductor costs. -/
theorem gamma_primePower_ramified_correction_eq {q p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (if Nat.Coprime (p ^ k) q then 0 else Analysis.gammaResolventMangoldtWeight (p ^ k)) =
      if p ∣ q then Analysis.gammaResolventMangoldtWeight (p ^ k) else 0 := by
  simp only [Nat.coprime_pow_left_iff hk, Nat.Prime.coprime_iff_not_dvd hp]
  by_cases h : p ∣ q
  · rw [ite_eq_right (not_not.mpr h), ite_eq_left h]
  · rw [ite_eq_left h, ite_eq_right h]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
