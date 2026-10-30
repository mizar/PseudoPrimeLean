/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.ConductorRatioBounds
public import PseudoPrime.LLS.RationalPoleCertificates

/-! # Certified rational-pole least-prime bounds under GRH -/

@[expose] public section
namespace PseudoPrime.LLS.PaperStatements.MellinKernel
/-- Under GRH, a strict unit-cutoff kernel certificate with coefficient c yields
a uniform strict c log(q) ^ 2 bound for the least prime outside an index-h subgroup.
Choose an intermediate coefficient inside the strict gap, then absorb the positive
ambient allowance using the universal conductor sum bound. The threshold is uniform
in the modulus and subgroup; no unproved analytic estimate is an input. -/
theorem least_prime_bound_of_strict_certificate (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h : ℕ} (hh : 1 < h)
    {c : ℝ}
    (hA : 0 < (h : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (K.transform u).re / Real.sqrt u) -
      (K.function (1 / 2)).re)
    (hcert : (((h : ℝ) - 1) * K.mass) ^ 2 <
      c * ((h : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (K.transform u).re / Real.sqrt u) -
        (K.function (1 / 2)).re) ^ 2) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = h → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) < c * (Real.log q) ^ 2 := by
  let A := (h : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (K.transform u).re / Real.sqrt u) -
    (K.function (1 / 2)).re
  have hs : 0 < A^2 := sq_pos_of_pos hA
  have hr : (((h : ℝ) - 1) * K.mass) ^ 2 / A^2 < c := (div_lt_iff₀ hs).mpr hcert
  obtain ⟨c₀, hlow, hhigh⟩ := exists_between hr
  have hc₀ : 0 < c₀ :=
    (div_nonneg (sq_nonneg _) hs.le).trans_lt hlow
  have hcert₀ : (((h : ℝ) - 1) * K.mass) ^ 2 < c₀ * A^2 := (div_lt_iff₀ hs).mp hlow
  obtain ⟨Q,hQ,hb⟩ := least_prime_bound_of_conductor_ratio hh hc₀ zero_le_one
    (by simpa only [one_pow,mul_one] using hhigh)
    (fun ε hε ↦ (least_prime_bound_of_conductor_certificate K) hg hh zero_lt_one hc₀ hε hA
      (by simpa only [one_mul] using hcert₀))
  refine ⟨Q,hQ,?_⟩
  intro q _ hq H hi
  apply hb q hq H hi
  simpa only [one_mul, hi] using subgroupConductorLogSum_le H
end PseudoPrime.LLS.PaperStatements.MellinKernel
namespace PseudoPrime.LLS.PaperStatements
/-- Under GRH, the certified rational-pole kernel gives a conductor-sensitive
least-outside-prime radius for every positive ambient allowance. The threshold is
uniform over moduli and index-two subgroups. Retain the ambient logarithmic error term,
including when the primitive conductors stay bounded. -/
theorem rationalPole_quadratic_conductor
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 2 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤
          (Real.sqrt (777/1000) / ((2 : ℝ) - 1) * subgroupConductorLogSum H +
            ε * Real.log q) ^ 2 := by
  exact (MellinKernel.least_prime_bound_of_conductor_certificate rationalPoleFourKernel) hg
    (by norm_num only : 1 < 2) zero_lt_one (by norm_num only) hε
    rationalPole_quadratic_certificate.1
    (by simpa only [one_mul, Nat.cast_ofNat] using rationalPole_quadratic_certificate.2)
/-- Under GRH, the rational-pole certificate yields its strict rational leading
coefficient times log(q) ^ 2 for all sufficiently large moduli, uniformly over subgroups
of the stated index. Apply the actual admissible kernel and absorb the strict margin.
The theorem asserts existence of a threshold, without a numerical finite entrance. -/
theorem rationalPole_quadratic_prime_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 2 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) < (777/1000) * (Real.log q) ^ 2 := by
  exact (MellinKernel.least_prime_bound_of_strict_certificate rationalPoleFourKernel) hg
    (by norm_num only : 1 < 2) rationalPole_quadratic_certificate.1
      rationalPole_quadratic_certificate.2
end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements
/-- Under GRH, the certified rational-pole kernel gives a conductor-sensitive
least-outside-prime radius for every positive ambient allowance. The threshold is
uniform over moduli and index-four subgroups. Retain the ambient logarithmic error term,
including when the primitive conductors stay bounded. -/
theorem rationalPole_index_four_conductor
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 4 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤
          (Real.sqrt (623/1000) / ((4 : ℝ) - 1) * subgroupConductorLogSum H +
            ε * Real.log q) ^ 2 := by
  exact (MellinKernel.least_prime_bound_of_conductor_certificate rationalPoleSixKernel) hg
    (by norm_num only : 1 < 4) zero_lt_one (by norm_num only) hε
    rationalPole_index_four_certificate.1
    (by simpa only [one_mul, Nat.cast_ofNat] using rationalPole_index_four_certificate.2)
/-- Under GRH, the rational-pole certificate yields its strict rational leading
coefficient times log(q) ^ 2 for all sufficiently large moduli, uniformly over subgroups
of the stated index. Apply the actual admissible kernel and absorb the strict margin.
The theorem asserts existence of a threshold, without a numerical finite entrance. -/
theorem rationalPole_index_four_prime_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 4 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) < (623/1000) * (Real.log q) ^ 2 := by
  exact (MellinKernel.least_prime_bound_of_strict_certificate rationalPoleSixKernel) hg
    (by norm_num only : 1 < 4) rationalPole_index_four_certificate.1
      rationalPole_index_four_certificate.2
end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements
/-- Under GRH, the certified rational-pole kernel gives a conductor-sensitive
least-outside-prime radius for every positive ambient allowance. The threshold is
uniform over moduli and index-five subgroups. Retain the ambient logarithmic error term,
including when the primitive conductors stay bounded. -/
theorem rationalPole_index_five_conductor
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 5 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤
          (Real.sqrt (23/40) / ((5 : ℝ) - 1) * subgroupConductorLogSum H +
            ε * Real.log q) ^ 2 := by
  exact (MellinKernel.least_prime_bound_of_conductor_certificate rationalPoleSixKernel) hg
    (by norm_num only : 1 < 5) zero_lt_one (by norm_num only) hε
    rationalPole_index_five_certificate.1
    (by simpa only [one_mul, Nat.cast_ofNat] using rationalPole_index_five_certificate.2)
/-- Under GRH, the rational-pole certificate yields its strict rational leading
coefficient times log(q) ^ 2 for all sufficiently large moduli, uniformly over subgroups
of the stated index. Apply the actual admissible kernel and absorb the strict margin.
The theorem asserts existence of a threshold, without a numerical finite entrance. -/
theorem rationalPole_index_five_prime_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 5 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) < (23/40) * (Real.log q) ^ 2 := by
  exact (MellinKernel.least_prime_bound_of_strict_certificate rationalPoleSixKernel) hg
    (by norm_num only : 1 < 5) rationalPole_index_five_certificate.1
      rationalPole_index_five_certificate.2
end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements
/-- Under GRH, the certified rational-pole kernel gives a conductor-sensitive
least-outside-prime radius for every positive ambient allowance. The threshold is
uniform over moduli and index-six subgroups. Retain the ambient logarithmic error term,
including when the primitive conductors stay bounded. -/
theorem rationalPole_index_six_conductor
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 6 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤
          (Real.sqrt (549/1000) / ((6 : ℝ) - 1) * subgroupConductorLogSum H +
            ε * Real.log q) ^ 2 := by
  exact (MellinKernel.least_prime_bound_of_conductor_certificate rationalPoleSixKernel) hg
    (by norm_num only : 1 < 6) zero_lt_one (by norm_num only) hε
    rationalPole_index_six_certificate.1
    (by simpa only [one_mul, Nat.cast_ofNat] using rationalPole_index_six_certificate.2)
/-- Under GRH, the rational-pole certificate yields its strict rational leading
coefficient times log(q) ^ 2 for all sufficiently large moduli, uniformly over subgroups
of the stated index. Apply the actual admissible kernel and absorb the strict margin.
The theorem asserts existence of a threshold, without a numerical finite entrance. -/
theorem rationalPole_index_six_prime_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 6 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) < (549/1000) * (Real.log q) ^ 2 := by
  exact (MellinKernel.least_prime_bound_of_strict_certificate rationalPoleSixKernel) hg
    (by norm_num only : 1 < 6) rationalPole_index_six_certificate.1
      rationalPole_index_six_certificate.2
end PseudoPrime.LLS.PaperStatements
