/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TightCubicConductorBounds

/-! # Cubic witness bounds with cutoff-localized exclusion costs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Product of the distinct prime divisors of M not exceeding the real cutoff X.
The empty product is one, so this exclusion modulus is always nonzero.
Primes extracted below X avoid M as soon as they avoid this smaller modulus. -/
noncomputable def truncatedExclusionModulus (M : ℕ) (X : ℝ) : ℕ :=
  ∏ p ∈ M.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ X), p

/-- Character-sensitive exclusion cost restricted to prime divisors at most X.
The level f is independent of the excluded integer M. This finite sum replaces
full support costs in the cubic fixed-point criterion. -/
noncomputable def truncatedCharacterExclusionCost {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ)
    (X : ℝ) : ℝ :=
  ∑ p ∈ M.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ X), (1 - (χ p).re) * Real.log p

/-- The cutoff-localized exclusion modulus is nonzero for every M and X.
Every factor is prime and hence nonzero. This permits cubic extraction. -/
theorem truncatedExclusionModulus_ne_zero (M : ℕ) (X : ℝ) : truncatedExclusionModulus M X ≠ 0 := by
  classical
    exact
    Finset.prod_ne_zero_iff.mpr
      (fun p hp ↦ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)

/-- For nonzero M, every prime divisor p of M below X divides the localized
modulus. Membership in the filtered prime-factor set gives divisibility of
its product. This transfers avoidance of the localized modulus to M. -/
theorem dvd_truncatedExclusionModulus {M p : ℕ} (hM : M ≠ 0) (hp : p.Prime) (hd : p ∣ M) {X : ℝ}
    (hx : (p : ℝ) ≤ X) : p ∣ truncatedExclusionModulus M X := by
  classical
    exact
    Finset.dvd_prod_of_mem (fun q : ℕ ↦ q)
      (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hd, hM⟩, hx⟩)

/-- The full sensitive cost of the localized modulus equals the truncated
sum. The prime factors of a product of distinct primes are precisely those
primes. This identifies the exact input to the existing extraction theorem. -/
theorem characterExclusionCost_truncated {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ) (X : ℝ) :
    AnalyticNumberTheory.Arithmetic.characterExclusionCost χ (truncatedExclusionModulus M X) =
      truncatedCharacterExclusionCost χ M X := by
  classical
  unfold AnalyticNumberTheory.Arithmetic.characterExclusionCost truncatedExclusionModulus
  rw [Nat.primeFactors_prod (fun p hp ↦ Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
  rfl

/-- Primitive nonprincipal GRH data and a localized radius below X give a
prime at most X outside M with non-one character value. Extract outside the
localized modulus and use the cutoff to recover avoidance of the full M.
No contribution from excluded primes larger than X is charged. -/
theorem exists_prime_outside_le_of_truncated_cubic_radius {f M : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hf : 2 ≤ f) (hM : M ≠ 0)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) {G E X : ℝ} (hlog : Real.log f ≤ G)
    (hcost : truncatedCharacterExclusionCost χ M X ≤ E)
    (hbound : (tightCubicExclusionRadius G E) ^ 2 ≤ X) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬p ∣ M ∧ χ p ≠ 1 := by
  have hc := (characterExclusionCost_truncated χ M X).trans_le hcost
  obtain ⟨p, hprime, hb, hd, hv⟩ :=
    exists_prime_outside_le_tight_cubic_exclusion_radius χ hf
      (truncatedExclusionModulus_ne_zero M X) hGRH hp hne hlog hc
  have hbX := hb.trans hbound
  exact ⟨p, hprime, hbX, fun h ↦ hd (dvd_truncatedExclusionModulus hM hprime h hbX), hv⟩

/-- Increasing the cutoff increases the localized cost. Nonnegative character
 defects and prime logarithms permit inclusion of additional prime factors.
 This is the monotonicity input for descending radius iteration. -/
theorem truncatedCharacterExclusionCost_mono {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ) {X Y : ℝ}
    (h : X ≤ Y) :
    truncatedCharacterExclusionCost χ M X ≤ truncatedCharacterExclusionCost χ M Y := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.trans h⟩
  · intro p _ _
    exact
      mul_nonneg (AnalyticNumberTheory.Arithmetic.character_defect_nonneg χ p)
        (Real.log_natCast_nonneg p)

/-- Localizing the exclusion cost never exceeds the full support cost.
Discarding prime factors beyond X removes nonnegative summands. This
compares every localized radius with the earlier full-support radius. -/
theorem truncatedCharacterExclusionCost_le_full {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ)
    (X : ℝ) :
    truncatedCharacterExclusionCost χ M X ≤
      AnalyticNumberTheory.Arithmetic.characterExclusionCost χ M := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p _ _
  exact
    mul_nonneg (AnalyticNumberTheory.Arithmetic.character_defect_nonneg χ p)
      (Real.log_natCast_nonneg p)

/-- The localized sensitive cost is nonnegative for every cutoff.
Identify it with the full cost at the localized modulus and use its sign.
This validates the nonnegative branch of the cubic radius. -/
theorem truncatedCharacterExclusionCost_nonneg {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ)
    (X : ℝ) : 0 ≤ truncatedCharacterExclusionCost χ M X := by
  rw [← characterExclusionCost_truncated]
  exact AnalyticNumberTheory.Arithmetic.characterExclusionCost_nonneg _ _

/-- With the conductor envelope fixed, the cubic radius increases with its
exclusion cost. Monotonicity of the square root proves the comparison for
arbitrary real envelopes and supports fixed-point refinement. -/
theorem tightCubicExclusionRadius_mono_cost {G E F : ℝ} (h : E ≤ F) :
    tightCubicExclusionRadius G E ≤ tightCubicExclusionRadius G F := by
  unfold tightCubicExclusionRadius
  apply add_le_add le_rfl
  apply Real.sqrt_le_sqrt
  linarith only [h]

/-- Squaring preserves monotonicity of the cubic radius for nonnegative
conductor and cost envelopes. The radius data place both radii on the
nonnegative branch. This compares actual witness cutoffs. -/
theorem tightCubicExclusionRadius_sq_mono_cost {G E F : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) (h : E ≤ F) :
    (tightCubicExclusionRadius G E) ^ 2 ≤ (tightCubicExclusionRadius G F) ^ 2 := by
  have hn : 0 ≤ tightCubicExclusionRadius G E :=
    (by norm_num only : (0 : ℝ) ≤ 63 / 2).trans (tightCubicExclusionRadius_data hG hE).1
  exact pow_le_pow_left₀ hn (tightCubicExclusionRadius_mono_cost h) 2

end PseudoPrime.LLS.PaperStatements
