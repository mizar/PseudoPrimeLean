/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TruncatedCubicExclusion

/-! # Descending refinement of localized cubic witness cutoffs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Squared cubic radius using only excluded prime factors at most X.
Inputs are a character, its excluded integer and conductor envelope.
A post-fixed point F(X)≤X gives a prime witness at most X. -/
noncomputable def truncatedCubicBound {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ) (G X : ℝ) : ℝ :=
  (tightCubicExclusionRadius G (truncatedCharacterExclusionCost χ M X)) ^ 2

/-- With nonnegative conductor envelope, the localized bound increases with
its cutoff. Combine the cost inclusion with squared-radius monotonicity.
This preserves the post-fixed-point condition after refinement. -/
theorem truncatedCubicBound_mono {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ) {G : ℝ} (hG : 0 ≤ G) :
    Monotone (truncatedCubicBound χ M G) := by
  intro X Y hXY
  exact
    tightCubicExclusionRadius_sq_mono_cost hG (truncatedCharacterExclusionCost_nonneg χ M X)
      (truncatedCharacterExclusionCost_mono χ M hXY)

/-- Any admissible cutoff refines to a smaller admissible cutoff.
Apply monotonicity to F(X)≤X. This is the invariant used at every iteration. -/
theorem truncatedCubicBound_refine {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ) {G X : ℝ}
    (hG : 0 ≤ G) (hX : truncatedCubicBound χ M G X ≤ X) :
    truncatedCubicBound χ M G (truncatedCubicBound χ M G X) ≤ truncatedCubicBound χ M G X := by
  exact truncatedCubicBound_mono χ M hG hX

/-- Start from the full-support squared cubic radius and repeatedly replace
it by the localized bound. This sequence supplies successively no larger
witness cutoffs without choosing a circular initial estimate. -/
noncomputable def truncatedCubicIterate {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ) (G : ℝ) : ℕ → ℝ
  | 0 =>
    (tightCubicExclusionRadius G (AnalyticNumberTheory.Arithmetic.characterExclusionCost χ M)) ^ 2
  | k + 1 => truncatedCubicBound χ M G (truncatedCubicIterate χ M G k)

/-- Every iterate is an admissible cutoff and the next one is no larger.
The initial case uses localization below the full cost, and induction uses
the refinement invariant. This makes each finite iteration a valid bound. -/
theorem truncatedCubicIterate_step_le {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ) {G : ℝ}
    (hG : 0 ≤ G) (k : ℕ) : truncatedCubicIterate χ M G (k + 1) ≤ truncatedCubicIterate χ M G k := by
  induction k with
  | zero =>
    exact
      tightCubicExclusionRadius_sq_mono_cost hG (truncatedCharacterExclusionCost_nonneg χ M _)
        (truncatedCharacterExclusionCost_le_full χ M _)
  | succ k ih => exact truncatedCubicBound_refine χ M hG ih

/-- Primitive nonprincipal GRH data give an outside prime below every
iterate of the localized cutoff. Apply the step invariant as a radius
condition. Thus refinement improves a witness bound, not only its budget. -/
theorem exists_prime_outside_le_truncatedCubicIterate {f M : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hf : 2 ≤ f) (hM : M ≠ 0)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) {G : ℝ} (hlog : Real.log f ≤ G) (k : ℕ) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ truncatedCubicIterate χ M G k ∧ ¬p ∣ M ∧ χ p ≠ 1 := by
  exact
    exists_prime_outside_le_of_truncated_cubic_radius χ hf hM hGRH hp hne hlog le_rfl
      (truncatedCubicIterate_step_le χ M ((Real.log_natCast_nonneg f).trans hlog) k)

/-- An antitone sequence in a linear order with values in a fixed finite set
is eventually constant. Choose the least attained value and use antitonicity.
This generic finite-descent lemma avoids numerical iteration certificates. -/
theorem eventually_constant_of_antitone_mem_finset {α : Type*} [LinearOrder α] (u : ℕ → α)
    (T : Finset α) (hu : Antitone u) (hT : ∀ k, u k ∈ T) : ∃ k, ∀ j, k ≤ j → u j = u k := by
  classical
  let S := T.filter (fun x ↦ ∃ k, u k = x)
  have hs : S.Nonempty := ⟨u 0, Finset.mem_filter.mpr ⟨hT 0, 0, rfl⟩⟩
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image S id hs
  obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hx).2
  refine ⟨k, fun j hj ↦ le_antisymm (hu hj) ?_⟩
  have hm := hmin (u j) (Finset.mem_filter.mpr ⟨hT j, j, rfl⟩)
  simpa only [id_eq, ← hk] using hm

/-- Every localized iterate lies in the finite set obtained by evaluating
the cubic radius at all prime-factor subsets, together with the initial
cutoff. The powerset is used for a proof of finiteness, not enumerated. -/
theorem truncatedCubicIterate_mem_finset {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ) (G : ℝ)
    (k : ℕ) :
    truncatedCubicIterate χ M G k ∈
      insert (truncatedCubicIterate χ M G 0)
        (M.primeFactors.powerset.image
          (fun S : Finset ℕ ↦
            (tightCubicExclusionRadius G (∑ p ∈ S, (1 - (χ p).re) * Real.log p)) ^ 2)) := by
  classical
    cases k with
  | zero => exact Finset.mem_insert_self _ _
  | succ k =>
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine
      ⟨M.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ truncatedCubicIterate χ M G k),
        Finset.mem_powerset.mpr (Finset.filter_subset _ _), rfl⟩

/-- For nonnegative conductor envelope, localized cubic refinement reaches
a fixed value after finitely many steps. Combine the finite prime-factor
subset image with the decreasing-step invariant. No gigantic finite
certificate or prescribed iteration count is required. -/
theorem truncatedCubicIterate_eventually_constant {f : ℕ} (χ : DirichletCharacter ℂ f) (M : ℕ)
    {G : ℝ} (hG : 0 ≤ G) :
    ∃ k, ∀ j, k ≤ j → truncatedCubicIterate χ M G j = truncatedCubicIterate χ M G k := by
  classical
    exact
    eventually_constant_of_antitone_mem_finset (truncatedCubicIterate χ M G) _
      (antitone_nat_of_succ_le (truncatedCubicIterate_step_le χ M hG))
      (truncatedCubicIterate_mem_finset χ M G)

end PseudoPrime.LLS.PaperStatements
