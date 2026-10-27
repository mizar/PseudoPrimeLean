/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorPrimeExclusionBounds
public import PseudoPrime.LLS.ConductorPrimeWitnessBounds
public import PseudoPrime.LLS.SmallScaleConductorLogBounds

/-! # Sharper conductor and excluded-prime budgets -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive χ of level q ≥ 3 and nonzero excluded modulus m,
a cutoff y ≥ 131072 satisfying the displayed strict comparison contains a prime
outside m with χ(p) ≠ 1. Contradict the no-witness half-log comparison.
This interface accepts arbitrary certified scalar bounds. -/
theorem exists_prime_ne_one_of_conductor_exclusion_gap {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) {y : ℝ}
    (hy : 131072 ≤ y)
    (hgap :
      (12 * Real.log q + 112) * Real.sqrt y + 2 * (∑ r ∈ m.primeFactors, Real.log r) < y / 2) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  classical
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ y) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hne
    exact hnone ⟨p, hp, hb, hd, hne⟩
  exact (log_half_no_witness_conductor_comparison χ hq hp hGRH hm hy hno).not_gt hgap

/-- For A ≥ 0 and real E, the displayed maximum cutoff satisfies the strict
quadratic comparison. Apply Young's inequality to A sqrt(y), retaining one unit
of slack in A+1. This improves both coefficients of the former coarse budget. -/
theorem conductor_exclusion_refined_gap {A E : ℝ} (hA : 0 ≤ A) :
    let y := max 131072 (4 * (A + 1) ^ 2 + 8 * E)
    A * Real.sqrt y + 2 * E < y / 2 := by
  dsimp only
  let y := max (131072 : ℝ) (4 * (A + 1) ^ 2 + 8 * E)
  have hy0 : 0 ≤ y := le_trans (by norm_num only) (le_max_left _ _)
  have hs := Real.sq_sqrt hy0
  have hb : 4 * (A + 1) ^ 2 + 8 * E ≤ y := le_max_right _ _
  have hYoung := sq_nonneg (Real.sqrt y / 2 - A)
  nlinarith only [hs, hb, hYoung, hA]

/-- Under GRH for primitive χ of level q ≥ 3 and m ≠ 0, a non-one prime outside m
lies below max(131072,4(12log(q)+113)²+8E(m)). Apply the scalar comparison with
A=12log(q)+112. This separates conductor and excluded-prime costs with smaller constants. -/
theorem exists_prime_ne_one_le_refined_conductor_exclusion {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          max 131072 (4 * (12 * Real.log q + 113) ^ 2 + 8 * (∑ r ∈ m.primeFactors, Real.log r)) ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  apply exists_prime_ne_one_of_conductor_exclusion_gap χ hq hp hGRH hm (le_max_left _ _)
  have h :=
    conductor_exclusion_refined_gap (A := 12 * Real.log q + 112) (E :=
      ∑ r ∈ m.primeFactors, Real.log r) (by linarith only [Real.log_natCast_nonneg q])
  simpa only [add_assoc, show (112 : ℝ) + 1 = 113 by norm_num only] using h

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For nonnegative A and E, the positive-root cutoff with one unit of slack
satisfies the strict comparison. Compare sqrt(y) with the larger quadratic root
and factor the difference. This avoids the loss from Young's inequality. -/
theorem conductor_exclusion_root_gap {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) :
    let y := max 131072 ((A + 1 + Real.sqrt ((A + 1) ^ 2 + 4 * E)) ^ 2)
    A * Real.sqrt y + 2 * E < y / 2 := by
  dsimp only
  let s := Real.sqrt ((A + 1) ^ 2 + 4 * E)
  let y := max (131072 : ℝ) ((A + 1 + s) ^ 2)
  have hs : s ^ 2 = (A + 1) ^ 2 + 4 * E := Real.sq_sqrt (by nlinarith only [sq_nonneg (A + 1), hE])
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hb0 : 0 ≤ A + 1 + s := by linarith only [hA, hs0]
  have ht : A + 1 + s ≤ Real.sqrt y := by
    have h := Real.sqrt_le_sqrt (show (A + 1 + s) ^ 2 ≤ y from le_max_right _ _)
    rw [Real.sqrt_sq hb0] at h
    exact h
  have hy0 : 0 ≤ y := le_trans (by norm_num only) (le_max_left _ _)
  have hy := Real.sq_sqrt hy0
  have hprod :=
    mul_nonneg (sub_nonneg.mpr ht)
      (show 0 ≤ Real.sqrt y + (A + 1 + s) - 2 * A by linarith only [ht, hs0])
  nlinarith only [hs, hy, hprod, ht, hs0, hA]

/-- Under GRH for primitive χ of level q ≥ 3 and m ≠ 0, there is a non-one prime
outside m below the displayed root budget. Solve the conductor comparison before
relaxing its mixed term. This is the sharper arbitrary-exclusion witness interface. -/
theorem exists_prime_ne_one_le_root_conductor_exclusion {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          max 131072
            ((12 * Real.log q + 113 +
                Real.sqrt ((12 * Real.log q + 113) ^ 2 + 4 * (∑ r ∈ m.primeFactors, Real.log r))) ^
              2) ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  apply exists_prime_ne_one_of_conductor_exclusion_gap χ hq hp hGRH hm (le_max_left _ _)
  have h :=
    conductor_exclusion_root_gap (A := 12 * Real.log q + 112) (E :=
      ∑ r ∈ m.primeFactors, Real.log r) (by linarith only [Real.log_natCast_nonneg q])
      (Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p))
  simpa only [add_assoc, show (112 : ℝ) + 1 = 113 by norm_num only] using h

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For E ≥ 0 and real B, the root budget is at most the linear radical budget.
Use the square-root identity and (B-sqrt(B²+4E))² ≥ 0. This formally compares
the two explicit forms without identifying their witnesses. -/
theorem root_conductor_budget_le_linear {B E : ℝ} (hE : 0 ≤ E) :
    max (131072 : ℝ) ((B + Real.sqrt (B ^ 2 + 4 * E)) ^ 2) ≤ max 131072 (4 * B ^ 2 + 8 * E) := by
  apply max_le_max (le_refl _)
  have hs := Real.sq_sqrt (show 0 ≤ B ^ 2 + 4 * E by nlinarith only [sq_nonneg B, hE])
  nlinarith only [hs, sq_nonneg (B - Real.sqrt (B ^ 2 + 4 * E))]

/-- For nonnegative logarithmic conductor L and exclusion cost E, the refined
budget is at most the previous 8(12L+200)²+16E bound. Check both branches of the
maximum by rational polynomial inequalities. This certifies improvement on the full domain. -/
theorem refined_conductor_budget_le_previous {L E : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E) :
    max (131072 : ℝ) (4 * (12 * L + 113) ^ 2 + 8 * E) ≤ 8 * (12 * L + 200) ^ 2 + 16 * E := by
  apply max_le
  · nlinarith only [hL, hE, sq_nonneg (12 * L + 200)]
  · nlinarith only [hL, hE, sq_nonneg L]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character at nonzero level q has a unit-prime
non-one witness below the displayed root bound in its primitive conductor and
ambient exclusion cost. Primitivize and transfer the unit value back to χ.
This is the original-level interface for the sharper conductor estimate. -/
theorem exists_prime_ne_one_le_conductor_root_budget {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          max 131072
            ((12 * Real.log χ.conductor + 113 +
                Real.sqrt
                  ((12 * Real.log χ.conductor + 113) ^ 2 +
                    4 * (∑ r ∈ q.primeFactors, Real.log r))) ^
              2) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_root_conductor_exclusion χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a subgroup supplies a
unit-prime outside its image below the root conductor budget. Apply the character
witness and contradict triviality on a proposed subgroup unit.
This retains the chosen character's conductor in the subgroup conclusion. -/
theorem exists_prime_outside_le_character_conductor_root {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤
          max 131072
            ((12 * Real.log χ.conductor + 113 +
                Real.sqrt
                  ((12 * Real.log χ.conductor + 113) ^ 2 +
                    4 * (∑ r ∈ q.primeFactors, Real.log r))) ^
              2) ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_conductor_root_budget χ hχ hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive χ of level q ≥ 3 and m ≠ 0, any y ≥ 200 with the
stated strict conductor comparison contains a non-one prime outside m.
Contradict the improved no-witness comparison. This permits cutoffs without the old large floor. -/
theorem exists_prime_ne_one_of_small_conductor_gap {q m : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hm : m ≠ 0) {y : ℝ} (hy : 200 ≤ y)
    (hgap :
      (12 * Real.log q + 112) * Real.sqrt y + 2 * (∑ r ∈ m.primeFactors, Real.log r) < y / 2) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  classical
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ y) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hne
    exact hnone ⟨p, hp, hb, hd, hne⟩
  exact
    (log_half_no_witness_conductor_comparison_of_ge_twoHundred χ hq hp hGRH hm hy hno).not_gt hgap

/-- For A,E ≥ 0, the squared larger root with one unit of slack satisfies the
strict conductor comparison. Expand after the square-root identity.
This scalar lemma needs no maximum with an external analytic threshold. -/
theorem conductor_exclusion_unclipped_root_gap {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) :
    let y := (A + 1 + Real.sqrt ((A + 1) ^ 2 + 4 * E)) ^ 2
    A * Real.sqrt y + 2 * E < y / 2 := by
  dsimp only
  have hs0 := Real.sqrt_nonneg ((A + 1) ^ 2 + 4 * E)
  have hs := Real.sq_sqrt (show 0 ≤ (A + 1) ^ 2 + 4 * E by nlinarith only [sq_nonneg (A + 1), hE])
  rw [Real.sqrt_sq (show 0 ≤ A + 1 + Real.sqrt ((A + 1) ^ 2 + 4 * E) by linarith only [hA, hs0])]
  nlinarith only [hs, hA, hs0]

/-- For E ≥ 0 and real B, the squared root radius is at most 4B²+8E.
Use the square-root identity and the nonnegative square of their difference.
This gives a polynomial envelope without reintroducing a constant branch. -/
theorem conductor_root_le_polynomial {B E : ℝ} (hE : 0 ≤ E) :
    (B + Real.sqrt (B ^ 2 + 4 * E)) ^ 2 ≤ 4 * B ^ 2 + 8 * E := by
  have hs := Real.sq_sqrt (show 0 ≤ B ^ 2 + 4 * E by nlinarith only [sq_nonneg B, hE])
  nlinarith only [hs, sq_nonneg (B - Real.sqrt (B ^ 2 + 4 * E))]

/-- Under GRH for primitive χ of level q ≥ 3 and m ≠ 0, a non-one prime outside
m lies below the displayed root bound without a constant maximum branch.
The radius automatically exceeds the analytic cutoff 200, then its strict root gap
supplies the witness. This removes the artificial scale floor in the conductor estimate. -/
theorem exists_prime_ne_one_le_unclipped_conductor_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          (12 * Real.log q + 113 +
              Real.sqrt ((12 * Real.log q + 113) ^ 2 + 4 * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  have hB : 113 ≤ 12 * Real.log q + 113 := by linarith only [Real.log_natCast_nonneg q]
  have hy :
    (200 : ℝ) ≤
      (12 * Real.log q + 113 +
          Real.sqrt ((12 * Real.log q + 113) ^ 2 + 4 * (∑ r ∈ m.primeFactors, Real.log r))) ^
        2 := by
    nlinarith only [hB,
      Real.sqrt_nonneg ((12 * Real.log q + 113) ^ 2 + 4 * (∑ r ∈ m.primeFactors, Real.log r))]
  apply exists_prime_ne_one_of_small_conductor_gap χ hq hp hGRH hm hy
  have h :=
    conductor_exclusion_unclipped_root_gap (A := 12 * Real.log q + 112) (E :=
      ∑ r ∈ m.primeFactors, Real.log r) (by linarith only [Real.log_natCast_nonneg q])
      (Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p))
  simpa only [add_assoc, show (112 : ℝ) + 1 = 113 by norm_num only] using h

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character at nonzero level q has a unit-prime
non-one witness below the displayed root bound in its primitive conductor and
ambient exclusion cost. Primitivize and transfer the unit value back to χ.
This is the original-level interface for the smaller-scale conductor estimate. -/
theorem exists_prime_ne_one_le_unclipped_conductor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((12 * Real.log χ.conductor + 113 +
              Real.sqrt
                ((12 * Real.log χ.conductor + 113) ^ 2 + 4 * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_unclipped_conductor_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a subgroup supplies a
unit-prime outside its image below the root conductor budget. Apply the character
witness and contradict triviality on a proposed subgroup unit.
This retains the chosen character's conductor in the subgroup conclusion. -/
theorem exists_prime_outside_le_unclipped_character_conductor {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤
          ((12 * Real.log χ.conductor + 113 +
              Real.sqrt
                ((12 * Real.log χ.conductor + 113) ^ 2 + 4 * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_unclipped_conductor_root χ hχ hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS
