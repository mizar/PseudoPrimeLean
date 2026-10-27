/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterProgressionSums
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterLogDifferences
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrincipalLogDifferenceLower
public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionTheta

/-! # From logarithmic character difference budgets to progression theta supply -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

open Classical in
/-- For positive ordered cutoffs and a coprime residue, the principal logarithmic
difference minus the sum of nonprincipal norms is at most `phi(q) psi(y;q,a)
log(y/x)`. Apply weighted orthogonality and the pointwise upper difference bound.
This transfers analytic character errors to an unsmoothed progression sum. -/
theorem principalLogDifference_sub_errors_le_psiInProgression {q a : ℕ} [NeZero q]
    (ha : Nat.Coprime a q) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (Arithmetic.characterLogWeightedSum y (1 : DirichletCharacter ℂ q) -
            Arithmetic.characterLogWeightedSum x (1 : DirichletCharacter ℂ q)).re -
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖Arithmetic.characterLogWeightedSum y χ - Arithmetic.characterLogWeightedSum x χ‖ ≤
      (q.totient : ℝ) * psiInProgression y q a * Real.log (y / x) := by
  let w : ℕ → ℝ := fun n ↦
    Arithmetic.logWeightedMangoldtTerm y n -
      if n ≤ ⌊x⌋₊ then Arithmetic.logWeightedMangoldtTerm x n else 0
  have hb :=
    Arithmetic.weighted_progression_lower_of_character_sums (ZMod.unitOfCoprime a ha)
      (Finset.Ioc 0 ⌊y⌋₊) w
  dsimp only [w] at hb
  simp only [Arithmetic.sum_log_difference_weight_mul_character _ hxy] at hb
  have hfilter :
    (Finset.Ioc 0 ⌊y⌋₊).filter
        (fun n : ℕ ↦ ((ZMod.unitOfCoprime a ha : (ZMod q)ˣ) : ZMod q) = (n : ZMod q)) =
      (Finset.Ioc 0 ⌊y⌋₊).filter (fun n ↦ n % q = a % q) := by
    ext n
    simp only [Finset.mem_filter, ZMod.coe_unitOfCoprime, ZMod.natCast_eq_natCast_iff']
    exact and_congr_right (fun _ ↦ eq_comm)
  rw [hfilter] at hb
  have hs :
    (∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n ↦ n % q = a % q), w n) ≤
      psiInProgression y q a * Real.log (y / x) := by
    rw [psiInProgression, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    exact
      (Arithmetic.logWeightedMangoldtTerm_difference hx hxy (Finset.mem_Ioc.mp hnI).1
          ((Nat.le_floor_iff (hx.trans_le hxy).le).mp (Finset.mem_Ioc.mp hnI).2)).2
  exact
    hb.trans
      (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q.totient))

open Classical in
/-- At scale at least one and a coprime residue, a principal coefficient `17/32`
and a total error budget `x log(5/4)/32` imply `theta(x;q,a) >= x/(2 phi(q))`.
The budget includes the common-factor correction, nonprincipal difference norms,
and the elementary prime-power loss. Combine the progression psi inequality with
`psi - theta <= 18 sqrt(x)` and cancel positive logarithm and totient factors. -/
theorem thetaInProgression_lower_of_log_difference_budget {q a : ℕ} [NeZero q]
    (ha : Nat.Coprime a q) {x : ℝ} (hx : 1 ≤ x)
    (hprincipal :
      (17 / 32 : ℝ) * x * Real.log (5 / 4) - (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 ≤
        (Arithmetic.characterLogWeightedSum x (1 : DirichletCharacter ℂ q) -
            Arithmetic.characterLogWeightedSum (4 * x / 5) (1 : DirichletCharacter ℂ q)).re)
    (hbudget :
      (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 +
          (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            ‖Arithmetic.characterLogWeightedSum x χ -
                Arithmetic.characterLogWeightedSum (4 * x / 5) χ‖) +
          18 * (q.totient : ℝ) * Real.sqrt x * Real.log (5 / 4) ≤
        (1 / 32 : ℝ) * x * Real.log (5 / 4)) :
    x / (2 * (q.totient : ℝ)) ≤ thetaInProgressionReal x q a := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have ht : 0 < 4 * x / 5 := div_pos (mul_pos (by norm_num only) hxpos) (by norm_num only)
  have htx : 4 * x / 5 ≤ x := by linarith only [hx]
  have hratio : x / (4 * x / 5) = (5 / 4 : ℝ) := by
    apply (div_eq_iff ht.ne').2
    ring
  have hlog : 0 < Real.log (5 / 4 : ℝ) := Real.log_pos (by norm_num only)
  have hb := principalLogDifference_sub_errors_le_psiInProgression ha ht htx
  rw [hratio] at hb
  have hd := (psi_sub_thetaInProgression_bounds x q a hx).2
  have hφ : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hdm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hφ.le) hlog.le
  have htheta :
    x / 2 * Real.log (5 / 4) ≤
      (q.totient : ℝ) * thetaInProgressionReal x q a * Real.log (5 / 4) := by
    nlinarith only [hprincipal, hbudget, hb, hdm]
  have ht' := (mul_le_mul_iff_left₀ hlog).mp htheta
  apply (div_le_iff₀ (mul_pos (by norm_num only) hφ)).mpr
  nlinarith only [ht']

open Classical in
/-- There is one absolute principal threshold for all positive moduli and
coprime residues. Above it, the displayed total logarithmic difference budget
implies the required progression theta lower bound. Insert the unconditional
principal estimate into the finite arithmetic conversion; bounding the
nonprincipal family uniformly remains an explicit separate analytic task. -/
theorem exists_uniform_log_difference_theta_threshold :
    ∃ X : ℝ,
      1 ≤ X ∧
        ∀ (q a : ℕ) [NeZero q],
          Nat.Coprime a q →
            ∀ x : ℝ,
              X ≤ x →
                (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 +
                    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                      ‖Arithmetic.characterLogWeightedSum x χ -
                          Arithmetic.characterLogWeightedSum (4 * x / 5) χ‖) +
                    18 * (q.totient : ℝ) * Real.sqrt x * Real.log (5 / 4) ≤
                  (1 / 32 : ℝ) * x * Real.log (5 / 4) →
                x / (2 * (q.totient : ℝ)) ≤ thetaInProgressionReal x q a := by
  obtain ⟨X, hX, hp⟩ := Arithmetic.exists_principalLogDifference_lower
  refine ⟨X, hX, ?_⟩
  intro q a inst ha x hx hbudget
  exact
    thetaInProgression_lower_of_log_difference_budget ha (hX.trans hx) (hp q (NeZero.ne q) x hx)
      hbudget

end PseudoPrime.AnalyticNumberTheory.AGP
