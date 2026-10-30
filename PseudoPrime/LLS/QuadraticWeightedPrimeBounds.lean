/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.WeightedCharacterPrimeBounds

/-! # Quadratic character weights and actual least outside primes -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, the quadratic three-character profile yields an actual least
outside prime whenever its weighted conductor budget beats the principal prefix
and tail. Distinct nonprincipal quadratic characters annihilating the target
subgroup are required. The proved trace penalty is max(t,1-2t), and total weight
is one. This specializes the weighted criterion without a supplied trace bound. -/
theorem quadratic_pair_least_criterion (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ (H : Subgroup (ZMod q)ˣ) (a b : DirichletCharacter ℂ q),
                      a ≠ b →
                        a ≠ a * b →
                        b ≠ a * b →
                        a.IsQuadratic →
                        b.IsQuadratic →
                        (∀ χ ∈ NumberTheory.quadraticTriple a b, χ ≠ 1) →
                        a ∈ NumberTheory.subgroupAnnihilator H →
                        b ∈ NumberTheory.subgroupAnnihilator H →
                        ∀ t X x : ℝ,
                          0 ≤ t →
                            t ≤ 1 →
                            2 ≤ x →
                            ∀ T : Finset ℕ,
                              (∀ n ∈ T, (n : ℝ) ≤ X) →
                                K.mass *
                                      NumberTheory.weightedConductorLogSum
                                        (NumberTheory.quadraticTriple a b)
                                        (NumberTheory.quadraticPairWeight a b t) +
                                    (η * Real.log q +
                                      C * (1 + Real.log q * Real.log x / Real.sqrt x)) <
                                  (1 + max t (1 - 2 * t)) *
                                      (∑ n ∈ T,
                                        (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x
                                            n).re) -
                                    max t (1 - 2 * t) *
                                      (∑' n : ℕ,
                                          MellinKernel.summand K (1 : DirichletCharacter ℂ q) x
                                            n).re →
                                ∃ p : ℕ,
                                  IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤ X := by
  obtain ⟨C, hC, hb⟩ := weighted_least_prime_criterion K hg
  refine ⟨C, hC, ?_⟩
  intro η hη
  obtain ⟨Q, hQ, hb⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H a b hab ha hb' hqa hqb hnp haH hbH t X x ht ht1 hx T hT hgap
  apply
    hb q hq H (NumberTheory.quadraticTriple a b) (NumberTheory.quadraticPairWeight a b t)
      (fun χ _ ↦ NumberTheory.quadraticPairWeight_nonneg a b ht ht1 χ) hnp
      (NumberTheory.quadraticTriple_annihilates H a b haH hbH) (max t (1 - 2 * t)) X x hx
      (NumberTheory.quadraticPairTrace_lower a b hab ha hb' hqa hqb ht) T hT
  simpa only [NumberTheory.quadraticPairWeight_total a b hab ha hb' t, mul_one] using hgap

/-- If the conductor saving exceeds four times the principal tail, equal
weights on a and b give a strictly smaller comparison deficit than uniform
weights on a, b and a*b. The same allowance E is retained in both candidates.
Expand the exact conductor costs and compare the two linear deficits. -/
theorem quadratic_pair_budget_saving {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (M P F E : ℝ)
    (hsave :
      4 * (F - P) <
        M * (2 * Real.log (a * b).conductor - Real.log a.conductor - Real.log b.conductor)) :
    M *
              NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
                (NumberTheory.quadraticPairWeight a b 0) +
            E -
          2 * P +
        F <
      M *
              NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
                (NumberTheory.quadraticPairWeight a b (1 / 3)) +
            E -
          (4 / 3 : ℝ) * P +
        F / 3 := by
  rw [NumberTheory.quadraticPairWeight_cost a b hab ha hb 0,
    NumberTheory.quadraticPairWeight_cost a b hab ha hb (1 / 3)]
  norm_num only
  nlinarith only [hsave]

/-- Under GRH, the two-character candidate produces an actual least outside
prime when its conductor saving beats the actual principal tail and the uniform
three-character budget is at most its principal comparison. Keep the ambient
allowance and use the strict saving to turn even equality into a strict gap.
This connects the nonnegative profile improvement to the least-prime API. -/
theorem quadratic_pair_strict_prime (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ (H : Subgroup (ZMod q)ˣ) (a b : DirichletCharacter ℂ q),
                      a ≠ b →
                        a ≠ a * b →
                          b ≠ a * b →
                            a.IsQuadratic →
                              b.IsQuadratic →
                                (∀ χ ∈ NumberTheory.quadraticTriple a b, χ ≠ 1) →
                                  a ∈ NumberTheory.subgroupAnnihilator H →
                                    b ∈ NumberTheory.subgroupAnnihilator H →
                                      ∀ X x : ℝ,
                                        2 ≤ x →
                                          ∀ T : Finset ℕ,
                                            (∀ n ∈ T, (n : ℝ) ≤ X) →
                                              let P :=
                                                ∑ n ∈ T,
                                                  (MellinKernel.summand K
                                                      (1 : DirichletCharacter ℂ q) x n).re
                                              let F :=
                                                (∑' n : ℕ,
                                                    MellinKernel.summand K
                                                      (1 : DirichletCharacter ℂ q) x n).re
                                              let E :=
                                                η * Real.log q +
                                                  C * (1 + Real.log q * Real.log x / Real.sqrt x)
                                              4 * (F - P) <
                                                  K.mass *
                                                    (2 * Real.log (a * b).conductor -
                                                      Real.log a.conductor -
                                                      Real.log b.conductor) →
                                                K.mass *
                                                      NumberTheory.weightedConductorLogSum
                                                        (NumberTheory.quadraticTriple a b)
                                                        (NumberTheory.quadraticPairWeight a b
                                                          (1 / 3)) +
                                                    E ≤
                                                  (4 / 3 : ℝ) * P - F / 3 →
                                                ∃ p : ℕ,
                                                  IsLeast (NumberTheory.primesOutside q H) p ∧
                                                    (p : ℝ) ≤ X := by
  obtain ⟨C, hC, hb⟩ := quadratic_pair_least_criterion K hg
  refine ⟨C, hC, ?_⟩
  intro η hη
  obtain ⟨Q, hQ, hb⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H a b hab ha hb' hqa hqb hnp haH hbH X x hx T hT P F E hsave havg
  have hs := quadratic_pair_budget_saving a b hab ha hb' K.mass P F E hsave
  have hgap :
    K.mass *
          NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
            (NumberTheory.quadraticPairWeight a b 0) +
        E <
      2 * P - F := by
    linarith only [hs, havg]
  apply
    hb q hq H a b hab ha hb' hqa hqb hnp haH hbH 0 X x (by norm_num only) (by norm_num only) hx T hT
  norm_num only [mul_zero, sub_zero, max_eq_right zero_le_one, one_mul]
  exact hgap

end PseudoPrime.LLS.PaperStatements
