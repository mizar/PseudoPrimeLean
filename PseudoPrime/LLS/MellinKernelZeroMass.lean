/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelZeroTail

/-!
# Reduction of sharp Mellin-kernel zero mass to bounded height

The conductor-uniform zero tail is proved separately. An eventual compact-height estimate
with the kernel's integral mass as coefficient therefore suffices for the full sharp bound.
The compact estimate is an explicit hypothesis of this reduction.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Under GRH, suppose every fixed positive height truncation admits, for each positive
delta, an eventual upper bound (K.mass + delta) log q uniform over primitive nonprincipal
characters. Then the full absolute zero mass is eventually at most (1+epsilon) K.mass log q.
Choose delta = epsilon K.mass / 2, apply the proved uniform tail bound, and add the two
absolutely convergent complementary series. The compact-truncation estimate remains an
explicit hypothesis; this reduction removes the tail from the remaining analytic task. -/
theorem exists_uniform_kernelZeroSum_le_mass_of_truncations (K : MellinKernel)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hcompact :
      ∀ T : ℝ,
        0 < T →
          ∀ δ : ℝ,
            0 < δ →
              ∃ Q : ℕ,
                2 ≤ Q ∧
                  ∀ (q : ℕ) [NeZero q],
                    Q ≤ q →
                      ∀ (χ : DirichletCharacter ℂ q),
                        χ.IsPrimitive →
                          χ ≠ 1 →
                          χ⁻¹ ≠ 1 →
                          (∑' ρ : ℂ, if |ρ.im| < T then ‖K.kernelZeroTerm χ ρ‖ else 0) ≤
                            (K.mass + δ) * Real.log q) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ Q : ℕ,
          2 ≤ Q ∧
            ∀ (q : ℕ) [NeZero q],
              Q ≤ q →
                ∀ (χ : DirichletCharacter ℂ q),
                  χ.IsPrimitive →
                    χ ≠ 1 →
                    χ⁻¹ ≠ 1 →
                    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ (1 + ε) * K.mass * Real.log q := by
  classical
  intro ε hε
  let δ := ε * K.mass / 2
  have hδ : 0 < δ := div_pos (mul_pos hε (mass_pos K)) (by norm_num only)
  obtain ⟨T, Q₁, hT, hQ₁, hb⟩ := exists_uniform_kernelZeroSum_tail_le_log K hδ
  obtain ⟨Q₂, hQ₂, hc⟩ := hcompact T hT δ hδ
  refine ⟨max Q₁ Q₂, hQ₁.trans (Nat.le_max_left _ _), ?_⟩
  intro q _ hq χ hp hne hinv
  have hq₁ := (Nat.le_max_left Q₁ Q₂).trans hq
  have hq₂ := (Nat.le_max_right Q₁ Q₂).trans hq
  have hs := (summable_kernelZeroTerm K (hQ₁.trans hq₁) hGRH hp hne hinv).norm
  have hinside : Summable (fun ρ : ℂ ↦ if |ρ.im| < T then ‖K.kernelZeroTerm χ ρ‖ else 0) :=
    Summable.of_nonneg_of_le (fun ρ ↦ ite_nonneg (norm_nonneg _) le_rfl)
      (fun ρ ↦ by
        split_ifs
        · exact le_rfl
        · exact norm_nonneg _)
      hs
  have houtside : Summable (fun ρ : ℂ ↦ if T ≤ |ρ.im| then ‖K.kernelZeroTerm χ ρ‖ else 0) :=
    Summable.of_nonneg_of_le (fun ρ ↦ ite_nonneg (norm_nonneg _) le_rfl)
      (fun ρ ↦ by
        split_ifs
        · exact le_rfl
        · exact norm_nonneg _)
      hs
  have he :
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) =
      (∑' ρ : ℂ, if |ρ.im| < T then ‖K.kernelZeroTerm χ ρ‖ else 0) +
        (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖K.kernelZeroTerm χ ρ‖ else 0) := by
    rw [← hinside.tsum_add houtside]
    apply tsum_congr
    intro ρ
    by_cases h : |ρ.im| < T
    · rw [ite_eq_left h, ite_eq_right (not_le.mpr h), add_zero]
    · rw [ite_eq_right h, ite_eq_left (le_of_not_gt h), zero_add]
  rw [he]
  have hi := hc q hq₂ χ hp hne hinv
  have ho := hb q hq₁ χ (hGRH q χ hp) hp hne hinv
  dsimp only [δ] at hi ho
  nlinarith only [hi, ho]

end PseudoPrime.LLS.PaperStatements.MellinKernel
