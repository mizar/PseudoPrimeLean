/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelCompactZeroMass

/-! # Kernel zero mass at an ambient modulus

Integer-height zero counts bound the full mass by a linear function of the log conductor.
Combine this bound at small conductors with the sharp kernel-mass asymptotic at large
conductors to obtain a bound in the log of any sufficiently large ambient modulus.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For primitive nonprincipal characters with individual RH and modulus at least two,
the absolute kernel zero sum is bounded by D log q + B, with nonnegative constants
depending only on the kernel. Sum the quadratic integer-height bounds and their
logarithmic errors using the two summable majorants. This controls small conductors
when the sharp asymptotic is applied at a larger ambient modulus. -/
theorem exists_uniform_kernelZeroSum_le_log_add (K : MellinKernel) :
    ∃ D B : ℝ,
      0 ≤ D ∧
        0 ≤ B ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 → χ⁻¹ ≠ 1 → (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ D * Real.log q + B := by
  classical
  obtain ⟨C, A, hC, hA, hb⟩ := exists_uniform_finite_kernelZeroSum_height_bins K
  let U := ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)
  let V := ∑' k : ℤ, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)
  have hden (k : ℤ) : 0 ≤ 1 + (k : ℝ) ^ 2 := by nlinarith only [sq_nonneg (k : ℝ)]
  have hu (k : ℤ) : 0 ≤ 1 / (1 + (k : ℝ) ^ 2) := div_nonneg zero_le_one (hden k)
  have hv (k : ℤ) : 0 ≤ (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2) :=
    div_nonneg (add_nonneg (Real.log_nonneg (by linarith only [abs_nonneg (k : ℝ)])) zero_le_one)
      (hden k)
  have hD : 0 ≤ 3 * C * U := mul_nonneg (mul_nonneg (by norm_num only) hC.le) (tsum_nonneg hu)
  have hB : 0 ≤ 6 * C * A * V :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hC.le) hA.le) (tsum_nonneg hv)
  refine ⟨3 * C * U, 6 * C * A * V, hD, hB, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  apply Real.tsum_le_of_sum_le (fun ρ ↦ norm_nonneg _)
  intro S
  let J := S.image (fun ρ : ℂ ↦ (⌊ρ.im⌋ : ℤ))
  have huJ := Analysis.summable_int_quadratic.sum_le_tsum J (fun k _ ↦ hu k)
  have hvJ := Analysis.summable_int_logWeighted_quadratic.sum_le_tsum J (fun k _ ↦ hv k)
  have hs := hb q hq χ hRH hp hne hinv S
  have he :
    (∑ k ∈ J, (3 * C / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1))) =
      3 * C * Real.log q * (∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2)) +
        6 * C * A * (∑ k ∈ J, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  change
    (∑ ρ ∈ S, ‖K.kernelZeroTerm χ ρ‖) ≤
      ∑ k ∈ J,
        (3 * C / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) at hs
  rw [he] at hs
  have huq :=
    mul_le_mul_of_nonneg_left huJ
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hC.le) (Real.log_natCast_nonneg q))
  have hvq :=
    mul_le_mul_of_nonneg_left hvJ
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6) hC.le) hA.le)
  dsimp only [U, V]
  nlinarith only [hs, huq, hvq]

/-- Under GRH and for any positive epsilon, the absolute kernel zero sum of every
primitive nonprincipal character of conductor m between two and q is eventually
bounded by (1+epsilon) K.mass log q, uniformly in m and the character. For large m,
use the sharp conductor bound and monotonicity of log. For the remaining m, use the
coarse bound and let log q absorb its fixed maximum. This supplies the mass estimate
for the primitive character inducing a character of ambient modulus q in Lemma 6.1. -/
theorem exists_uniform_kernelZeroSum_le_mass_ambient (K : MellinKernel)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q m : ℕ) [NeZero m],
          Q ≤ q →
            2 ≤ m →
            m ≤ q →
            ∀ (χ : DirichletCharacter ℂ m),
              χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 → (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ (1 + ε) * K.mass * Real.log q := by
  obtain ⟨N, hN, hb⟩ := exists_uniform_kernelZeroSum_le_mass K hGRH ε hε
  obtain ⟨D, B, hD, _, hc⟩ := exists_uniform_kernelZeroSum_le_log_add K
  have hM : 0 < (1 + ε) * K.mass := mul_pos (by linarith only [hε]) (mass_pos K)
  have hl :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      ((D * Real.log N + B) / ((1 + ε) * K.mass))
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hl
  refine ⟨max 2 R, Nat.le_max_left _ _, ?_⟩
  intro q m _ hq hm hmq χ hp hne hinv
  have hmp : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 0 < 2) hm)
  by_cases hNm : N ≤ m
  · exact
      (hb m hNm χ hp hne hinv).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log hmp (by exact_mod_cast hmq)) hM.le)
  · have hmN : m ≤ N := Nat.le_of_not_ge hNm
    have hml :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hmp (show (m : ℝ) ≤ (N : ℝ) by exact_mod_cast hmN))
        hD
    have hsmall := hc m hm χ (hGRH m χ hp) hp hne hinv
    have hlarge := (div_le_iff₀ hM).mp (hR q ((Nat.le_max_right 2 R).trans hq))
    simp only [Function.comp_apply] at hlarge
    nlinarith only [hsmall, hml, hlarge]

end PseudoPrime.LLS.PaperStatements.MellinKernel
