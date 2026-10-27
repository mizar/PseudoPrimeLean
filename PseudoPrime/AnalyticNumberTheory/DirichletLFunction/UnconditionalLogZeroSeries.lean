/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalGenusMass
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogHalfZeros

/-! # Unconditional logarithmic completed-zero series and height exhaustion -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a nonprincipal character and real scale at least one, each logarithmic
completed-zero term is bounded by the scale times its inverse-square divisor mass.
The zero-free right half-plane bounds the complex-power norm by the scale.
This supplies an unconditional summable majorant. -/
theorem norm_completedLogZeroTerm_le_unconditionally {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (ρ : ℂ) :
    ‖completedLogZeroTerm χ x ρ‖ ≤
      x * ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ) := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hDzero : D = 0
  · change ‖(D : ℂ) * (x : ℂ) ^ ρ / ρ ^ 2‖ ≤ x * ((D : ℝ) / Complex.normSq ρ)
    simp only [hDzero, Int.cast_zero, zero_mul, zero_div, norm_zero, mul_zero, le_refl]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hDzero
    have hre := completedLFunction_zero_re_lt_one hne hz
    have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (χ.differentiable_completedLFunction hne).analyticAt z
    have hD : 0 ≤ (D : ℝ) := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    have hpow : ‖(x : ℂ) ^ ρ‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      have h := Real.rpow_le_rpow_of_exponent_le hx hre.le
      simpa only [Real.rpow_one] using h
    change ‖(D : ℂ) * (x : ℂ) ^ ρ / ρ ^ 2‖ ≤ x * ((D : ℝ) / Complex.normSq ρ)
    rw [norm_div, norm_mul, norm_pow, Complex.norm_intCast, abs_of_nonneg hD, ←
      Complex.normSq_eq_norm_sq]
    have h :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD) (Complex.normSq_nonneg ρ)
    exact h.trans_eq (by ring)

/-- For a primitive nonprincipal character and real scale at least one, the
completed logarithmic zero contributions are absolutely summable without RH.
Dominate their norms by the scale times the unconditional inverse-square mass.
This justifies passage from finite logarithmic residue sums to the full zero sum. -/
theorem summable_norm_completedLogZeroTerm_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) : Summable (fun ρ : ℂ ↦ ‖completedLogZeroTerm χ x ρ‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_completedLogZeroTerm_le_unconditionally hne hx)
    ((summable_divisor_div_normSq_unconditionally hq hp hne hinv).mul_left x)

/-- A nonzero completed logarithmic zero term comes from a zero in the open critical
strip, distinct from zero and one, with nonvanishing gamma factor and vanishing
ordinary L-value. Use the unconditional zero-free half-planes and gamma nonvanishing.
This identifies the support used in finite contour ledgers without RH. -/
theorem completedLogZeroTerm_ne_zero_facts_unconditionally {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} {ρ : ℂ}
    (hnz : completedLogZeroTerm χ x ρ ≠ 0) :
    0 < ρ.re ∧
      ρ.re < 1 ∧ ρ ≠ 0 ∧ ρ ≠ 1 ∧ DirichletCharacter.gammaFactor χ ρ ≠ 0 ∧ χ.LFunction ρ = 0 := by
  have hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ ≠ 0 := by
    intro h
    apply hnz
    simp only [completedLogZeroTerm, h, Int.cast_zero, zero_mul, zero_div]
  have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
  have hpos := completedLFunction_zero_re_pos hp hinv hz
  have hlt := completedLFunction_zero_re_lt_one hne hz
  have hzero : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  have hone : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hlt
    exact (lt_irrefl 1) hlt
  refine ⟨hpos, hlt, hzero, hone, gammaFactor_ne_zero_of_pos_re hpos, ?_⟩
  rw [dirichletLFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hzero), hz, zero_div]

/-- Every nonzero completed logarithmic zero term eventually belongs to the finite
ledger on any cofinal symmetric height sequence with fixed negative half-integer
left edge and right edge two. Use its open-critical-strip support and the height
bound. This retains the existing residue ledger and analytic multiplicities. -/
theorem eventually_completedLogZeroTerm_mem_unconditional_height_ledger {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (T : ℕ → ℝ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (A : ℕ) {x : ℝ} {ρ : ℂ}
    (hnz : completedLogZeroTerm χ x ρ ≠ 0) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ρ ∈
        completedLogRectangleLedger χ hne (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) - T k * Complex.I)
          (((2 : ℝ) : ℂ) + T k * Complex.I) := by
  obtain ⟨hrpos, hrlt, hzero, hone, hgamma, hLzero⟩ :=
    completedLogZeroTerm_ne_zero_facts_unconditionally hp hne hinv hnz
  filter_upwards [hT.eventually_ge_atTop (|ρ.im| + 1)] with k hk
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_erase.mpr ⟨hzero, Finset.mem_erase.mpr ⟨hone, ?_⟩⟩, hgamma⟩
  apply mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
  refine ⟨?_, Or.inr (Or.inr hLzero)⟩
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    mul_zero, sub_zero, Complex.add_re, add_zero, Complex.sub_im, Complex.mul_im, Complex.I_im,
    mul_one, zero_sub, Complex.add_im, zero_add]
  refine ⟨Set.Icc_subset_uIcc ⟨?_, ?_⟩, Set.Icc_subset_uIcc ⟨?_, ?_⟩⟩
  · linarith only [hrpos, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  · linarith only [hrlt]
  · linarith only [hk, neg_abs_le ρ.im]
  · linarith only [hk, le_abs_self ρ.im]

/-- For every cofinal real height sequence, every fixed negative half-integer left
edge, and real scale at least one, finite completed logarithmic zero ledgers converge
to the full zero sum. Combine unconditional absolute convergence with eventual
support membership. This removes RH from the zero-sum exhaustion step. -/
theorem tendsto_completedLogZero_unconditional_height_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (T : ℕ → ℝ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (A : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ∑
          ρ ∈
            completedLogRectangleLedger χ hne (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) - T k * Complex.I)
              (((2 : ℝ) : ℂ) + T k * Complex.I),
          completedLogZeroTerm χ x ρ)
      Filter.atTop (nhds (∑' ρ : ℂ, completedLogZeroTerm χ x ρ)) :=
  Analysis.tendsto_sum_of_eventually_mem_support _
    (summable_norm_completedLogZeroTerm_unconditionally hq hp hne hinv hx) _
    (fun _ hnz ↦
      eventually_completedLogZeroTerm_mem_unconditional_height_ledger hp hne hinv T hT A hnz)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
