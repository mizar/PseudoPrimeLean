/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogZeroTail

/-! # Unconditional finite-height error bounds for logarithmically weighted sums -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A nonzero half-scale completed-zero term of bounded ordinate lies in the
finite completed-zero ledger with fixed left edge `-5/2` and right edge two.
Primitivity and nonprincipality put the zero in the open critical strip.
This identifies the finite low-height set without RH. -/
theorem completedLogHalfZeroTerm_mem_height_ledger_unconditionally {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x T : ℝ}
    {ρ : ℂ} (hnz : completedLogHalfZeroTerm χ x ρ ≠ 0) (hheight : |ρ.im| ≤ T) :
    ρ ∈
      completedZerosInRectangle χ hne (unconditionalHeightLowerCorner 2 T)
        (unconditionalHeightUpperCorner T) := by
  have hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ ≠ 0 := by
    intro h
    apply hnz
    simp only [completedLogHalfZeroTerm, h, Int.cast_zero, zero_mul, zero_div]
  have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
  have hrpos := completedLFunction_zero_re_pos hp hinv hz
  have hrlt := completedLFunction_zero_re_lt_one hne hz
  apply mem_completedZerosInRectangle_iff.mpr ⟨?_, hz⟩
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
  simp only [unconditionalHeightLowerCorner, unconditionalHeightUpperCorner, Complex.sub_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, sub_zero,
    Complex.add_re, add_zero, Complex.sub_im, Complex.mul_im, Complex.I_im, mul_one, zero_sub,
    Complex.add_im, zero_add, Nat.cast_ofNat]
  refine ⟨Set.Icc_subset_uIcc ⟨?_, ?_⟩, Set.Icc_subset_uIcc (abs_le.mp hheight)⟩
  · linarith only [hrpos]
  · linarith only [hrlt]

/-- For a primitive nonprincipal character and its nonprincipal inverse, split the
absolutely convergent half-scale zero sum into a finite height ledger and a high
ordinate tail. The scale is at least two; no zero-free boundary is required.
A pointwise indicator comparison preserves boundary zeros and multiplicity. -/
theorem tsum_norm_half_le_finite_height_add_tail_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 2 ≤ x) (T : ℝ) :
    (∑' ρ : ℂ, ‖completedLogHalfZeroTerm χ x ρ‖) ≤
      (∑
          ρ ∈
            completedZerosInRectangle χ hne (unconditionalHeightLowerCorner 2 T)
              (unconditionalHeightUpperCorner T),
          ‖completedLogHalfZeroTerm χ x ρ‖) +
        ∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfZeroTerm χ x ρ‖ else 0 := by
  classical
  let S :=
    completedZerosInRectangle χ hne (unconditionalHeightLowerCorner 2 T)
      (unconditionalHeightUpperCorner T)
  let f : ℂ → ℝ := fun ρ ↦ ‖completedLogHalfZeroTerm χ x ρ‖
  let lo : ℂ → ℝ := fun ρ ↦ if ρ ∈ S then f ρ else 0
  let hi : ℂ → ℝ := fun ρ ↦ if T ≤ |ρ.im| then f ρ else 0
  have hs : Summable f := (summable_completedLogHalfZeroTerm_unconditionally hq hp hne hinv hx).norm
  have hlo : Summable lo := by
    apply (hs.indicator (S : Set ℂ)).congr
    intro ρ
    by_cases hm : ρ ∈ S
    · rw [Set.indicator_of_mem hm]
      exact (ite_eq_left hm).symm
    · rw [Set.indicator_of_notMem hm]
      exact (ite_eq_right hm).symm
  have hhi : Summable hi := by
    apply (hs.indicator {ρ : ℂ | T ≤ |ρ.im|}).congr
    intro ρ
    by_cases ht : T ≤ |ρ.im|
    · rw [Set.indicator_of_mem (s := {ρ : ℂ | T ≤ |ρ.im|}) ht]
      exact (ite_eq_left ht).symm
    · rw [Set.indicator_of_notMem (s := {ρ : ℂ | T ≤ |ρ.im|}) ht]
      exact (ite_eq_right ht).symm
  have hpoint (ρ : ℂ) : f ρ ≤ lo ρ + hi ρ := by
    by_cases hm : ρ ∈ S
    · simp only [lo, ite_eq_left hm]
      exact le_add_of_nonneg_right (ite_nonneg (norm_nonneg _) le_rfl)
    · by_cases hz : completedLogHalfZeroTerm χ x ρ = 0
      · simp only [f, lo, hi, hz, norm_zero, ite_self, add_zero, le_refl]
      · have ht : T ≤ |ρ.im| := by
          by_contra ht
          exact
            hm
              (completedLogHalfZeroTerm_mem_height_ledger_unconditionally hp hne hinv hz
                (le_of_lt (lt_of_not_ge ht)))
        simp only [lo, hi, ite_eq_right hm, ite_eq_left ht, zero_add, le_refl]
  have hlowSum : (∑' ρ : ℂ, lo ρ) = ∑ ρ ∈ S, f ρ := by
    rw [tsum_eq_sum (s := S) (fun ρ hρ ↦ ite_eq_right hρ)]
    exact Finset.sum_congr rfl (fun ρ hρ ↦ ite_eq_left hρ)
  have hb := hs.tsum_le_tsum hpoint (hlo.add hhi)
  rw [hlo.tsum_add hhi, hlowSum] at hb
  exact hb

/-- One positive absolute constant bounds the half-scale character sum by a finite
low-height completed-zero sum, an explicit conductor-height tail, and the origin
and trivial-zero remainder. The character and its inverse are nonprincipal and
the character is primitive; modulus and height are at least two and `x > 2`.
Combine the unconditional explicit formula, finite ledger comparison, and uniform
tail estimate. This is the quantitative finite-height interface for theta supply. -/
theorem exists_norm_characterLogWeightedSum_half_le_finite_height_unconditionally :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ.IsPrimitive →
                ∀ (hne : χ ≠ 1),
                  χ⁻¹ ≠ 1 →
                    ∀ (x : ℝ),
                      2 < x →
                        ∀ (H : ℕ),
                          2 ≤ H →
                            ‖Arithmetic.characterLogWeightedSum x χ -
                                  Arithmetic.characterLogWeightedSum (x / 2) χ‖ ≤
                              ((∑
                                    ρ ∈
                                      completedZerosInRectangle χ hne
                                        (unconditionalHeightLowerCorner 2 (H + 1))
                                        (unconditionalHeightUpperCorner (H + 1)),
                                    ‖completedLogHalfZeroTerm χ x ρ‖) +
                                  (24 * x * K * Real.log q / ((H - 1 : ℕ) : ℝ) +
                                    192 * x * K * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3))) +
                                ‖logarithmicHalfRemainder hne x‖ := by
  obtain ⟨K, hK, htail⟩ := exists_tsum_norm_completedLogHalfZeroTerm_tail_bound_unconditionally
  refine ⟨K, hK, ?_⟩
  intro q _ hq χ hp hne hinv x hx H hH
  have hsplit :=
    tsum_norm_half_le_finite_height_add_tail_unconditionally hq hp hne hinv hx.le (H + 1)
  have ht := htail q hq χ hp hne hinv x hx.le H hH
  have ht' :
    (∑' ρ : ℂ, if (H : ℝ) + 1 ≤ |ρ.im| then ‖completedLogHalfZeroTerm χ x ρ‖ else 0) ≤
      24 * x * K * Real.log q / ((H - 1 : ℕ) : ℝ) +
        192 * x * K * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  exact
    (norm_characterLogWeightedSum_half_le_unconditionally hq hp hne hinv hx).trans
      (add_le_add (hsplit.trans (add_le_add le_rfl ht')) le_rfl)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
