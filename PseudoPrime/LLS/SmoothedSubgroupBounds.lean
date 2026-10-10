/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements
public import PseudoPrime.LLS.SubgroupKernelComparison

/-!
# From smoothed character estimates to subgroup comparisons

Lemma 6.1 bounds the real annihilator average by one principal main term and
`H.index - 1` nonprincipal contributions. Combining this estimate with subgroup
orthogonality bounds the finite principal sum under the no-small-prime hypothesis.
The analytic estimates and the passage from the finite sum to its integral remain
explicit prerequisites, rather than assumed proofs of the numbered statements.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For a nonempty finite type, the number of points other than one chosen point,
cast to the reals, is the real cardinality minus one. This normalizes the count
of nonprincipal characters in the finite average. -/
private theorem cast_card_sub_one {ι : Type*} [Fintype ι] (a : ι) :
    ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
  simpa only [Nat.cast_one] using
    (Nat.cast_sub (R := ℝ)
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨a⟩))))

/-- Bound a finite sum excluding a distinguished point by its number of terms
times a common upper bound. Sum the pointwise bound and count the erased set.
This handles the nonprincipal part of the character average. -/
private theorem sum_erase_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (f : ι → ℝ) {B : ℝ}
    (hb : ∀ i, i ≠ a → f i ≤ B) :
    (∑ i ∈ Finset.univ.erase a, f i) ≤ (Fintype.card ι - 1 : ℕ) * B := by
  calc
    _ ≤ ∑ _ ∈ Finset.univ.erase a, B :=
      Finset.sum_le_sum (fun i hi ↦ hb i (Finset.mem_erase.mp hi).1)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ]

/-- One distinguished main term and uniformly bounded other terms give the total
bound `A + (card - 1) B + card E`. Split off the distinguished point and combine
the bounds. This keeps the principal and nonprincipal counts exact. -/
private theorem sum_le_of_distinguished {ι : Type*} [Fintype ι] (a : ι) (f : ι → ℝ) {A B E : ℝ}
    (ha : f a ≤ A + E) (hb : ∀ i, i ≠ a → f i ≤ B + E) :
    ∑ i, f i ≤ A + ((Fintype.card ι : ℝ) - 1) * B + Fintype.card ι * E := by
  classical
  have he := sum_erase_le a f hb
  rw [cast_card_sub_one a] at he
  have hs := Finset.sum_erase_add (Finset.univ : Finset ι) f (Finset.mem_univ a)
  linarith only [he, ha, hs]

/-- A norm bound on a complex error bounds the real part above by the real main
term plus the error. Apply the real-part norm inequality and rearrange. This
converts the principal estimate of Lemma 6.1 to a scalar inequality. -/
private theorem re_le_add_of_norm_sub_le (z w : ℂ) {E : ℝ} (he : ‖z - w‖ ≤ E) :
    z.re ≤ w.re + E := by
  have h := (Complex.re_le_norm (z - w)).trans he
  rw [Complex.sub_re] at h
  linarith only [h]

/-- A signed contribution with coefficient of absolute value at most one and
bounded remainder is at most `B + E` when `B` is nonnegative. This is the scalar
upper bound for each nonprincipal estimate of Lemma 6.1. -/
private theorem le_of_bounded_theta {S B E θ r : ℝ} (he : S = θ * B + r) (ht : |θ| ≤ 1)
    (hr : |r| ≤ E) (hB : 0 ≤ B) : S ≤ B + E := by
  rw [he]
  calc
    _ ≤ 1 * B + E := add_le_add (mul_le_mul_of_nonneg_right (abs_le.mp ht).2 hB) (abs_le.mp hr).2
    _ = _ := by rw [one_mul]

variable {q : ℕ} [NeZero q]

/-- A principal norm estimate and signed nonprincipal estimates with common
nonnegative contribution `B` and error `E` bound the annihilator average by
`Re K(1/2) sqrt x + (index - 1) B + index E`. Split off the principal character
and use exact annihilator cardinality. This is the analytic side of Proposition 6.1. -/
theorem average_le_of_smoothed_estimates (K : MellinKernel) (H : Subgroup (ZMod q)ˣ) (x B E : ℝ)
    (hB : 0 ≤ B)
    (hp :
      ‖(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ q) x n) -
            K.function (1 / 2) * (Real.sqrt x : ℂ)‖ ≤
        E)
    (hn :
      ∀ χ : NumberTheory.subgroupAnnihilator H,
        χ.val ≠ 1 → ∃ θ r : ℝ, |θ| ≤ 1 ∧ |r| ≤ E ∧ (∑' n : ℕ, K.summand χ.val x n).re = θ * B + r) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, (∑' n : ℕ, K.summand χ.val x n).re ≤
      (K.function (1 / 2)).re * Real.sqrt x + ((H.index : ℝ) - 1) * B + H.index * E := by
  classical
  have hp' := re_le_add_of_norm_sub_le _ _ hp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hp'
  have he :=
    sum_le_of_distinguished (1 : NumberTheory.subgroupAnnihilator H)
      (fun χ ↦ (∑' n : ℕ, K.summand χ.val x n).re) hp'
      (fun χ hχ ↦ by
        obtain ⟨θ, r, ht, hr, he⟩ := hn χ (fun heq ↦ hχ (Subtype.ext heq))
        exact le_of_bounded_theta he ht hr hB)
  simpa only [NumberTheory.card_subgroupAnnihilator] using he

/-- Assuming Lemma 6.1 and GRH, each admissible kernel has a positive error
constant and, for each positive epsilon, a modulus threshold giving the averaged
upper estimate uniformly in proper subgroups and `x ≥ 2`. Specialize the lemma
to the annihilator characters and count one principal contribution. This preserves
the precise analytic premise still needed for Proposition 6.1. -/
theorem average_le_of_lemma61 (h61 : lls_lemma61)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ ε : ℝ,
          0 < ε →
            ∃ Q : ℕ,
              3 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ H : Subgroup (ZMod q)ˣ,
                      H ≠ ⊤ →
                        ∀ x : ℝ,
                          2 ≤ x →
                            ∑ χ : NumberTheory.subgroupAnnihilator H,
                                (∑' n : ℕ, K.summand χ.val x n).re ≤
                              (K.function (1 / 2)).re * Real.sqrt x +
                                ((H.index : ℝ) - 1) * ((1 + ε) * Real.log q * K.mass) +
                                H.index * (C * (1 + Real.log q * Real.log x / Real.sqrt x)) := by
  obtain ⟨C, hC, hh⟩ := h61 hGRH K
  refine ⟨C, hC, ?_⟩
  intro ε hε
  obtain ⟨Q, hQ, hq⟩ := hh ε hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hlevel H hH x hx
  have hlog : 0 ≤ Real.log q :=
    Real.log_nonneg
      (Nat.one_le_cast.mpr ((show (1 : ℕ) ≤ 3 from by decide).trans (hQ.trans hlevel)))
  have hB : 0 ≤ (1 + ε) * Real.log q * K.mass :=
    mul_nonneg (mul_nonneg (add_nonneg zero_le_one hε.le) hlog) (mass_pos K).le
  apply average_le_of_smoothed_estimates K H x _ _ hB
  · exact
      (hq q hlevel H hH 1
            ((NumberTheory.mem_subgroupAnnihilator_iff H 1).mp
              (NumberTheory.subgroupAnnihilator H).one_mem)
            x hx).2.1
        rfl
  · intro χ hχ
    simpa only [mul_assoc] using
      (hq q hlevel H hH χ.val ((NumberTheory.mem_subgroupAnnihilator_iff H χ.val).mp χ.property) x
            hx).2.2
        hχ

/-- Assuming Lemma 6.1 and GRH, the no-small-prime hypothesis bounds the finite
principal smoothed sum by one principal main term, `index - 1` nonprincipal
contributions and `index` error terms. The constant and threshold are uniform in
proper subgroups and cutoffs. Combine the proved orthogonality lower bound with
the averaged analytic upper bound. This is the finite-sum stage of Proposition 6.1. -/
theorem principal_sum_le_of_lemma61 (h61 : lls_lemma61)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ ε : ℝ,
          0 < ε →
            ∃ Q : ℕ,
              3 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ H : Subgroup (ZMod q)ˣ,
                      H ≠ ⊤ →
                        ∀ x : ℝ,
                          2 ≤ x →
                            ∀ X : ℝ,
                              (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) →
                                (H.index : ℝ) *
                                    ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
                                      (K.summand (1 : DirichletCharacter ℂ q) x n).re ≤
                                  (K.function (1 / 2)).re * Real.sqrt x +
                                    ((H.index : ℝ) - 1) * ((1 + ε) * Real.log q * K.mass) +
                                    H.index *
                                      (C * (1 + Real.log q * Real.log x / Real.sqrt x)) := by
  obtain ⟨C, hC, hh⟩ := average_le_of_lemma61 h61 hGRH K
  refine ⟨C, hC, ?_⟩
  intro ε hε
  obtain ⟨Q, hQ, hq⟩ := hh ε hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hlevel H hH x hx X hsmall
  exact
    (principal_sum_le_average_of_noSmallPrimes K H
          (lt_of_lt_of_le (show (0 : ℝ) < 2 by norm_num only) hx) hsmall).trans
      (hq q hlevel H hH x hx)

omit [NeZero q] in
/-- Suppose the finite principal sum has the averaged upper bound with contribution
`B` and error `E`, and its integral main term has a lower bound with error `D`.
Then the kernel expression in Proposition 6.1 is bounded by
`(index - 1) B + index (E + D)`. Multiply the lower estimate by the nonnegative
index and eliminate the finite sum. The analytic and integral errors remain explicit. -/
theorem integral_comparison_le_of_principal_bounds (K : MellinKernel) (H : Subgroup (ZMod q)ˣ)
    (x X lambda B E D : ℝ)
    (hupper :
      (H.index : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re ≤
        (K.function (1 / 2)).re * Real.sqrt x + ((H.index : ℝ) - 1) * B + H.index * E)
    (hlower :
      Real.sqrt x *
            intervalIntegral (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) 0 lambda
              MeasureTheory.volume -
          D ≤
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) :
    ((H.index : ℝ) *
            intervalIntegral (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) 0 lambda
              MeasureTheory.volume -
          (K.function (1 / 2)).re) *
        Real.sqrt x ≤
      ((H.index : ℝ) - 1) * B + H.index * (E + D) := by
  have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg H.index)
  nlinarith only [h, hupper]

/-- For positive `X` and `lambda`, the square-root factor after choosing
`x = X / lambda` rescales to `sqrt X`. Use multiplicativity of the square root
and cancellation of the nonzero scale. This normalizes Proposition 6.1. -/
private theorem sqrt_div_mul_sqrt {X lambda : ℝ} (hX : 0 < X) (hlambda : 0 < lambda) :
    Real.sqrt (X / lambda) * Real.sqrt lambda = Real.sqrt X := by
  rw [← Real.sqrt_mul (div_nonneg hX.le hlambda.le), div_mul_cancel₀ X (ne_of_gt hlambda)]

omit [NeZero q] in
/-- For positive `X` and `lambda`, assume the finite smoothed upper estimate at
`x = X / lambda`, the integral lower estimate with error `D`, and absorption of
the total error into half of the epsilon allowance. Then the exact kernel
inequality of Proposition 6.1 holds. Eliminate the finite sum, absorb both errors,
and rescale the square root. This reduction retains the missing analytic estimates
explicitly and does not assert the unconditional numbered proposition. -/
theorem kernel_comparison_le_of_smoothed_bounds (K : MellinKernel) (H : Subgroup (ZMod q)ˣ)
    {X lambda ε E D : ℝ} (hX : 0 < X) (hlambda : 0 < lambda)
    (hupper :
      (H.index : ℝ) *
          ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) (X / lambda) n).re ≤
        (K.function (1 / 2)).re * Real.sqrt (X / lambda) +
          ((H.index : ℝ) - 1) * ((1 + ε / 2) * Real.log q * K.mass) +
          H.index * E)
    (hlower :
      Real.sqrt (X / lambda) *
            intervalIntegral (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) 0 lambda
              MeasureTheory.volume -
          D ≤
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) (X / lambda) n).re)
    (herror : (H.index : ℝ) * (E + D) ≤ ε / 2 * ((H.index : ℝ) - 1) * Real.log q * K.mass) :
    ((H.index : ℝ) *
            intervalIntegral (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) 0 lambda
              MeasureTheory.volume -
          (K.function (1 / 2)).re) *
        Real.sqrt X ≤
      (1 + ε) * Real.sqrt lambda * ((H.index : ℝ) - 1) * Real.log q * K.mass := by
  have h := integral_comparison_le_of_principal_bounds K H _ _ _ _ _ _ hupper hlower
  have hsharp :
    ((H.index : ℝ) *
            intervalIntegral (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) 0 lambda
              MeasureTheory.volume -
          (K.function (1 / 2)).re) *
        Real.sqrt (X / lambda) ≤
      (1 + ε) * ((H.index : ℝ) - 1) * Real.log q * K.mass := by
    nlinarith only [h, herror]
  have hs := mul_le_mul_of_nonneg_right hsharp (Real.sqrt_nonneg lambda)
  rw [mul_assoc, sqrt_div_mul_sqrt hX hlambda] at hs
  nlinarith only [hs]

end PseudoPrime.LLS.PaperStatements.MellinKernel
