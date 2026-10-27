/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterAmbientTriviality
public import PseudoPrime.LLS.ReciprocalGapCoprimeArithmetic

/-! # Principal factors and exact additional-exclusion losses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The Mangoldt-free principal factor (1/sqrt(x))*(1-(n/x)^h)/h.
Inputs are totalized. Nonnegativity requires h>=0,x>0 and n<=x.
This supplies weights for additional-exclusion loss identities. -/
noncomputable def reciprocalGapPrincipalFactor (h x : ℝ) (n : ℕ) : ℝ :=
  (1 / Real.sqrt x) * ((1 - ((n : ℝ) / x) ^ h) / h)

/-- The principal-weight sum on positive indices below x coprime to q but not N.
Inputs h,q,N,x are totalized. This is the exact additional-exclusion budget
subtracted from a selected allowed principal sum. -/
noncomputable def reciprocalGapAdditionalNonunitWeight (h : ℝ) (q N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ Nat.Coprime n q ∧ ¬Nat.Coprime n N),
    reciprocalGapPrincipalWeight h x n

/-- For h>=0,x>0 and n<=x, the principal factor is nonnegative.
Use the power bound on [0,1] and nonnegative denominators.
This verifies the sign hypotheses of finite weighted loss comparisons. -/
theorem reciprocalGapPrincipalFactor_nonneg {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) (n : ℕ)
    (hn : (n : ℝ) ≤ x) : 0 ≤ reciprocalGapPrincipalFactor h x n := by
  have hp := Real.rpow_le_one (div_nonneg (Nat.cast_nonneg n) hx.le) ((div_le_one hx).mpr hn) hh
  exact mul_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg x)) (div_nonneg (sub_nonneg.mpr hp) hh)

/-- For arbitrary h,x,n, multiplying the principal factor by Lambda(n) gives
the principal weight. Rearrange real field operations without division cancellation.
This connects generic arithmetic prefixes to the Mellin arithmetic normalization. -/
theorem mangoldt_mul_reciprocalGapPrincipalFactor (h x : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * reciprocalGapPrincipalFactor h x n =
      reciprocalGapPrincipalWeight h x n := by
  unfold reciprocalGapPrincipalFactor reciprocalGapPrincipalWeight
  ring

/-- For any character and real h,x, the real character sum is the finite sum
of Re chi(n) times the principal weights. Expand complex real parts and rearrange.
No positivity, GRH or prime-triviality assumptions are needed. -/
theorem reciprocalGapCharacterSum_re_eq_weighted {q : ℕ} (χ : DirichletCharacter ℂ q) (h x : ℝ) :
    (reciprocalGapCharacterSum h χ x).re =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (χ n).re * reciprocalGapPrincipalWeight h x n := by
  rw [reciprocalGapCharacterSum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold reciprocalGapPrincipalWeight
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- If q divides N, h>=0,x>0 and primes coprime to N through x have character value
one, a selected N-coprime principal sum minus the exact additional-nonunit weight
bounds the real character sum below. Apply the generic weighted arithmetic comparison. -/
theorem selected_reciprocalGap_sum_sub_loss_le_character {q N : ℕ} (hqN : q ∣ N) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) (χ : DirichletCharacter ℂ q)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) :
    (∑ n ∈ B, reciprocalGapPrincipalWeight h x n) - reciprocalGapAdditionalNonunitWeight h q N x ≤
      (reciprocalGapCharacterSum h χ x).re := by
  have hs :=
    AnalyticNumberTheory.Arithmetic.selected_mangoldt_sub_loss_le_character hqN χ
      (Finset.Ioc 0 ⌊x⌋₊) B (reciprocalGapPrincipalFactor h x) hB hcop
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx.le))
      (fun n hn ↦
        reciprocalGapPrincipalFactor_nonneg hh hx n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx.le)))
      hsmall
  simp only [AnalyticNumberTheory.Arithmetic.additionalNonunitMangoldtPrefix, mul_assoc,
    mangoldt_mul_reciprocalGapPrincipalFactor] at hs
  rw [reciprocalGapCharacterSum_re_eq_weighted]
  exact hs

/-- Under the same ambient prime-triviality data, certified Mangoldt lower endpoints
and power upper endpoints at most one give a selected lower sum minus the exact exclusion
cost below the character sum. Compose the algebraic selected-weight certificate. -/
theorem selected_reciprocalGap_lower_sub_loss_le_character {q N : ℕ} (hqN : q ∣ N) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) (χ : DirichletCharacter ℂ q)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1) :
    (∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) -
        reciprocalGapAdditionalNonunitWeight h q N x ≤
      (reciprocalGapCharacterSum h χ x).re := by
  have hl := sum_lower_le_reciprocalGap_selectedWeight hh B lo u hlo hu hu1
  exact
    (sub_le_sub_right hl (reciprocalGapAdditionalNonunitWeight h q N x)).trans
      (selected_reciprocalGap_sum_sub_loss_le_character hqN hh hx χ hsmall B hB hcop)

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For h>=0,x>0 and any q,N, the additional-nonunit weight budget is nonnegative.
All selected indices are below x and hence have nonnegative principal weights.
This supports coarsening exact exclusion budgets safely. -/
theorem reciprocalGapAdditionalNonunitWeight_nonneg {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) (q N : ℕ) :
    0 ≤ reciprocalGapAdditionalNonunitWeight h q N x := by
  exact
    Finset.sum_nonneg
      (fun n hn ↦
        reciprocalGapPrincipalWeight_nonneg hh hx n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2).trans
            (Nat.floor_le hx.le)))

/-- For equal character and exclusion moduli, the additional-nonunit budget is zero.
Its filter requires coprimality and its negation simultaneously. This recovers the
previous coprime witness setting without extra losses. -/
theorem reciprocalGapAdditionalNonunitWeight_same (h x : ℝ) (q : ℕ) :
    reciprocalGapAdditionalNonunitWeight h q q x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  exact False.elim ((Finset.mem_filter.mp hn).2.2 (Finset.mem_filter.mp hn).2.1)

end PseudoPrime.LLS.PaperStatements
