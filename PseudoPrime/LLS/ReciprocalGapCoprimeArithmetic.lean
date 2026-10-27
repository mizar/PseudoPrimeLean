/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterCoprimeTriviality
public import PseudoPrime.LLS.ReciprocalGapPrincipalLower

/-! # Selected unit-supported lower bounds under coprime prime triviality -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For x>0 and triviality on coprime primes through x, the real character sum
is exactly the principal-weight sum restricted to indices coprime to q.
Use the zero-or-one prime-power values and the finite Mangoldt prefix identity.
This retains all nonunit zeros without assuming triviality at ramified primes. -/
theorem reciprocalGapCharacterSum_re_eq_coprime_of_trivial {h x : ℝ} (hx : 0 < x) {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p q → χ p = 1) :
    (reciprocalGapCharacterSum h χ x).re =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ Nat.Coprime n q),
        reciprocalGapPrincipalWeight h x n := by
  let w := fun n : ℕ ↦ (1 / Real.sqrt x) * ((1 - ((n : ℝ) / x) ^ h) / h)
  have hs :=
    AnalyticNumberTheory.Arithmetic.character_mangoldt_prefix_re_eq_coprime χ (Finset.Ioc 0 ⌊x⌋₊) w
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx.le)) hsmall
  rw [reciprocalGapCharacterSum, Complex.re_sum]
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (χ n).re * ArithmeticFunction.vonMangoldt n * w n := by
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [w]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    _ = _ := hs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      unfold reciprocalGapPrincipalWeight
      dsimp only [w]
      ring

/-- For h>=0,x>0 and coprime prime triviality through x, the principal weights on
any unit-supported subset below x bound the real character sum from below.
Use the exact coprime sum and nonnegativity of omitted weights. -/
theorem sum_reciprocalGapPrincipalWeight_le_of_coprime_trivial {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x)
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p q → χ p = 1) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n q) :
    (∑ n ∈ B, reciprocalGapPrincipalWeight h x n) ≤ (reciprocalGapCharacterSum h χ x).re := by
  rw [reciprocalGapCharacterSum_re_eq_coprime_of_trivial hx χ hsmall]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (fun n hn ↦ Finset.mem_filter.mpr ⟨hB hn, hcop n hn⟩)
      (fun n hn _ ↦
        reciprocalGapPrincipalWeight_nonneg hh hx n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2).trans
            (Nat.floor_le hx.le)))

/-- For h,x>0 and coprime prime triviality through x, selected unit-supported
Mangoldt lower endpoints and power upper endpoints at most one bound the character sum
from below. Compare terms and retain only the selected coprime contributions. -/
theorem sum_lower_le_reciprocalGap_character_of_coprime_trivial {h x : ℝ} (hh : 0 < h) (hx : 0 < x)
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p q → χ p = 1) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n q) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1) :
    (∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) ≤ (reciprocalGapCharacterSum h χ x).re := by
  have hp :
    (∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) ≤
      ∑ n ∈ B, reciprocalGapPrincipalWeight h x n := by
    refine Finset.sum_le_sum (fun n hn ↦ ?_)
    exact
      mul_le_mul (div_le_div_of_nonneg_right (hlo n hn) (Real.sqrt_nonneg x))
        (div_le_div_of_nonneg_right (sub_le_sub_left (hu n hn) 1) hh.le)
        (div_nonneg (sub_nonneg.mpr (hu1 n hn)) hh.le)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg x))
  exact
    hp.trans (sum_reciprocalGapPrincipalWeight_le_of_coprime_trivial hh.le hx χ hsmall B hB hcop)

/-- For h>=0 and arbitrary real x, Mangoldt lower endpoints and power upper
endpoints at most one bound the weights on a selected finite support from below.
Compare products termwise. Positivity or support constraints on x are not needed
for this algebraic certificate; witness applications impose them separately. -/
theorem sum_lower_le_reciprocalGap_selectedWeight {h x : ℝ} (hh : 0 ≤ h) (B : Finset ℕ)
    (lo u : ℕ → ℝ) (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1) :
    (∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) ≤
      ∑ n ∈ B, reciprocalGapPrincipalWeight h x n := by
  refine Finset.sum_le_sum (fun n hn ↦ ?_)
  exact
    mul_le_mul (div_le_div_of_nonneg_right (hlo n hn) (Real.sqrt_nonneg x))
      (div_le_div_of_nonneg_right (sub_le_sub_left (hu n hn) 1) hh)
      (div_nonneg (sub_nonneg.mpr (hu1 n hn)) hh)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg x))

end PseudoPrime.LLS.PaperStatements
