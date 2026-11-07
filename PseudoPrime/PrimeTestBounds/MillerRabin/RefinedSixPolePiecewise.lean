/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePaperRootWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Log8

/-! # Piecewise refined Miller--Rabin coefficient -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The high-range residual allowance: `3`, `1`, or `0` at the paper thresholds.
It selects the corresponding fourth-power root cutoff. -/
noncomputable def refinedPaperAllowance (L : ℝ) : ℝ :=
  if L < 3000 then 3 else if L < 10000 then 1 else 0

/-- The paper coefficient `C_new(L)`: three tenths below `1000`, and the selected
root cutoff divided by `L²` above that threshold. The witness theorem multiplies it by `L²`. -/
noncomputable def refinedPaperCoefficient (L : ℝ) : ℝ :=
  if L < 1000 then 3 / 10 else refinedPaperBound L (refinedPaperAllowance L) / L ^ 2

/-- Every selected residual allowance lies between zero and three. Evaluate the
three branches of the piecewise definition. -/
theorem refined_allowance_range (L : ℝ) :
    0 ≤ refinedPaperAllowance L ∧ refinedPaperAllowance L ≤ 3 := by
  dsimp only [refinedPaperAllowance]
  split_ifs <;> constructor <;> norm_num only

/-- Above the first threshold, multiplying the coefficient by `L²` recovers the
selected paper cutoff. The threshold guarantees a nonzero denominator. -/
theorem refined_piecewise_high {L : ℝ} (hL : 1000 ≤ L) :
    refinedPaperCoefficient L * L ^ 2 = refinedPaperBound L (refinedPaperAllowance L) := by
  have hL0 : L ≠ 0 := (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1000) hL).ne'
  rw [refinedPaperCoefficient, ite_eq_right (not_lt_of_ge hL),
    div_mul_cancel₀ _ (pow_ne_zero 2 hL0)]

/-- Under GRH, the uniform three-prime branch has a prime witness bounded by the
piecewise coefficient when the selected residual certificate holds. Rewrite the
coefficient as the paper root cutoff and apply the root witness theorem. -/
theorem refined_pair_piecewise_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : 1000 ≤ Real.log n)
    (hres :
      refinedPaperResidual (Real.log n)
          (refinedPaperRoot (Real.log n) (refinedPaperAllowance (Real.log n)) ^ 2) ≤
        (27 / 25 : ℝ) ^ 5 * refinedPaperAllowance (Real.log n)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ refinedPaperCoefficient (Real.log n) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  rw [refined_piecewise_high hL]
  exact
    refined_pair_root_witness hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
      hvq hvr hL (refined_allowance_range _).1 hres

/-- Under GRH, every odd composite with `8 ≤ log n < 1000` has a prime witness
bounded by the piecewise coefficient. This is the existing three-tenths theorem
rewritten using the low-range branch of the coefficient. -/
theorem refined_piecewise_low_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ refinedPaperCoefficient (Real.log n) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  rw [refinedPaperCoefficient, ite_eq_left hU]
  exact exists_prime_reject_03_log8 hn ho hc hGRH hL

/-- The four branches of the coefficient agree exactly with the paper's thresholds.
Evaluate the piecewise allowance and coefficient at the stated interval endpoints. -/
theorem refined_piecewise_branches (L : ℝ) :
    (L < 1000 → refinedPaperCoefficient L = 3 / 10) ∧
      (1000 ≤ L → L < 3000 → refinedPaperCoefficient L = refinedPaperBound L 3 / L ^ 2) ∧
      (3000 ≤ L → L < 10000 → refinedPaperCoefficient L = refinedPaperBound L 1 / L ^ 2) ∧
      (10000 ≤ L → refinedPaperCoefficient L = refinedPaperBound L 0 / L ^ 2) := by
  constructor
  · intro h
    rw [refinedPaperCoefficient, ite_eq_left h]
  constructor
  · intro h1 h2
    rw [refinedPaperCoefficient, ite_eq_right (not_lt_of_ge h1), refinedPaperAllowance,
      ite_eq_left h2]
  constructor
  · intro h1 h2
    rw [refinedPaperCoefficient,
      ite_eq_right (not_lt_of_ge (by linarith only [h1] : (1000 : ℝ) ≤ L)), refinedPaperAllowance,
      ite_eq_right (not_lt_of_ge h1), ite_eq_left h2]
  · intro h
    rw [refinedPaperCoefficient,
      ite_eq_right (not_lt_of_ge (by linarith only [h] : (1000 : ℝ) ≤ L)), refinedPaperAllowance,
      ite_eq_right (not_lt_of_ge (by linarith only [h] : (3000 : ℝ) ≤ L)),
      ite_eq_right (not_lt_of_ge h)]

end PseudoPrime.PrimeTestBounds.MillerRabin
