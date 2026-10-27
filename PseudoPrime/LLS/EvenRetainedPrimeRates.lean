/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExplicitUntaperedPrimeRates

/-! # Local even-power cancellation and retained finite exception budgets -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The weight sum over even positive powers within the root cutoff.
Inputs are a cutoff, arbitrary real weight and natural base; no sign is assumed.
The sum measures the exact mass canceled at a unit square in a quadratic character. -/
noncomputable def evenPrimePowerCost (x : ℝ) (w : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    if p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ ∧ Even k then w (p ^ k) else 0

/-- For a prime coprime to q, its local cost plus twice the even-power mass
equals twice the conductor-zero local cost. Split parity and cutoff cases termwise.
This exact identity needs no positivity and precedes all analytic upper bounds. -/
theorem quadraticPrimeCost_add_even {q p : ℕ} (hp : p.Prime) (hc : Nat.Coprime p q) (x : ℝ)
    (w : ℕ → ℝ) :
    quadraticExcludedPrimeCost q x w p + 2 * evenPrimePowerCost x w p =
      2 * quadraticExcludedPrimeCost 0 x w p := by
  have hc0 : ¬Nat.Coprime p 0 := fun h ↦ hp.ne_one ((Nat.coprime_zero_right p).mp h)
  rw [quadraticExcludedPrimeCost_of_coprime hp hc, quadraticExcludedPrimeCost_of_not_coprime hc0]
  unfold evenPrimePowerCost
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hcut : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ <;> by_cases he : Even k <;>
    simp only [hcut, he, not_true_eq_false, not_false_eq_true, and_true, and_false, ite_true,
      ite_false, mul_zero, zero_add, add_zero]

/-- With nonnegative weights at cutoff powers, the even-power cost is nonnegative.
Sum the nonnegative selected terms; this controls the sign of the cancellation. -/
theorem evenPrimePowerCost_nonneg (p : ℕ) (x : ℝ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ → 0 ≤ w (p ^ k)) :
    0 ≤ evenPrimePowerCost x w p := by
  apply Finset.sum_nonneg
  intro k hk
  split_ifs with h
  · exact hw k hk h.1
  · exact le_rfl

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.LLS.PaperStatements

/-- Even prime-power mass for the untapered endpoint weight, at cutoff x and base p.
This finite sum is subtracted twice on the unramified local branch. -/
noncomputable def untaperedEvenPrimeCost (x : ℝ) (p : ℕ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.evenPrimePowerCost x (untaperedExcludedEndpointWeight x) p

/-- For prime p and x>1 the even-power saving is nonnegative.
Use cutoff positivity term by term; this shows retaining it cannot worsen a bound. -/
theorem untaperedEvenPrimeCost_nonneg {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 < x) :
    0 ≤ untaperedEvenPrimeCost x p := by
  exact
    AnalyticNumberTheory.Arithmetic.evenPrimePowerCost_nonneg p x _
      (fun k hk hcut ↦ untaperedEndpointWeight_nonneg_at_cutoff hp hx (Finset.mem_Icc.mp hk).1 hcut)

open AnalyticNumberTheory.Arithmetic in
/-- At a prime coprime to q and x>1, retain twice the even-power cost when
bounding by the principal envelope. This improves the former factor-two bound. -/
theorem untaperedPrimeCost_add_even_le {p : ℕ} (hp : p.Prime) (q : ℕ) (hc : Nat.Coprime p q) {x : ℝ}
    (hx : 1 < x) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p +
        2 * untaperedEvenPrimeCost x p ≤
      2 * untaperedPrimeEnvelope x p := by
  rw [untaperedEvenPrimeCost, quadraticPrimeCost_add_even hp hc]
  exact
    mul_le_mul_of_nonneg_left (untaperedPrimeCost_zero_le_envelope hp hx)
      (by norm_num only : (0 : ℝ) ≤ 2)

/-- The finite exceptional cost after keeping even-power cancellation.
The two deficits charge a ramified prime at rate alpha and an unramified prime
at rate 2alpha. The outer maximum enforces the nonnegative-excess invariant. -/
noncomputable def evenRetainedPrimeExcess (x : ℝ) (P p : ℕ) : ℝ :=
  max 0
    (max (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
      (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
        2 * explicitUntaperedPrimeRate x P * Real.log p))

/-- The retained excess is nonnegative for all arguments by its outer maximum.
This permits enlarging the finite exception support in global budgets. -/
theorem evenRetainedPrimeExcess_nonneg (x : ℝ) (P p : ℕ) : 0 ≤ evenRetainedPrimeExcess x P p :=
  le_max_left _ _

/-- At a prime and x>1 the retained excess is at most the previous common-rate excess.
Bound each deficit by twice its nonnegative positive part and keep the even mass. -/
theorem evenRetainedPrimeExcess_le {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 < x) (P : ℕ) :
    evenRetainedPrimeExcess x P p ≤ explicitUntaperedPrimeExcess x P p := by
  have hs := untaperedEvenPrimeCost_nonneg hp hx
  have h0 :=
    le_max_left 0 (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
  have ht :=
    le_max_right 0 (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
  dsimp only [evenRetainedPrimeExcess, explicitUntaperedPrimeExcess]
  apply max_le
  · linarith only [h0]
  · apply max_le
    · linarith only [h0, ht]
    · linarith only [hs, ht]

open AnalyticNumberTheory.Arithmetic in
/-- For a ramified odd prime, the retained finite deficit supplies the
one-rate local bound. Outside the exception support reuse the proved prime tail. -/
theorem untaperedPrimeCost_le_even_retained_ramified {x : ℝ} (hx : 1 < x) {P p : ℕ} (hP : 2 ≤ P)
    (hp : p.Prime) (ho : Odd p) (q : ℕ) (hd : p ∣ q) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤
      explicitUntaperedPrimeRate x P * Real.log p +
        if p ∈ explicitUntaperedPrimeExceptions P then evenRetainedPrimeExcess x P p else 0 := by
  by_cases hm : p ∈ explicitUntaperedPrimeExceptions P
  · rw [ite_eq_left hm]
    have hc := untaperedPrimeCost_le_envelope_of_dvd hp q hd hx
    have h1 :=
      le_max_left (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
        (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
          2 * explicitUntaperedPrimeRate x P * Real.log p)
    have h2 :=
      le_max_right 0
        (max (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
          (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
            2 * explicitUntaperedPrimeRate x P * Real.log p))
    dsimp only [evenRetainedPrimeExcess]
    linarith only [hc, h1, h2]
  · have hc := untaperedPrimeCost_le_explicit_ramified hx hP hp ho q hd
    simpa only [ite_eq_right hm] using hc

open AnalyticNumberTheory.Arithmetic in
/-- For an unramified odd prime, the retained even-power mass supplies the
two-rate local bound with the smaller deficit. The large-prime tail is unchanged. -/
theorem untaperedPrimeCost_le_even_retained_unramified {x : ℝ} (hx : 1 < x) {P p : ℕ} (hP : 2 ≤ P)
    (hp : p.Prime) (ho : Odd p) (q : ℕ) (hd : ¬p ∣ q) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤
      2 * explicitUntaperedPrimeRate x P * Real.log p +
        if p ∈ explicitUntaperedPrimeExceptions P then evenRetainedPrimeExcess x P p else 0 := by
  by_cases hm : p ∈ explicitUntaperedPrimeExceptions P
  · rw [ite_eq_left hm]
    have hc := untaperedPrimeCost_add_even_le hp q (hp.coprime_iff_not_dvd.mpr hd) hx
    have h1 :=
      le_max_right (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
        (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
          2 * explicitUntaperedPrimeRate x P * Real.log p)
    have h2 :=
      le_max_right 0
        (max (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
          (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
            2 * explicitUntaperedPrimeRate x P * Real.log p))
    dsimp only [evenRetainedPrimeExcess]
    linarith only [hc, h1, h2]
  · have hc := untaperedPrimeCost_le_explicit_twice hx hP hp ho q
    simpa only [ite_eq_right hm] using hc

/-- Fully specified input budget with even-power cancellation in the finite exceptions.
It depends only on x,P,n and retains the earlier two-adic envelope and tail rate. -/
noncomputable def evenRetainedInputBudget (x : ℝ) (P n : ℕ) : ℝ :=
  2 * untaperedPrimeEnvelope x 2 + explicitUntaperedPrimeRate x P * Real.log n +
    ∑ p ∈ explicitUntaperedPrimeExceptions P, evenRetainedPrimeExcess x P p

/-- For x>1 the retained input budget is no larger than the earlier explicit budget.
Every exceptional prime is prime, so the local excess comparison can be summed. -/
theorem evenRetainedInputBudget_le {x : ℝ} (hx : 1 < x) (P n : ℕ) :
    evenRetainedInputBudget x P n ≤ explicitUntaperedInputBudget x P n := by
  have hs :=
    Finset.sum_le_sum (s := explicitUntaperedPrimeExceptions P)
      (fun p hp ↦ evenRetainedPrimeExcess_le (Finset.mem_filter.mp hp).2.1 hx P)
  dsimp only [evenRetainedInputBudget, explicitUntaperedInputBudget]
  linarith only [hs]

/-- At the common rate the coupled budget with retained excesses is at most
the fully specified input budget. The conductor-log coefficient vanishes;
bound only the remaining prime-two cost by its principal envelope twice. -/
theorem conductorSquareBudget_le_even_retained {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x : ℝ} (hx : 1 < x) (P : ℕ) :
    conductorSquareUntaperedBudget bridge x (explicitUntaperedPrimeRate x P)
        (explicitUntaperedPrimeRate x P) (explicitUntaperedPrimeExceptions P)
        (evenRetainedPrimeExcess x P) ≤
      evenRetainedInputBudget x P n := by
  dsimp only [conductorSquareUntaperedBudget, evenRetainedInputBudget]
  simp only [sub_self, zero_mul, add_zero]
  have h :=
    untaperedPrimeCost_le_twice_envelope Nat.prime_two
      (NumberTheory.complexQuadraticCharacter n hn).conductor hx
  linarith only [h]

open AnalyticNumberTheory.Arithmetic in
/-- Under x>1 and P>=2, the untapered structural budget of any odd nonsquare
is bounded by the retained input budget. Insert the proved ramified and
unramified rates into the square-factor decomposition. No input enumeration occurs. -/
theorem untaperedBudget_le_even_retained {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x : ℝ} (hx : 1 < x) {P : ℕ}
    (hP : 2 ≤ P) :
    quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
        (Finset.Ioc 0 ⌊x⌋₊) (untaperedExcludedEndpointWeight x) ≤
      evenRetainedInputBudget x P n := by
  have ha := explicitUntaperedPrimeRate_nonneg hx hP
  have hcost :=
    untaperedBudget_le_conductor_square_rates bridge (zero_lt_one.trans hx).le ha ha
      (explicitUntaperedPrimeExceptions P) (evenRetainedPrimeExcess x P)
      (fun p _ ↦ evenRetainedPrimeExcess_nonneg x P p)
      (fun p hp hd ↦
        untaperedPrimeCost_le_even_retained_ramified hx hP (Nat.prime_of_mem_primeFactors hp)
          (hn.of_dvd_nat ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp).2) _ hd)
      (fun p hp hd ↦
        untaperedPrimeCost_le_even_retained_unramified hx hP (Nat.prime_of_mem_primeFactors hp)
          (hn.of_dvd_nat ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp).2) _ hd)
  exact hcost.trans (conductorSquareBudget_le_even_retained bridge hx P)

/-- For positive n<=B and admissible x,P, the retained budget is monotone in n.
Only the nonnegative coefficient of log n depends on the input size. -/
theorem evenRetainedInputBudget_mono {n B P : ℕ} (hn : 0 < n) (hnB : n ≤ B) {x : ℝ} (hx : 1 < x)
    (hP : 2 ≤ P) : evenRetainedInputBudget x P n ≤ evenRetainedInputBudget x P B := by
  have hm :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (Nat.cast_pos.mpr hn) (Nat.cast_le.mpr hnB))
      (explicitUntaperedPrimeRate_nonneg hx hP)
  dsimp only [evenRetainedInputBudget]
  linarith only [hm]

end PseudoPrime.LLS.PaperStatements
