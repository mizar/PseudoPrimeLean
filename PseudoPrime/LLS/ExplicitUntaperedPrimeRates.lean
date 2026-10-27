/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.UntaperedPrimeCostBounds

/-! # Explicit local rates and finite excesses without cost hypotheses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At prime threshold P, the common half-rate for the principal envelope:
A(x)/(P-1)+(log x)^2/(2sqrt x log P). Later theorems assume x>1 and P>=2.
This replaces abstract ramified and unramified rate assumptions. -/
noncomputable def explicitUntaperedPrimeRate (x : ℝ) (P : ℕ) : ℝ :=
  excludedReciprocalCoefficient x / (P - 1) + ((Real.log x) ^ 2 / (2 * Real.sqrt x)) / Real.log P

/-- The finite exception support is exactly the odd primes below the natural
threshold P. This is a symbolic finset; no input modulus certificates are generated. -/
def explicitUntaperedPrimeExceptions (P : ℕ) : Finset ℕ :=
  (Finset.range P).filter (fun p ↦ p.Prime ∧ Odd p)

/-- Twice the positive excess of the elementary principal prime envelope
over its rate charge. This single nonnegative function covers the principal
and twice-principal branches on the finite exception support. -/
noncomputable def explicitUntaperedPrimeExcess (x : ℝ) (P p : ℕ) : ℝ :=
  2 * max 0 (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)

/-- At x>1 and P>=2, the explicit prime rate is nonnegative. Both denominators
are positive and the reciprocal coefficient and logarithm square are nonnegative.
This discharges the sign premise of the square-factor cost consumer. -/
theorem explicitUntaperedPrimeRate_nonneg {x : ℝ} (hx : 1 < x) {P : ℕ} (hP : 2 ≤ P) :
    0 ≤ explicitUntaperedPrimeRate x P := by
  have hPr : (1 : ℝ) < P := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 2) (Nat.cast_le.mpr hP)
  dsimp only [explicitUntaperedPrimeRate]
  exact
    add_nonneg (div_nonneg (excludedReciprocalCoefficient_pos hx).le (sub_pos.mpr hPr).le)
      (div_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)))
        (Real.log_nonneg hPr.le))

/-- At primes p>=P>=2 and x>1, the principal envelope is at most the explicit
rate times log p. Compare reciprocal denominators and multiply log p>=log P
before cancelling the positive log P. This is a uniform analytic prime tail. -/
theorem untaperedPrimeEnvelope_le_rate {x : ℝ} (hx : 1 < x) {P p : ℕ} (hP : 2 ≤ P) (hp : p.Prime)
    (hPp : P ≤ p) : untaperedPrimeEnvelope x p ≤ explicitUntaperedPrimeRate x P * Real.log p := by
  have hPr : (1 : ℝ) < P := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 2) (Nat.cast_le.mpr hP)
  have hPpr : (P : ℝ) ≤ p := Nat.cast_le.mpr hPp
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos hPr
  have hlog := Real.log_le_log (zero_lt_one.trans hPr) hPpr
  have hgeom := one_div_le_one_div_of_le (sub_pos.mpr hPr) (sub_le_sub_right hPpr 1)
  have hm :=
    mul_le_mul_of_nonneg_left hgeom
      (mul_nonneg (excludedReciprocalCoefficient_pos hx).le
        (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_le)))
  have hr :
    excludedReciprocalCoefficient x * (Real.log p / (p - 1)) ≤
      (excludedReciprocalCoefficient x / (P - 1)) * Real.log p := by
    calc
      _ = excludedReciprocalCoefficient x * Real.log p * (1 / (p - 1)) := by ring
      _ ≤ excludedReciprocalCoefficient x * Real.log p * (1 / (P - 1)) := hm
      _ = _ := by ring
  have hg : 0 ≤ ((Real.log x) ^ 2 / (2 * Real.sqrt x)) / Real.log P :=
    div_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)))
      hlogP.le
  have hl := mul_le_mul_of_nonneg_left hlog hg
  rw [div_mul_cancel₀ _ hlogP.ne'] at hl
  dsimp only [untaperedPrimeEnvelope, explicitUntaperedPrimeRate]
  nlinarith only [hr, hl]

/-- The explicit finite excess is nonnegative for every cutoff, threshold and
index. Positivity of a maximum proves the sign without a local cost certificate. -/
theorem explicitUntaperedPrimeExcess_nonneg (x : ℝ) (P p : ℕ) :
    0 ≤ explicitUntaperedPrimeExcess x P p := by
  exact mul_nonneg (by norm_num only) (le_max_left _ _)

open AnalyticNumberTheory.Arithmetic in
/-- At a conductor-dividing odd prime, the explicit rate and finite excess bound
the actual untapered local cost. Use the analytic tail outside the exception
support and the excess envelope inside it. No unproved local-rate premise remains. -/
theorem untaperedPrimeCost_le_explicit_ramified {x : ℝ} (hx : 1 < x) {P p : ℕ} (hP : 2 ≤ P)
    (hp : p.Prime) (hodd : Odd p) (q : ℕ) (hpq : p ∣ q) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤
      explicitUntaperedPrimeRate x P * Real.log p +
        if p ∈ explicitUntaperedPrimeExceptions P then explicitUntaperedPrimeExcess x P p
        else 0 := by
  have hcost := untaperedPrimeCost_le_envelope_of_dvd hp q hpq hx
  by_cases hmem : p ∈ explicitUntaperedPrimeExceptions P
  · rw [ite_eq_left hmem]
    have hm :=
      le_max_right (0 : ℝ)
        (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
    have h0 :=
      le_max_left (0 : ℝ) (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
    dsimp only [explicitUntaperedPrimeExcess]
    linarith only [hcost, hm, h0]
  · rw [ite_eq_right hmem, add_zero]
    have hPp : P ≤ p := by
      by_contra h
      exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_of_not_ge h), ⟨hp, hodd⟩⟩)
    exact hcost.trans (untaperedPrimeEnvelope_le_rate hx hP hp hPp)

open AnalyticNumberTheory.Arithmetic in
/-- At any odd prime and conductor, twice the explicit rate and the finite excess
bound the untapered local cost. This supplies the unramified branch uniformly,
using its twice-principal envelope and the same finite exception support. -/
theorem untaperedPrimeCost_le_explicit_twice {x : ℝ} (hx : 1 < x) {P p : ℕ} (hP : 2 ≤ P)
    (hp : p.Prime) (hodd : Odd p) (q : ℕ) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤
      2 * explicitUntaperedPrimeRate x P * Real.log p +
        if p ∈ explicitUntaperedPrimeExceptions P then explicitUntaperedPrimeExcess x P p
        else 0 := by
  have hcost := untaperedPrimeCost_le_twice_envelope hp q hx
  by_cases hmem : p ∈ explicitUntaperedPrimeExceptions P
  · rw [ite_eq_left hmem]
    have hm :=
      le_max_right (0 : ℝ)
        (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
    dsimp only [explicitUntaperedPrimeExcess]
    linarith only [hcost, hm]
  · rw [ite_eq_right hmem, add_zero]
    have hPp : P ≤ p := by
      by_contra h
      exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_of_not_ge h), ⟨hp, hodd⟩⟩)
    have hm :=
      mul_le_mul_of_nonneg_left (untaperedPrimeEnvelope_le_rate hx hP hp hPp)
        (by norm_num only : (0 : ℝ) ≤ 2)
    linarith only [hcost, hm]

/-- A completely specified untapered input budget: twice the envelope at two,
the explicit rate times log n, and finite excesses at primes below P. It is
independent of conductor and unproved local costs; later theorems supply x>1,
P>=2 and the odd nonsquare input. -/
noncomputable def explicitUntaperedInputBudget (x : ℝ) (P n : ℕ) : ℝ :=
  2 * untaperedPrimeEnvelope x 2 + explicitUntaperedPrimeRate x P * Real.log n +
    ∑ p ∈ explicitUntaperedPrimeExceptions P, explicitUntaperedPrimeExcess x P p

open AnalyticNumberTheory.Arithmetic in
/-- At the explicit common rate, the coupled budget is at most the fully
specified input budget. The log d term vanishes and the actual cost at two
is bounded by twice its principal envelope. This transfers a scalar separation
without exposing any local-cost hypotheses. -/
theorem conductorSquareBudget_le_explicit_input {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x : ℝ} (hx : 1 < x) (P : ℕ) :
    conductorSquareUntaperedBudget bridge x (explicitUntaperedPrimeRate x P)
        (explicitUntaperedPrimeRate x P) (explicitUntaperedPrimeExceptions P)
        (explicitUntaperedPrimeExcess x P) ≤
      explicitUntaperedInputBudget x P n := by
  dsimp only [conductorSquareUntaperedBudget, explicitUntaperedInputBudget]
  simp only [sub_self, zero_mul, add_zero]
  have h :=
    untaperedPrimeCost_le_twice_envelope Nat.prime_two
      (NumberTheory.complexQuadraticCharacter n hn).conductor hx
  linarith only [h]

open AnalyticNumberTheory.Arithmetic in
/-- For any odd nonsquare bridge, x>1 and P>=2, the untapered structural
exclusion budget is at most the fully specified input budget. Apply the proved
local rates to both conductor branches, then use the explicit two-adic bound.
This removes the former unproved local-rate and global-cost premises. -/
theorem untaperedBudget_le_explicit_input {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x : ℝ} (hx : 1 < x) {P : ℕ}
    (hP : 2 ≤ P) :
    quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
        (Finset.Ioc 0 ⌊x⌋₊) (untaperedExcludedEndpointWeight x) ≤
      explicitUntaperedInputBudget x P n := by
  have ha := explicitUntaperedPrimeRate_nonneg hx hP
  have hcost :=
    untaperedBudget_le_conductor_square_rates bridge (zero_lt_one.trans hx).le ha ha
      (explicitUntaperedPrimeExceptions P) (explicitUntaperedPrimeExcess x P)
      (fun p _ ↦ explicitUntaperedPrimeExcess_nonneg x P p)
      (fun p hp hdiv ↦
        untaperedPrimeCost_le_explicit_ramified hx hP (Nat.prime_of_mem_primeFactors hp)
          (hn.of_dvd_nat ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp).2) _ hdiv)
      (fun p hp _ ↦
        untaperedPrimeCost_le_explicit_twice hx hP (Nat.prime_of_mem_primeFactors hp)
          (hn.of_dvd_nat ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp).2) _)
  exact hcost.trans (conductorSquareBudget_le_explicit_input bridge hx P)

/-- For positive n<=B, x>1 and P>=2, the explicit input budget is monotone
in the input size. Only its nonnegative rate times log n depends on n.
This supplies a common bound including all small inputs in the finite maximum. -/
theorem explicitUntaperedInputBudget_mono {n B P : ℕ} (hn : 0 < n) (hnB : n ≤ B) {x : ℝ}
    (hx : 1 < x) (hP : 2 ≤ P) :
    explicitUntaperedInputBudget x P n ≤ explicitUntaperedInputBudget x P B := by
  have hm :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (Nat.cast_pos.mpr hn) (Nat.cast_le.mpr hnB))
      (explicitUntaperedPrimeRate_nonneg hx hP)
  dsimp only [explicitUntaperedInputBudget]
  linarith only [hm]

end PseudoPrime.LLS.PaperStatements
