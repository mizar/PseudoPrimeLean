/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.SeedConstruction

/-! # ProgressionAuxiliaryData

P2 auxiliary data and finite divisor-count conversions.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a base-set size `w`, a prime bound `x`, a seed size `T + 1`, and an
auxiliary modulus satisfying the size bounds from the seed construction.

Claim: the P2 threshold term involving `2^w * floor(λ(L) log L)` is bounded
above by the explicit expression `2^w * x^2 * (T + 1) * log x`.

Proof: bound `log L` using `L ≤ x^(T+1)`, bound `λ(L)` by `x^2`, and use
monotonicity of multiplication and the natural floor.

Role: this is the upper side of the quantitative comparison needed to choose
the fixed-factor seed parameters.
-/
theorem p2_floor_term_upper_bound_of_auxiliary_size_bounds {w x T L : ℕ} (hx : 2 ≤ x) (hL : 1 < L)
    (hLbound : L ≤ x ^ (T + 1)) (hLambdaBound : ArithmeticFunction.carmichael L ≤ x ^ 2) :
    (2 ^ w : ℝ) * (Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) : ℝ) ≤
      (2 ^ w : ℝ) * (x : ℝ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log (x : ℝ) := by
  have hxreal : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hx)
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLboundR : (L : ℝ) ≤ (x : ℝ) ^ (T + 1) := by exact_mod_cast hLbound
  have hlogL : Real.log (L : ℝ) ≤ ((T + 1 : ℕ) : ℝ) * Real.log (x : ℝ) := by
    calc
      Real.log (L : ℝ) ≤ Real.log ((x : ℝ) ^ (T + 1)) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < L)) hLboundR
      _ = ((T + 1 : ℕ) : ℝ) * Real.log (x : ℝ) := by rw [Real.log_pow]
  have hlogLnonneg : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (le_of_lt hLreal)
  have hlambdaR : (ArithmeticFunction.carmichael L : ℝ) ≤ (x : ℝ) ^ 2 := by
    exact_mod_cast hLambdaBound
  have hmul :
    (ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ) ≤
      (x : ℝ) ^ 2 * (((T + 1 : ℕ) : ℝ) * Real.log (x : ℝ)) := by
    calc
      (ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ) ≤ (x : ℝ) ^ 2 * Real.log (L : ℝ) :=
        mul_le_mul_of_nonneg_right hlambdaR hlogLnonneg
      _ ≤ (x : ℝ) ^ 2 * (((T + 1 : ℕ) : ℝ) * Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogL (sq_nonneg (x : ℝ))
  have hfloor :
    (Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) : ℝ) ≤
      (x : ℝ) ^ 2 * (((T + 1 : ℕ) : ℝ) * Real.log (x : ℝ)) := by
    exact
      le_trans
        (Nat.floor_le
          (mul_nonneg (by exact_mod_cast Nat.zero_le (ArithmeticFunction.carmichael L))
            hlogLnonneg))
        hmul
  have hpowNonneg : (0 : ℝ) ≤ (2 ^ w : ℝ) := by exact_mod_cast Nat.zero_le (2 ^ w)
  calc
    (2 ^ w : ℝ) * (Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) : ℝ) ≤
        (2 ^ w : ℝ) * ((x : ℝ) ^ 2 * (((T + 1 : ℕ) : ℝ) * Real.log (x : ℝ))) :=
      mul_le_mul_of_nonneg_left hfloor hpowNonneg
    _ = (2 ^ w : ℝ) * (x : ℝ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log (x : ℝ) := by ring

/--
Purpose: store the auxiliary integer parameters needed to turn the output of
reliable Proposition 1.5 into the prime supply required by P2.

Inputs: a finite positive base set `W`, lower bound `C`, and the fixed
Proposition 1.5 constants `c₀`, `x₀`.

Fields: `L` controls the divisor count and Carmichael exponent, `q` exceeds the
base and prime-factor cutoffs, and `x` is large enough. The real lower bound
already includes both the P2 threshold and the loss of at most `q` small prime
values.

Role: unlike `AGPProgressionCountData`, this structure contains no selected
`k` or Proposition 1.5 count; those are supplied by
`ReliableProp15UniformCoprimeCount`.
-/
structure AGPProgressionAuxiliaryData (W : Finset ℕ) (C : ℕ) (c₀ : ℝ) (x₀ : ℕ) where
  L : ℕ
  q : ℕ
  x : ℕ
  hL : 2 < L
  hLargeEnough : x₀ ≤ x
  hProp15Input : ReliableProp15ModFourInput L x
  /-- The stronger reciprocal-prime bound used for the coarse sieve loss. -/
  hReciprocal1024 : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ)
  hCq : max C (W.sup id) ≤ q
  hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q
  hlambda : 3 ≤ ArithmeticFunction.carmichael L
  hlower :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log L) + q : ℕ) : ℝ) <
      reliableProp15Coefficient c₀ 4 x *
        ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ)

/--
Inputs: a positive Proposition 1.5 coefficient, a modulus-four input L, a
cutoff q, and a fixed-factor divisor lower bound whose coefficient exceeds
the P2 threshold.

Claim: these data form an AGP progression auxiliary-data object.

Proof: the fixed-factor bound gives a lower bound for the restricted divisor
count; positivity of the coefficient transfers the strict threshold bound to
that full count.

Role: this packages the finite divisor estimate into the P2 interface used by
the second Proposition 1.5 application.
-/
noncomputable def progressionAuxiliaryData_of_primeFactorCountLowerBound {W : Finset ℕ}
    {C x₀ L q x s : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hx : 2 ≤ x) (hL : 2 < L) (hLargeEnough : x₀ ≤ x)
    (hProp15Input : ReliableProp15ModFourInput L x)
    (hReciprocal1024 : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ))
    (hCq : max C (W.sup id) ≤ q) (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L) (hcut : q ^ s ≤ reliableProp15DivisorCutoff x)
    (hlower :
      ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + q : ℕ) :
          ℝ) <
        reliableProp15Coefficient c₀ 4 x *
          ((((L.primeFactors.card + 1 - s : ℕ) : ℝ) ^ s) / (s.factorial : ℝ))) :
    AGPProgressionAuxiliaryData W C c₀ x₀ := by
  have hLne : L ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two hL)
  have hdivLower :=
    primeFactorProducts_lower_bound_restrictedDivisors hLne hProp15Input.1 hfactor hcut
  have hxreal : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hx)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have hprimeTwo : Nat.Prime 2 := Nat.prime_two
  have hexp : 0 < (2 : ℕ) := by norm_num only
  have htotient : Nat.totient 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num only, Nat.totient_prime_pow hprimeTwo hexp]
    norm_num only
  have hcoef : 0 < reliableProp15Coefficient c₀ 4 x := by
    unfold reliableProp15Coefficient
    rw [htotient]
    exact div_pos hc₀ (mul_pos (by norm_num only : 0 < (2 : ℝ)) hlog)
  have hscaled := mul_le_mul_of_nonneg_left hdivLower (le_of_lt hcoef)
  have hlower' :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + q : ℕ) :
        ℝ) <
      reliableProp15Coefficient c₀ 4 x *
        ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ) :=
    lt_of_lt_of_le hlower hscaled
  exact
    { L := L
      q := q
      x := x
      hL := hL
      hLargeEnough := hLargeEnough
      hProp15Input := hProp15Input
      hReciprocal1024 := hReciprocal1024
      hCq := hCq
      hfactor := hfactor
      hlambda := hlambda
      hlower := hlower' }

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a positive coefficient, the P2 arithmetic conditions, a fixed-factor
size `s`, and a lower bound in terms of `L.primeFactors.card / (2 * s)`.

Claim: the data define an `AGPProgressionAuxiliaryData` object.

Proof: use `s! ≤ s ^ s` and the lower bound for the falling binomial product
to convert the ratio estimate to the existing factorial-form hypothesis.

Role: this connects the elementary size estimate from reliable, §2 directly
to the finite P2 interface.
-/
noncomputable def progressionAuxiliaryData_of_binomial_ratio_lower_bound {W : Finset ℕ}
    {C x₀ L q x s : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hx : 2 ≤ x) (hL : 2 < L) (hLargeEnough : x₀ ≤ x)
    (hProp15Input : ReliableProp15ModFourInput L x)
    (hReciprocal1024 : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ))
    (hCq : max C (W.sup id) ≤ q) (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L) (hcut : q ^ s ≤ reliableProp15DivisorCutoff x)
    (hs : 0 < s) (hsmall : 2 * s ≤ L.primeFactors.card)
    (hlower :
      ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + q : ℕ) :
          ℝ) <
        reliableProp15Coefficient c₀ 4 x * ((L.primeFactors.card : ℝ) / (2 * (s : ℝ))) ^ s) :
    AGPProgressionAuxiliaryData W C c₀ x₀ := by
  have hbinomial := fixedPrimeFactorProductsOf_binomial_ratio_lower_bound L.primeFactors s hs hsmall
  have hxreal : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hx)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have hprimeTwo : Nat.Prime 2 := Nat.prime_two
  have hexp : 0 < (2 : ℕ) := by norm_num only
  have htotient : Nat.totient 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num only, Nat.totient_prime_pow hprimeTwo hexp]
    norm_num only
  have hcoef : 0 < reliableProp15Coefficient c₀ 4 x := by
    unfold reliableProp15Coefficient
    rw [htotient]
    exact div_pos hc₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) hlog)
  have hscaled := mul_le_mul_of_nonneg_left hbinomial (le_of_lt hcoef)
  have hlower' := lt_of_lt_of_le hlower hscaled
  exact
    progressionAuxiliaryData_of_primeFactorCountLowerBound hc₀ hx hL hLargeEnough hProp15Input
      hReciprocal1024 hCq hfactor hlambda hcut hlower'

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: the P2 arithmetic conditions, a first-stage lower bound
`(T + 1) / 2 ≤ L.primeFactors.card`, and a second-stage size `s` satisfying
`4 * s ≤ T + 1`.

Claim: a lower bound in terms of `(T / (4 * s)) ^ s` supplies the
`AGPProgressionAuxiliaryData` object.

Proof: transfer the seed parameter bound to the actual prime-factor count,
then apply the binomial-ratio P2 constructor.

Role: this connects the first-stage seed output to the second-stage P2 input
using a single explicit size parameter.
-/
noncomputable def progressionAuxiliaryData_of_seed_factor_count_lower_bound {W : Finset ℕ}
    {C x₀ L q x s T : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hx : 2 ≤ x) (hL : 2 < L) (hLargeEnough : x₀ ≤ x)
    (hProp15Input : ReliableProp15ModFourInput L x)
    (hReciprocal1024 : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ))
    (hCq : max C (W.sup id) ≤ q) (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L) (hcut : q ^ s ≤ reliableProp15DivisorCutoff x)
    (hFactorCount : (T + 1) / 2 ≤ L.primeFactors.card) (hs : 0 < s) (hscale : 4 * s ≤ T + 1)
    (hlower :
      ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + q : ℕ) :
          ℝ) <
        reliableProp15Coefficient c₀ 4 x * ((T : ℝ) / (4 * (s : ℝ))) ^ s) :
    AGPProgressionAuxiliaryData W C c₀ x₀ := by
  have hsmall : 2 * s ≤ L.primeFactors.card := by
    clear * - hFactorCount hscale
    omega
  have hratio := fixedFactorRatio_le_of_seedFactorCount L.primeFactors T s hFactorCount hs hscale
  have hxreal : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hx)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have hprimeTwo : Nat.Prime 2 := Nat.prime_two
  have hexp : 0 < (2 : ℕ) := by norm_num only
  have htotient : Nat.totient 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num only, Nat.totient_prime_pow hprimeTwo hexp]
    norm_num only
  have hcoef : 0 < reliableProp15Coefficient c₀ 4 x := by
    unfold reliableProp15Coefficient
    rw [htotient]
    exact div_pos hc₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) hlog)
  have hscaled := mul_le_mul_of_nonneg_left hratio (le_of_lt hcoef)
  have hlower' := lt_of_lt_of_le hlower hscaled
  exact
    progressionAuxiliaryData_of_binomial_ratio_lower_bound hc₀ hx hL hLargeEnough hProp15Input
      hReciprocal1024 hCq hfactor hlambda hcut hs hsmall hlower'

end PseudoPrime.AnalyticNumberTheory.AGP
