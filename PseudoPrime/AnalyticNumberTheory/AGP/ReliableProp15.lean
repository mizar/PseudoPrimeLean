/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionCounting

/-! # ReliableProp15

Definitions and finite conversions for reliable Proposition 1.5.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Purpose: record the coefficient in the real lower bound of reliable,
Proposition 1.5.

Definition: `c₀ / (φ(m) * log x)`, where `φ(m)` is `Nat.totient m`.

Inputs: the positive constant `c₀`, a progression modulus `m`, and a prime
bound `x`.

Output: the real coefficient multiplying the number of divisors in the
Proposition 1.5 count.

Role: this keeps the source estimate explicit when it is passed to the finite
prime-set conversion theorem below.
-/
noncomputable def reliableProp15Coefficient (c₀ : ℝ) (m x : ℕ) : ℝ :=
  c₀ / ((Nat.totient m : ℝ) * Real.log x)

/--
Purpose: give the natural cutoff corresponding to the real bound `x^(2/5)`.

Definition: the floor of the real power `x^(2/5)`.

Role: this makes `restrictedDivisors L (reliableProp15DivisorCutoff x)` count
exactly the divisors in the range used by reliable, Proposition 1.5.
-/
noncomputable def reliableProp15DivisorCutoff (x : ℕ) : ℕ :=
  Nat.floor (Real.rpow (x : ℝ) ((2 : ℝ) / 5))

/--
Inputs: a positive natural number `N`.

Claim: the square-root divisor cutoff is covered by the Proposition 1.5 cutoff
for `N ^ 2`.

Content: `Nat.sqrt N ≤ N ^ (1/2) ≤ (N ^ 2) ^ (2/5)`, with floors handled by
`Nat.le_floor`.

Role: this gives a natural-valued prime bound close to the first-construction
scale in reliable, §2.
-/
theorem natSqrt_le_reliableProp15DivisorCutoff_square (N : ℕ) (hN : 1 ≤ N) :
    Nat.sqrt N ≤ reliableProp15DivisorCutoff (N ^ 2) := by
  change Nat.sqrt N ≤ Nat.floor (Real.rpow ((N ^ 2 : ℕ) : ℝ) ((2 : ℝ) / 5))
  apply Nat.le_floor
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hsqrtPos : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr hNpos
  apply
    (Real.le_rpow_iff_log_le (Nat.cast_pos.mpr hsqrtPos)
        (by exact_mod_cast Nat.pow_pos hNpos : 0 < ((N ^ 2 : ℕ) : ℝ))).2
  have hsqrtSq : (Nat.sqrt N) ^ 2 ≤ N := Nat.sqrt_le' N
  have hsqrtPosR : (0 : ℝ) < (Nat.sqrt N : ℝ) := by exact_mod_cast hsqrtPos
  have hlogSq :=
    Real.log_le_log (sq_pos_of_pos hsqrtPosR)
      (by exact_mod_cast hsqrtSq : (Nat.sqrt N : ℝ) ^ 2 ≤ (N : ℝ))
  rw [Real.log_pow] at hlogSq
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hhalf : Real.log (Nat.sqrt N : ℝ) ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := by
    calc
      Real.log (Nat.sqrt N : ℝ) = (1 / 2 : ℝ) * (2 * Real.log (Nat.sqrt N : ℝ)) := by ring
      _ ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := mul_le_mul_of_nonneg_left hlogSq (by norm_num only)
  have hscale := mul_le_mul_of_nonneg_right (by norm_num only : (1 / 2 : ℝ) ≤ 4 / 5) hlogN
  rw [Nat.cast_pow, Real.log_pow]
  calc
    Real.log (Nat.sqrt N : ℝ) ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := hhalf
    _ ≤ (4 / 5 : ℝ) * Real.log (N : ℝ) := hscale
    _ = (2 / 5 : ℝ) * (2 * Real.log (N : ℝ)) := by ring

/--
Inputs: a squarefree initial modulus `N`, a bound `x` whose divisor cutoff
contains `Nat.sqrt N`, and a strict lower bound using half the full divisor
count.

Claim: the same strict lower bound holds with the actual restricted-divisor
count used by reliable, Proposition 1.5.

Content: complementary divisors give at least half of the squarefree divisor
count below `Nat.sqrt N`; inclusion then transfers that count to the supplied
cutoff.

Role: this is the source-faithful finite counting bridge for the initial
modulus-one prime supply.
-/
theorem initial_uniform_count_lower_bound_of_sqrt_divisors {N x T : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hN : N ≠ 0) (hSquarefree : Squarefree N) (hcut : Nat.sqrt N ≤ reliableProp15DivisorCutoff x)
    (hx : 2 ≤ x)
    (hlower :
      (T : ℝ) < reliableProp15Coefficient c₀ 1 x * (((2 ^ N.primeFactors.card : ℕ) : ℝ) / 2)) :
    (T : ℝ) <
      reliableProp15Coefficient c₀ 1 x *
        ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ) := by
  have hhalfNat := two_pow_primeFactors_card_le_twice_restrictedDivisors_sqrt hN hSquarefree
  have hhalfR :
    (((2 ^ N.primeFactors.card : ℕ) : ℝ) / 2) ≤ ((restrictedDivisors N (Nat.sqrt N)).card : ℝ) := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      ((2 ^ N.primeFactors.card : ℕ) : ℝ) ≤
          (2 : ℝ) * ((restrictedDivisors N (Nat.sqrt N)).card : ℝ) :=
        by exact_mod_cast hhalfNat
      _ = ((restrictedDivisors N (Nat.sqrt N)).card : ℝ) * 2 := by ring
  have hsubset :
    restrictedDivisors N (Nat.sqrt N) ⊆ restrictedDivisors N (reliableProp15DivisorCutoff x) := by
    intro d hd
    have hd' := (mem_restrictedDivisors hN).1 hd
    exact (mem_restrictedDivisors hN).2 ⟨hd'.1, le_trans hd'.2 hcut⟩
  have hcount :
    ((restrictedDivisors N (Nat.sqrt N)).card : ℝ) ≤
      ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hxreal : (1 : ℝ) < (x : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num only : 1 < 2) hx
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have hcoef : 0 < reliableProp15Coefficient c₀ 1 x := by
    simp only [reliableProp15Coefficient, Nat.totient_one, Nat.cast_one, one_mul]
    exact div_pos hc₀ hlog
  have hdivLower :
    (((2 ^ N.primeFactors.card : ℕ) : ℝ) / 2) ≤
      ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ) :=
    le_trans hhalfR hcount
  have hscaled := mul_le_mul_of_nonneg_left hdivLower (le_of_lt hcoef)
  exact lt_of_lt_of_le hlower hscaled

/--
Inputs: a natural prime bound `x` with `1 ≤ x`.

Claim: the natural divisor cutoff for `x^(2/5)` is at most `x`.

Proof: the floor is bounded by the real power, and for `x ≥ 1` the power
`x^(2/5)` is at most `x`.

Role: this converts an initial-modulus cutoff condition into the simpler
bound needed for Carmichael estimates.
-/
theorem reliableProp15DivisorCutoff_le_self {x : ℕ} (hx : 1 ≤ x) :
    reliableProp15DivisorCutoff x ≤ x := by
  change Nat.floor (Real.rpow (x : ℝ) ((2 : ℝ) / 5)) ≤ x
  have hxreal : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hpow : Real.rpow (x : ℝ) ((2 : ℝ) / 5) ≤ (x : ℝ) :=
    Real.rpow_le_self_of_one_le hxreal (by norm_num only : (2 : ℝ) / 5 ≤ 1)
  have hfloor :
    ((Nat.floor (Real.rpow (x : ℝ) ((2 : ℝ) / 5)) : ℕ) : ℝ) ≤ Real.rpow (x : ℝ) ((2 : ℝ) / 5) :=
    Nat.floor_le (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le x) _)
  exact_mod_cast le_trans hfloor hpow

/--
Inputs: a natural scale `X` and the fifth-power cutoff used by reliable,
Proposition 1.5.

Claim: every divisor below the cutoff for `X^5` is at most `X^2`.

Proof: evaluate the real power `(X^5)^(2/5)` as `X^2`, then use the floor
bound.

Role: turns membership in the fifth-power restricted-divisor set into the
range hypothesis required by the fixed-scale theta estimate.
-/
theorem reliableProp15DivisorCutoff_fifth_power_le_square (X : ℕ) :
    reliableProp15DivisorCutoff (X ^ 5) ≤ X ^ 2 := by
  change Nat.floor (Real.rpow ((X ^ 5 : ℕ) : ℝ) ((2 : ℝ) / 5)) ≤ X ^ 2
  have hXnonneg : 0 ≤ (X : ℝ) := by exact_mod_cast Nat.zero_le X
  have hXfiveRpow : (X : ℝ) ^ 5 = (X : ℝ) ^ (5 : ℝ) := (Real.rpow_natCast _ _).symm
  have hmul := Real.rpow_mul hXnonneg 5 ((2 : ℝ) / 5)
  have hexp : (5 : ℝ) * ((2 : ℝ) / 5) = 2 := by ring
  rw [hexp] at hmul
  have hXtwoRpow : (X : ℝ) ^ 2 = (X : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast _ _).symm
  have hpow : ((X : ℝ) ^ 5) ^ ((2 : ℝ) / 5) = (X : ℝ) ^ 2 := by
    rw [hXfiveRpow, hXtwoRpow]
    exact hmul.symm
  simp only [Nat.cast_pow]
  calc
    Nat.floor (Real.rpow ((X : ℝ) ^ 5) ((2 : ℝ) / 5)) ≤ Nat.floor ((X : ℝ) ^ 2) :=
      Nat.floor_mono hpow.le
    _ = X ^ 2 := by exact_mod_cast (Nat.floor_natCast (X ^ 2 : ℕ))

/--
Inputs: a positive natural scale `X`.

Claim: `X ^ 2` is no larger than the divisor cutoff for `X ^ 5`.

Proof: apply the logarithmic characterization of real powers; the logarithms on both sides are
equal after expanding the natural powers.

Role: together with `reliableProp15DivisorCutoff_fifth_power_le_square`, identifies the exact
cutoff needed when the full divisor set of an auxiliary modulus is used.
-/
theorem square_le_reliableProp15DivisorCutoff_fifth_power (X : ℕ) (hX : 0 < X) :
    X ^ 2 ≤ reliableProp15DivisorCutoff (X ^ 5) := by
  change X ^ 2 ≤ Nat.floor (Real.rpow ((X ^ 5 : ℕ) : ℝ) ((2 : ℝ) / 5))
  apply Nat.le_floor
  apply
    (Real.le_rpow_iff_log_le (Nat.cast_pos.mpr (Nat.pow_pos hX))
        (Nat.cast_pos.mpr (Nat.pow_pos hX))).2
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Real.log_pow]
  nlinarith only

/--
Inputs: a positive natural scale `X`.

Claim: the reliable Proposition 1.5 divisor cutoff at `X ^ 5` equals `X ^ 2`.

Proof: combine the floor upper bound with the logarithmic lower bound for the same real power.

Role: removes the cutoff from restricted divisor counts whenever the auxiliary modulus is at
most `X ^ 2`.
-/
theorem reliableProp15DivisorCutoff_fifth_power_eq_square (X : ℕ) (hX : 0 < X) :
    reliableProp15DivisorCutoff (X ^ 5) = X ^ 2 := by
  apply Nat.le_antisymm
  · exact reliableProp15DivisorCutoff_fifth_power_le_square X
  · exact square_le_reliableProp15DivisorCutoff_fifth_power X hX

/--
Inputs: a positive scale `X` and a nonzero squarefree modulus `L ≤ X ^ 2`.

Claim: the restricted divisor count at the Proposition 1.5 cutoff for `X ^ 5` is the full divisor
count `2 ^ L.primeFactors.card`.

Proof: identify the cutoff with `X ^ 2`, then apply the squarefree divisor-count formula.

Role: supplies the full divisor mass for the separate large-scale AGP construction.
-/
theorem restrictedDivisors_card_eq_full_at_fifth_power {L X : ℕ} (hX : 0 < X) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hLbound : L ≤ X ^ 2) :
    (restrictedDivisors L (reliableProp15DivisorCutoff (X ^ 5))).card =
      2 ^ L.primeFactors.card := by
  have hcut := reliableProp15DivisorCutoff_fifth_power_eq_square X hX
  have hLy : L ≤ reliableProp15DivisorCutoff (X ^ 5) := by
    rw [hcut]
    exact hLbound
  exact card_restrictedDivisors_eq_two_pow_primeFactors_card hL hSquarefree hLy

/--
Inputs: positive natural numbers `q`, `L`, and an exponent `J`.

Claim: for the scale `X = (4 * q * L) ^ J`, we have `q ≤ X`, `L ≤ X ^ 2`, and
`(4 * d) ^ J ≤ X` for every divisor `d` of `L`.

Proof: the base `4 * q * L` dominates `q`, `L`, and every `4 * d`; raising the base to a
positive power preserves these bounds.

Role: supplies the elementary range conditions for the large-scale theta and full-divisor
construction.
-/
theorem fullDivisorScale_arithmetic_bounds (q L J : ℕ) (hq : 0 < q) (hL : 0 < L) (hJ : 0 < J) :
    q ≤ (4 * q * L) ^ J ∧
      L ≤ ((4 * q * L) ^ J) ^ 2 ∧ ∀ d, d ∣ L → (4 * d) ^ J ≤ (4 * q * L) ^ J := by
  have hq1 : 1 ≤ q := Nat.succ_le_iff.mpr hq
  have hL1 : 1 ≤ L := Nat.succ_le_iff.mpr hL
  have hq4 : q ≤ 4 * q := by
    calc
      q = 1 * q := by simp only [one_mul]
      _ ≤ 4 * q := Nat.mul_le_mul_right q (by decide : 1 ≤ 4)
  have hqL : L ≤ q * L := by
    calc
      L = 1 * L := by simp only [one_mul]
      _ ≤ q * L := Nat.mul_le_mul_right L hq1
  have hqBase : q ≤ 4 * q * L := by
    calc
      q ≤ 4 * q := hq4
      _ = (4 * q) * 1 := by simp only [mul_one]
      _ ≤ (4 * q) * L := Nat.mul_le_mul_left (4 * q) hL1
  have hLBase : L ≤ 4 * q * L := by
    calc
      L ≤ q * L := hqL
      _ ≤ (4 * q) * L := Nat.mul_le_mul_right L hq4
  have hbasePos : 0 < 4 * q * L := lt_of_lt_of_le hq hqBase
  have hpow : 4 * q * L ≤ (4 * q * L) ^ J := Nat.le_self_pow (Nat.ne_of_gt hJ) (4 * q * L)
  have hXpos : 0 < (4 * q * L) ^ J := Nat.pow_pos hbasePos
  refine ⟨hqBase.trans hpow, ?_, ?_⟩
  · exact le_trans hLBase (le_trans hpow (Nat.le_self_pow (by omega) ((4 * q * L) ^ J)))
  · intro d hd
    have hdL : d ≤ L := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_of_gt hL)) hd
    have h4d : 4 * d ≤ 4 * q * L := by
      calc
        4 * d ≤ 4 * L := Nat.mul_le_mul_left 4 hdL
        _ ≤ 4 * (q * L) := Nat.mul_le_mul_left 4 hqL
        _ = 4 * q * L := by rw [Nat.mul_assoc]
    exact Nat.pow_le_pow_left h4d J

/--
Inputs: positive `q`, `L`, and `J`, with `L` squarefree.

Claim: at `X = (4 * q * L) ^ J`, the restricted divisors of `L` below the Proposition 1.5 cutoff
for `X ^ 5` have cardinality `2 ^ L.primeFactors.card`.

Proof: `fullDivisorScale_arithmetic_bounds` gives `L ≤ X ^ 2`; the fifth-power cutoff identity
then makes the restriction include every divisor of `L`.

Role: packages the scale choice with the full divisor count needed by the P2 density argument.
-/
theorem fullDivisorScale_restrictedDivisor_card (q L J : ℕ) (hq : 0 < q) (hL : 0 < L) (hJ : 0 < J)
    (hSquarefree : Squarefree L) :
    (restrictedDivisors L (reliableProp15DivisorCutoff (((4 * q * L) ^ J) ^ 5))).card =
      2 ^ L.primeFactors.card := by
  have hscale := fullDivisorScale_arithmetic_bounds q L J hq hL hJ
  have hX : 0 < (4 * q * L) ^ J := Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hq) hL)
  exact restrictedDivisors_card_eq_full_at_fifth_power hX (Nat.ne_of_gt hL) hSquarefree hscale.2.1

/--
Inputs: a positive natural number `n`.

Claim: `n` lies below the divisor cutoff associated with `n ^ 5`.

Content: the cutoff is the floor of the real power with exponent `2 / 5`, and
the logarithmic characterization reduces the claim to `log n ≤ 2 * log n`.

Proof: apply `Nat.le_floor`, then use `Real.le_rpow_iff_log_le` and the
nonnegativity of `log n`.

Role: choosing the prime-supply parameter as a fifth power automatically puts
the entire initial modulus below the divisor cutoff.
-/
theorem le_reliableProp15DivisorCutoff_fifth_power (n : ℕ) (hn : 0 < n) :
    n ≤ reliableProp15DivisorCutoff (n ^ 5) := by
  change n ≤ Nat.floor (Real.rpow ((n ^ 5 : ℕ) : ℝ) ((2 : ℝ) / 5))
  apply Nat.le_floor
  apply
    (Real.le_rpow_iff_log_le (Nat.cast_pos.mpr hn)
        (by exact_mod_cast Nat.pow_pos hn : 0 < ((n ^ 5 : ℕ) : ℝ))).2
  rw [Nat.cast_pow, Real.log_pow]
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  nlinarith only [hlog]

/--
Inputs: a squarefree integer `L`, a progression modulus `m`, divisor cutoff
`y`, parameter bound `k`, and prime bound `x`.

Claim: these are the arithmetic hypotheses in reliable, Proposition 1.5:
coprimality to the modulus, the bound on the number of prime factors, the
reciprocal-prime sum bound, the exact natural cutoff for `d ≤ x^(2/5)`, and
the power bound for `k`.

Role: this records the source conditions that must accompany the fixed-`k`
prime-count estimate used by the AGP supply construction.
-/
def ReliableProp15Admissible (L m y k x : ℕ) : Prop :=
  Squarefree L ∧
    Nat.Coprime L m ∧
    L.primeFactors.card ^ 4 ≤ x ∧
    (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
    y = reliableProp15DivisorCutoff x ∧ k ^ 5 ≤ x ^ 3

/--
Inputs: a squarefree modulus candidate `L` and a prime bound `x`.

Claim: `L` satisfies the non-parameter hypotheses of reliable, Proposition
1.5 for modulus `4`: coprimality to `4`, the prime-factor count bound, and the
reciprocal-prime sum bound.

Role: these are the hypotheses under which the fixed progression count below
must supply a positive `k` coprime to `L`.
-/
def ReliableProp15ModFourInput (L x : ℕ) : Prop :=
  Squarefree L ∧
    Nat.Coprime L 4 ∧ L.primeFactors.card ^ 4 ≤ x ∧ (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ)

/--
Inputs: a modulus-four input at a prime bound `x` and a larger bound `y`.

Claim: the same squarefree modulus satisfies the modulus-four input at `y`.

Content: only the prime-factor-count inequality depends on the bound, and it
is preserved when that bound increases.

Proof: retain the squarefreeness, coprimality, and reciprocal-sum fields, and
compose the factor-count inequality with `x ≤ y`.

Role: this carries seed-modulus data to a later fifth-power scale.
-/
theorem reliableProp15ModFourInput_mono {L x y : ℕ} (h : ReliableProp15ModFourInput L x)
    (hxy : x ≤ y) : ReliableProp15ModFourInput L y :=
  ⟨h.1, h.2.1, le_trans h.2.2.1 hxy, h.2.2.2⟩

/--
Inputs: modulus-four arithmetic data at a bound `x`, a later bound `z`, a
cutoff matching `z`, and a parameter bound `k^5 ≤ z^3`.

Claim: these fields establish `ReliableProp15Admissible L 4 y k z`.

Proof: lift the prime-factor-count bound along `x ≤ z`; the remaining
arithmetic fields are unchanged.

Role: this transfers the seed's modulus conditions to each parameter used by
the later finite averaging argument.
-/
theorem reliableProp15Admissible_of_modFourInput {L x y k z : ℕ}
    (hinput : ReliableProp15ModFourInput L x) (hxz : x ≤ z)
    (hcut : y = reliableProp15DivisorCutoff z) (hk : k ^ 5 ≤ z ^ 3) :
    ReliableProp15Admissible L 4 y k z :=
  ⟨hinput.1, hinput.2.1, le_trans hinput.2.2.1 hxz, hinput.2.2.2, hcut, hk⟩

/--
Inputs: a parameter `k` bounded by `X^3`.

Claim: `k^5 ≤ (X^5)^3`, the power condition in Proposition 1.5 at the
fifth-power scale.

Proof: raise `k ≤ X^3` to the fifth power and identify both resulting powers
of `X` using commutativity of natural multiplication.

Role: this derives the last arithmetic field of `ReliableProp15Admissible`
from membership in the finite averaging parameter set.
-/
theorem reliableProp15ParamPowerBound_of_le_cube {k X : ℕ} (hk : k ≤ X ^ 3) : k ^ 5 ≤ (X ^ 5) ^ 3 :=
  calc
    k ^ 5 ≤ (X ^ 3) ^ 5 := Nat.pow_le_pow_left hk 5
    _ = X ^ (3 * 5) := (Nat.pow_mul X 3 5).symm
    _ = X ^ (5 * 3) := congrArg (fun n : ℕ => X ^ n) (Nat.mul_comm 3 5)
    _ = (X ^ 5) ^ 3 := Nat.pow_mul X 5 3

/--
Inputs: a fixed positive coefficient `c₀`, progression modulus `m`, residue
`l`, threshold `x₀`, and a squarefree `L` coprime to `m`.

Claim: for every `x ≥ x₀`, some positive `k ≤ x^(3/5)` gives more primes
`d*k+1 ≤ x` in residue class `l mod m` than the Proposition 1.5 lower bound
for divisors `d ∣ L` with `d ≤ x^(2/5)`.

Role: this unrestricted count is used first with modulus `1` to construct the
auxiliary integer and again at modulus `4` for the final prime supply.
-/
def ReliableProp15UniformCount (c₀ : ℝ) (m l x₀ : ℕ) : Prop :=
  2 ≤ x₀ ∧
    0 < m ∧
    Nat.Coprime l m ∧
    ∀ L x,
      x₀ ≤ x →
        Squarefree L →
        Nat.Coprime L m →
        ∃ k,
          0 < k ∧
            k ^ 5 ≤ x ^ 3 ∧
            reliableProp15Coefficient c₀ m x *
                ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ) <
              ((((restrictedDivisors L (reliableProp15DivisorCutoff x)).filter
                      (fun d =>
                        Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)).card :
                  ℕ) :
                ℝ)

/--
Inputs: ordered positive-count coefficients `c₁ ≤ c₂` and a uniform
Proposition 1.5 count at coefficient `c₂`.

Claim: the same uniform count holds at coefficient `c₁`.

Proof: for every admissible `x`, the denominator `φ(m) * log x` is positive,
so the source lower bound decreases with the coefficient; the witnessing prime
set and averaging parameter can therefore be retained.

Role: this permits the common Proposition 1.5 coefficient to be reduced when
constructing the seed modulus and its later auxiliary data.
-/
theorem reliableProp15UniformCount_mono {c₁ c₂ : ℝ} {m l x₀ : ℕ} (hc : c₁ ≤ c₂)
    (h : ReliableProp15UniformCount c₂ m l x₀) : ReliableProp15UniformCount c₁ m l x₀ := by
  rcases h with ⟨hx₀, hm, hlm, hcount⟩
  refine ⟨hx₀, hm, hlm, ?_⟩
  intro L x hx hsq hcop
  obtain ⟨k, hk, hkpow, hbound⟩ := hcount L x hx hsq hcop
  refine ⟨k, hk, hkpow, ?_⟩
  have hxreal : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) (le_trans hx₀ hx))
  have hden : 0 < (Nat.totient m : ℝ) * Real.log (x : ℝ) := by
    apply mul_pos
    · exact_mod_cast (Nat.totient_pos.mpr hm)
    · exact Real.log_pos hxreal
  have hcoeff : reliableProp15Coefficient c₁ m x ≤ reliableProp15Coefficient c₂ m x := by
    unfold reliableProp15Coefficient
    exact div_le_div_of_nonneg_right hc hden.le
  calc
    reliableProp15Coefficient c₁ m x *
          ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ) ≤
        reliableProp15Coefficient c₂ m x *
          ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff
        (Nat.cast_nonneg (restrictedDivisors L (reliableProp15DivisorCutoff x)).card)
    _ <
        ((((restrictedDivisors L (reliableProp15DivisorCutoff x)).filter
                (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)).card :
            ℕ) :
          ℝ) :=
      hbound

/--
Purpose: state the strengthened `m=4`, `l=3` instance of reliable,
Proposition 1.5, using the natural cutoff corresponding to `x^(2/5)`.

Inputs: fixed positive count constant `c₀` and large-enough threshold `x₀`.

Claim: for every admissible squarefree `L` and `x ≥ x₀`, there is a positive
`k ≤ x^(3/5)`, coprime to `L`, for which the number of prime values `d*k+1`
in residue class `3 mod 4` exceeds the Proposition 1.5 divisor-count lower
bound. This proposition also includes the unrestricted modulus-4 count.

Role: this is an explicit proposition to prove from the source analysis; it is
not an axiom and is not yet proved in this module.
-/
def ReliableProp15UniformCoprimeCount (c₀ : ℝ) (x₀ : ℕ) : Prop :=
  ReliableProp15UniformCount c₀ 4 3 x₀ ∧
    ∀ L x,
      x₀ ≤ x →
        ReliableProp15ModFourInput L x →
        ∃ k,
          0 < k ∧
            k ^ 5 ≤ x ^ 3 ∧
            Nat.Coprime k L ∧
            reliableProp15Coefficient c₀ 4 x *
                ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ) <
              ((((restrictedDivisors L (reliableProp15DivisorCutoff x)).filter
                      (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % 4 = 3)).card :
                  ℕ) :
                ℝ)

/--
Inputs: ordered coefficients `c₁ ≤ c₂` and a modulus-four coprime count at
coefficient `c₂`.

Claim: the unrestricted and coprime counts both hold at coefficient `c₁`.

Proof: apply `reliableProp15UniformCount_mono` to the unrestricted field. For
the coprime field, retain its witness and reduce the coefficient in the same
way using positivity of `φ(4) * log x`.

Role: this carries a supplied Proposition 1.5 constant to the smaller common
constant needed by the seed and final progression-count constructions.
-/
theorem reliableProp15UniformCoprimeCount_mono {c₁ c₂ : ℝ} {x₀ : ℕ} (hc : c₁ ≤ c₂)
    (h : ReliableProp15UniformCoprimeCount c₂ x₀) : ReliableProp15UniformCoprimeCount c₁ x₀ := by
  refine ⟨reliableProp15UniformCount_mono hc h.1, ?_⟩
  intro L x hx hinput
  obtain ⟨k, hk, hkpow, hkcop, hbound⟩ := h.2 L x hx hinput
  refine ⟨k, hk, hkpow, hkcop, ?_⟩
  have hxreal : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) (le_trans h.1.1 hx))
  have hphi : Nat.totient 4 = 2 := by decide
  have hden : 0 < (Nat.totient 4 : ℝ) * Real.log (x : ℝ) := by
    rw [hphi]
    exact mul_pos (by norm_num only) (Real.log_pos hxreal)
  have hcoeff : reliableProp15Coefficient c₁ 4 x ≤ reliableProp15Coefficient c₂ 4 x := by
    unfold reliableProp15Coefficient
    exact div_le_div_of_nonneg_right hc hden.le
  calc
    reliableProp15Coefficient c₁ 4 x *
          ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ) ≤
        reliableProp15Coefficient c₂ 4 x *
          ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff
        (Nat.cast_nonneg (restrictedDivisors L (reliableProp15DivisorCutoff x)).card)
    _ <
        ((((restrictedDivisors L (reliableProp15DivisorCutoff x)).filter
                (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % 4 = 3)).card :
            ℕ) :
          ℝ) :=
      hbound

/--
Inputs: the data of a fixed-parameter restricted-divisor count, the constant
`c₀` from reliable, Proposition 1.5, and its real-valued divisor-count bound.

Claim: if the source coefficient times the number of small divisors exceeds
`T` and is bounded by the good-divisor count, then there is a set of more than
`T` distinct primes in the requested progression.

Content: this specializes the generic real-count bridge to the exact
`c₀/(φ(m) log x)` coefficient in Proposition 1.5.

Proof: unfold the coefficient and apply
`exists_prime_set_of_real_restricted_divisor_lower_bound`.

Role: this is the finite output interface for the analytic estimate in
Proposition 1.5.
-/
theorem exists_prime_set_of_reliable_prop15_count_bound (L y k x m a T : ℕ) (hL : L ≠ 0)
    (hk : 0 < k) (c₀ : ℝ)
    (hlower : (T : ℝ) < reliableProp15Coefficient c₀ m x * ((restrictedDivisors L y).card : ℝ))
    (hcount :
      reliableProp15Coefficient c₀ m x * ((restrictedDivisors L y).card : ℝ) ≤
        ((((restrictedDivisors L y).filter
                (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :
            ℕ) :
          ℝ)) :
    ∃ P : Finset ℕ,
      T < P.card ∧
        ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d, d ∣ L ∧ d ≤ y ∧ p = d * k + 1 := by
  exact
    exists_prime_set_of_real_restricted_divisor_lower_bound L y k x m a T hL hk
      (reliableProp15Coefficient c₀ m x) hlower hcount

/--
Inputs: the uniform form of reliable, Proposition 1.5 for modulus `m` and
residue `l`, an admissible squarefree modulus `L`, and a divisor-count
threshold `T` below the source lower bound.

Claim: the Proposition 1.5 count supplies both its parameter `k` and a finite
set of more than `T` distinct primes `d*k+1` in the requested progression.

Proof: obtain `k` and the strict prime-count estimate from the uniform
Proposition 1.5 input, then apply the finite-count conversion above.

Role: this is the reusable output interface for both applications in reliable,
§2: the initial modulus-1 seed set and the final modulus-4 prime set.
-/
theorem exists_prime_set_of_reliable_prop15_uniform_count (c₀ : ℝ) (m l x₀ L x T : ℕ)
    (hcount : ReliableProp15UniformCount c₀ m l x₀) (hx : x₀ ≤ x) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hCoprime : Nat.Coprime L m)
    (hlower :
      (T : ℝ) <
        reliableProp15Coefficient c₀ m x *
          ((restrictedDivisors L (reliableProp15DivisorCutoff x)).card : ℝ)) :
    ∃ k,
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        ∃ P : Finset ℕ,
          T < P.card ∧
            ∀ p ∈ P,
              Nat.Prime p ∧
                p ≤ x ∧
                p % m = l % m ∧ ∃ d, d ∣ L ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1 := by
  obtain ⟨k, hk, hkpow, hprimeCount⟩ := hcount.2.2.2 L x hx hSquarefree hCoprime
  refine ⟨k, hk, hkpow, ?_⟩
  exact
    exists_prime_set_of_reliable_prop15_count_bound L (reliableProp15DivisorCutoff x) k x m l T hL
      hk c₀ hlower (le_of_lt hprimeCount)

end PseudoPrime.AnalyticNumberTheory.AGP
