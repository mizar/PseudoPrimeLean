/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.SelbergSieve
public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionCounting

import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Totient

/-! # Selberg sieve reduction for progression prime counts

This module connects progression prime counts to the sifted sum of a
`BoundingSieve`, gives exact CRT formulas for the concrete progression sieve,
and bounds its remainder terms. Quantitative optimization of the Λ² weights
needed for a Brun–Titchmarsh bound remains separate.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a natural number `n`.

Claim: the sum of the real-valued Möbius function over the divisors of `n` is
one for `n = 1` and zero otherwise.

Proof: evaluate the convolution identity `ζ * μ = 1` at `n`, then use the
divisor-sum formula for convolution by `ζ`.

Role: supplies the finite cancellation identity used in Möbius inversion for
the Selberg quadratic main term.
-/
theorem moebius_sum_divisors_eq_ite_one (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d) =
      if n = 1 then 1 else 0 := by
  have h :=
    congrArg (fun f : ArithmeticFunction ℝ => f n)
      (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ))
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h
  simpa only [ArithmeticFunction.one_apply] using h

/--
Inputs: a positive modulus `Q` and a natural number `n`.

Claim: the Möbius sum over divisors of `Q` that also divide `n` is the
indicator of `Nat.Coprime n Q`.

Proof: identify the filtered divisor set with the divisors of `gcd n Q`, then
apply the Möbius divisor-sum cancellation identity.

Role: converts coprimality conditions in finite progression counts into a
finite divisor sum that can be exchanged with the summation over `n`.
-/
theorem moebius_sum_modulus_divisors_eq_coprime_indicator {n Q : ℕ} (hQ : 0 < Q) :
    (∑ d ∈ Q.divisors, if d ∣ n then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0) =
      if Nat.Coprime n Q then 1 else 0 := by
  classical
  let g := Nat.gcd n Q
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n hQ
  have hset : Q.divisors.filter (fun d => d ∣ n) = g.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdQ, hQ0⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdQ, Nat.ne_of_gt hgpos⟩
    · rintro ⟨hdg, hg0⟩
      refine ⟨⟨Nat.dvd_trans hdg (Nat.gcd_dvd_right n Q), hQ.ne'⟩, ?_⟩
      exact Nat.dvd_trans hdg (Nat.gcd_dvd_left n Q)
  calc
    _ =
        ∑ d ∈ Q.divisors.filter (fun d => d ∣ n),
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d :=
      by rw [← Finset.sum_filter]
    _ = ∑ d ∈ g.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d := by rw [hset]
    _ = if g = 1 then 1 else 0 := moebius_sum_divisors_eq_ite_one g
    _ = if Nat.Coprime n Q then 1 else 0 := by simp only [g, Nat.coprime_iff_gcd_eq_one]

/--
Inputs: a natural number `Q`.

Claim: the divisor sum of the absolute Möbius function equals the number of
squarefree divisors of `Q`.

Proof: use the exact formula `|μ(d)| = 1` for squarefree `d` and `0` otherwise,
then convert the resulting indicator sum to a filtered cardinality.

Role: identifies the precise support of the floor-function error in the
coprime counting estimate.
-/
theorem moebius_abs_divisor_sum_eq_squarefree_divisor_card (Q : ℕ) :
    (∑ d ∈ Q.divisors, |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d|) =
      ((Q.divisors.filter (fun d => Squarefree d)).card : ℝ) := by
  classical
    calc
    _ = ∑ d ∈ Q.divisors, if Squarefree d then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      change |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = _
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
      simp only [Int.cast_ite, Int.cast_one, Int.cast_zero]
    _ = ∑ d ∈ Q.divisors.filter (fun d => Squarefree d), 1 := by rw [Finset.sum_filter]
    _ = _ := by simp

/--
Inputs: a positive natural number `Q`.

Claim: `Q` has exactly `2 ^ ω(Q)` squarefree divisors, where `ω(Q)` is the
number of distinct prime factors.

Proof: identify squarefree divisors with products of subsets of the distinct
normalized prime factors, then count the powerset.

Role: expresses the coprime-counting error using only the number of distinct
prime factors of the modulus.
-/
theorem squarefree_divisor_count_eq_two_pow_cardDistinctFactors (Q : ℕ) (hQ : 0 < Q) :
    (Q.divisors.filter (fun d => Squarefree d)).card =
      2 ^ ArithmeticFunction.cardDistinctFactors Q := by
  rw [Finset.card_def, Nat.divisors_filter_squarefree hQ.ne', Multiset.card_map]
  rw [← Finset.card_def, Finset.card_powerset]
  congr 1
  rw [Nat.factors_eq]
  rw [ArithmeticFunction.cardDistinctFactors_apply, Multiset.card_toFinset]
  simp

/--
Inputs: a positive modulus `Q` and an inclusive counting bound `T`.

Claim: the number of integers `n ≤ T` coprime to `Q` equals a finite sum of
Möbius divisor indicators over `n` and the divisors of `Q`.

Proof: write the coprimality count as the sum of its indicator function and
apply `moebius_sum_modulus_divisors_eq_coprime_indicator` termwise.

Role: this is the finite inclusion-exclusion identity used to separate the
main density from the floor-function errors in the Brun–Titchmarsh estimate.
-/
theorem coprime_card_range_eq_moebius_double_sum (T Q : ℕ) (hQ : 0 < Q) :
    ((Finset.range (T + 1)).filter (fun n => Nat.Coprime n Q)).card =
      ∑ n ∈ Finset.range (T + 1),
        ∑ d ∈ Q.divisors,
          if d ∣ n then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0 := by
  classical
    calc
    _ = ∑ n ∈ Finset.range (T + 1), if Nat.Coprime n Q then (1 : ℝ) else 0 := by
      rw [← Finset.sum_boole]
    _ =
        ∑ n ∈ Finset.range (T + 1),
          ∑ d ∈ Q.divisors,
            if d ∣ n then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0 :=
      by
      apply Finset.sum_congr rfl
      intro n hn
      exact (moebius_sum_modulus_divisors_eq_coprime_indicator hQ).symm

/--
Inputs: a positive modulus `Q` and an inclusive counting bound `T`.

Claim: the coprime count is the divisor-first Möbius sum, with each inner sum
restricted to multiples of its divisor.

Proof: apply the finite double-sum identity and exchange the order of summation.

Role: exposes the individual floor-counting terms needed for an explicit
coprime-density estimate.
-/
theorem coprime_card_range_eq_moebius_multiple_sum (T Q : ℕ) (hQ : 0 < Q) :
    ((Finset.range (T + 1)).filter (fun n => Nat.Coprime n Q)).card =
      ∑ d ∈ Q.divisors,
        ∑ n ∈ Finset.range (T + 1),
          if d ∣ n then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0 := by
  calc
    _ =
        ∑ n ∈ Finset.range (T + 1),
          ∑ d ∈ Q.divisors,
            if d ∣ n then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0 :=
      coprime_card_range_eq_moebius_double_sum T Q hQ
    _ =
        ∑ d ∈ Q.divisors,
          ∑ n ∈ Finset.range (T + 1),
            if d ∣ n then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0 :=
      Finset.sum_comm

/--
Inputs: natural numbers `T` and `d`.

Claim: exactly `T / d` positive multiples of `d`, together with zero, lie in
the range `0, ..., T`.

Proof: split the filtered range into zero and nonzero multiples, then apply
`Nat.card_multiples'` to the nonzero part.

Role: evaluates each multiple-counting fiber in the finite Möbius expansion.
-/
theorem card_filter_dvd_range_add_one (T d : ℕ) :
    ((Finset.range (T + 1)).filter (fun n => d ∣ n)).card = T / d + 1 := by
  classical
  let B := (Finset.range (T + 1)).filter (fun n => n ≠ 0 ∧ d ∣ n)
  have hset : (Finset.range (T + 1)).filter (fun n => d ∣ n) = insert 0 B := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, B]
    constructor
    · rintro ⟨hn, hdn⟩
      by_cases hn0 : n = 0
      · exact Or.inl hn0
      · exact Or.inr ⟨hn, hn0, hdn⟩
    · rintro (hn0 | ⟨hn, hn0, hdn⟩)
      · subst n
        exact ⟨Nat.zero_lt_succ T, Nat.dvd_zero d⟩
      · exact ⟨hn, hdn⟩
  have hzeroB : 0 ∉ B := by
    intro hmem
    simp only [B, Finset.mem_filter] at hmem
    exact hmem.2.1 rfl
  have hB : B.card = T / d := Nat.card_multiples' T d
  rw [hset, Finset.card_insert_of_notMem hzeroB, hB]

/--
Inputs: natural numbers `T` and `d`.

Claim: the Möbius-weighted count of multiples of `d` up to `T` equals
`μ(d) * (T / d + 1)`.

Proof: rewrite the indicator sum as a constant sum over the multiples and use
`card_filter_dvd_range_add_one`.

Role: turns the divisor-first coprime expansion into explicit floor terms.
-/
theorem moebius_sum_multiples_range_eq_floor (T d : ℕ) :
    (∑ n ∈ Finset.range (T + 1),
        if d ∣ n then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0) =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T / d + 1 : ℕ) : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, card_filter_dvd_range_add_one, Nat.cast_add, Nat.cast_one]
  exact mul_comm _ _

/--
Inputs: a positive modulus `Q` and an inclusive counting bound `T`.

Claim: the coprime count through `T` is exactly the finite Möbius sum of
`T / d + 1` over divisors `d` of `Q`.

Proof: reorder the indicator expansion by divisor and evaluate each inner
multiple count using `moebius_sum_multiples_range_eq_floor`.

Role: isolates the floor-function error that must be bounded to obtain the
uniform coprime density estimate for the Selberg weight mass.
-/
theorem coprime_card_range_eq_moebius_floor_sum (T Q : ℕ) (hQ : 0 < Q) :
    ((Finset.range (T + 1)).filter (fun n => Nat.Coprime n Q)).card =
      ∑ d ∈ Q.divisors,
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T / d + 1 : ℕ) : ℝ) := by
  rw [coprime_card_range_eq_moebius_multiple_sum T Q hQ]
  apply Finset.sum_congr rfl
  intro d hd
  exact moebius_sum_multiples_range_eq_floor T d

/--
Inputs: a positive modulus `Q`.

Claim: the finite Möbius sum `∑_{d ∣ Q} μ(d) / d` equals `φ(Q) / Q`.

Proof: evaluate the exact floor-sum formula for the coprime count at `T = Q`.
The count is one complete reduced residue system, while `Q / d` is exact for
each divisor; the remaining unweighted Möbius sum vanishes unless `Q = 1`.

Role: identifies the main density in the Möbius expansion used to estimate
coprime counting errors.
-/
theorem moebius_divisor_reciprocal_sum_eq_totient_ratio (Q : ℕ) (hQ : 0 < Q) :
    (∑ d ∈ Q.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) =
      (Nat.totient Q : ℝ) / (Q : ℝ) := by
  classical
  by_cases hQ1 : Q = 1
  · subst Q
    have hmu : (ArithmeticFunction.moebius : ArithmeticFunction ℝ) 1 = 1 := by
      simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.moebius_apply_one,
        Int.cast_one]
    simp only [Nat.divisors_one, Finset.sum_singleton, hmu, Nat.cast_one, one_div, Nat.totient_one]
  · have hQgt : 1 < Q := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hQ.ne', hQ1⟩
    have hcard :
      ((Finset.range (Q + 1)).filter (fun n => Nat.Coprime n Q)).card = Nat.totient Q := by
      have hnot : ¬Nat.Coprime Q Q := by
        rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self]
        exact ne_of_gt hQgt
      rw [Finset.range_add_one, Finset.filter_insert]
      simp only [ite_eq_right hnot]
      simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using
        (Nat.totient_eq_card_coprime Q).symm
    have hcount := coprime_card_range_eq_moebius_floor_sum Q Q hQ
    have hcardR :
      ((Finset.range (Q + 1)).filter (fun n => Nat.Coprime n Q)).card = (Nat.totient Q : ℝ) := by
      exact_mod_cast hcard
    rw [hcardR] at hcount
    have hterm (d : ℕ) (hd : d ∈ Q.divisors) :
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((Q / d + 1 : ℕ) : ℝ) =
        (Q : ℝ) * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) +
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d := by
      have hdQ : d ∣ Q := (Nat.mem_divisors.mp hd).1
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_zero_of_dvd_ne_zero hQ.ne' hdQ)
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_div hdQ hd0]
      ring
    have hdecomp :
      (∑ d ∈ Q.divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((Q / d + 1 : ℕ) : ℝ)) =
        (Q : ℝ) *
            (∑ d ∈ Q.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) +
          ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d := by
      calc
        _ =
            ∑ d ∈ Q.divisors,
              ((Q : ℝ) * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) +
                (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d) :=
          by
          apply Finset.sum_congr rfl
          intro d hd
          exact hterm d hd
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hmu : (∑ d ∈ Q.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d) = 0 := by
      rw [moebius_sum_divisors_eq_ite_one, ite_eq_right hQ1]
    rw [hdecomp, hmu, add_zero] at hcount
    have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    calc
      _ =
          ((Q : ℝ) *
              (∑ d ∈ Q.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ))) /
            (Q : ℝ) :=
        by rw [mul_div_cancel_left₀ _ hQR]
      _ = (Nat.totient Q : ℝ) / (Q : ℝ) := by rw [← hcount]

/--
Inputs: a positive modulus `Q` and an inclusive counting bound `T`.

Claim: the number of integers at most `T` that are coprime to `Q` is at most
`T * φ(Q) / Q` plus the sum of `|μ(d)|` over divisors `d` of `Q`.

Proof: expand the count into Möbius floor terms. Each quotient `T / d` differs
from the real quotient by less than one, so its contribution is at most
`|μ(d)|`; sum these errors over the divisors and identify the main coefficient
with `φ(Q) / Q`.

Role: supplies the uniform coprime-count estimate needed to bound the
modulus-restricted Selberg weight mass.
-/
theorem coprime_card_range_le_density_add_moebius_abs_sum (T Q : ℕ) (hQ : 0 < Q) :
    (((Finset.range (T + 1)).filter (fun n => Nat.Coprime n Q)).card : ℝ) ≤
      (T : ℝ) * ((Nat.totient Q : ℝ) / (Q : ℝ)) +
        ∑ d ∈ Q.divisors, |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| := by
  classical
  rw [coprime_card_range_eq_moebius_floor_sum T Q hQ]
  have hterm (d : ℕ) (hd : d ∈ Q.divisors) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T / d + 1 : ℕ) : ℝ) ≤
      (T : ℝ) * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) +
        |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| := by
    have hdQ : d ∣ Q := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdQ hQ
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
    have hrem : T % d < d := Nat.mod_lt T hdpos
    have hdecomp : ((T % d : ℕ) : ℝ) + (d : ℝ) * ((T / d : ℕ) : ℝ) = (T : ℝ) := by
      exact_mod_cast Nat.mod_add_div T d
    have hremR : ((T % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hrem
    have hfloorUpper : (T : ℝ) / (d : ℝ) < ((T / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdR]
      nlinarith only [hdecomp, hremR]
    have hfloorLower : ((T / d : ℕ) : ℝ) ≤ (T : ℝ) / (d : ℝ) := Nat.cast_div_le
    let ε : ℝ := ((T / d : ℕ) : ℝ) + 1 - (T : ℝ) / (d : ℝ)
    have hε0 : 0 ≤ ε := by
      dsimp only [ε]
      nlinarith only [hfloorUpper]
    have hε1 : ε ≤ 1 := by
      dsimp only [ε]
      nlinarith only [hfloorLower]
    have hμerr :
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ε ≤
        |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| := by
      calc
        _ ≤ |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| * ε :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hε0
        _ ≤ |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| * 1 :=
          mul_le_mul_of_nonneg_left hε1 (abs_nonneg _)
        _ = |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| := by rw [mul_one]
    have hsplit : ((T / d + 1 : ℕ) : ℝ) = (T : ℝ) / (d : ℝ) + ε := by
      dsimp only [ε]
      rw [Nat.cast_add, Nat.cast_one]
      ring
    calc
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T / d + 1 : ℕ) : ℝ) =
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T : ℝ) / (d : ℝ) + ε) :=
        by rw [hsplit]
      _ =
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T : ℝ) / (d : ℝ)) +
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ε :=
        by ring
      _ ≤
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T : ℝ) / (d : ℝ)) +
            |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| :=
        by
        simpa only [one_mul, add_comm] using
          add_le_add_right hμerr
            ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T : ℝ) / (d : ℝ)))
      _ =
          (T : ℝ) * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) +
            |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| :=
        by
        congr 1
        field_simp [ne_of_gt hdR]
      _ ≤
          (T : ℝ) * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) +
            |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| :=
        le_rfl
  calc
    (∑ d ∈ Q.divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d * ((T / d + 1 : ℕ) : ℝ)) ≤
        ∑ d ∈ Q.divisors,
          ((T : ℝ) * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) +
            |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d|) :=
      by
      apply Finset.sum_le_sum
      intro d hd
      exact hterm d hd
    _ =
        (T : ℝ) *
            (∑ d ∈ Q.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d / (d : ℝ)) +
          ∑ d ∈ Q.divisors, |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| :=
      by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ =
        (T : ℝ) * ((Nat.totient Q : ℝ) / (Q : ℝ)) +
          ∑ d ∈ Q.divisors, |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| :=
      by rw [moebius_divisor_reciprocal_sum_eq_totient_ratio Q hQ]

/--
Inputs: a positive modulus `Q` and an inclusive counting bound `T`.

Claim: the number of integers at most `T` that are coprime to `Q` is at most
`T * φ(Q) / Q` plus the number of squarefree divisors of `Q`.

Proof: rewrite the exact Möbius support mass in the preceding density estimate
as a squarefree divisor count.

Role: states the coprime density estimate with an error term that omits
non-squarefree divisors.
-/
theorem coprime_card_range_le_density_add_squarefree_divisor_count (T Q : ℕ) (hQ : 0 < Q) :
    (((Finset.range (T + 1)).filter (fun n => Nat.Coprime n Q)).card : ℝ) ≤
      (T : ℝ) * ((Nat.totient Q : ℝ) / (Q : ℝ)) +
        ((Q.divisors.filter (fun d => Squarefree d)).card : ℝ) := by
  calc
    (((Finset.range (T + 1)).filter (fun n => Nat.Coprime n Q)).card : ℝ) ≤
        (T : ℝ) * ((Nat.totient Q : ℝ) / (Q : ℝ)) +
          ∑ d ∈ Q.divisors, |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) d| :=
      coprime_card_range_le_density_add_moebius_abs_sum T Q hQ
    _ =
        (T : ℝ) * ((Nat.totient Q : ℝ) / (Q : ℝ)) +
          ((Q.divisors.filter (fun d => Squarefree d)).card : ℝ) :=
      by rw [moebius_abs_divisor_sum_eq_squarefree_divisor_card]

/--
Inputs: a positive modulus `Q` and an inclusive counting bound `T`.

Claim: the number of integers at most `T` coprime to `Q` is at most the
density main term plus `2 ^ ω(Q)`.

Proof: use the squarefree-divisor error estimate and count those divisors by
choosing a subset of the distinct prime factors of `Q`.

Role: provides an explicit divisor-error form for later AGP parameter bounds.
-/
theorem coprime_card_range_le_density_add_two_pow_cardDistinctFactors (T Q : ℕ) (hQ : 0 < Q) :
    (((Finset.range (T + 1)).filter (fun n => Nat.Coprime n Q)).card : ℝ) ≤
      (T : ℝ) * ((Nat.totient Q : ℝ) / (Q : ℝ)) +
        (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors Q := by
  calc
    (((Finset.range (T + 1)).filter (fun n => Nat.Coprime n Q)).card : ℝ) ≤
        (T : ℝ) * ((Nat.totient Q : ℝ) / (Q : ℝ)) +
          ((Q.divisors.filter (fun d => Squarefree d)).card : ℝ) :=
      coprime_card_range_le_density_add_squarefree_divisor_count T Q hQ
    _ =
        (T : ℝ) * ((Nat.totient Q : ℝ) / (Q : ℝ)) +
          (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors Q :=
      by
      have hcount :=
        congrArg (fun n : ℕ => (n : ℝ))
          (squarefree_divisor_count_eq_two_pow_cardDistinctFactors Q hQ)
      have hcountReal :
        ((Q.divisors.filter (fun d => Squarefree d)).card : ℝ) =
          (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors Q := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcount
      rw [← hcountReal]

/--
Inputs: a nonzero natural number `k` and a divisor `l` of `k`.

Claim: the Möbius sum over divisors `d` of `k` that are multiples of `l`,
with summand `μ(k / d)`, is one when `k = l` and zero otherwise.

Proof: replace `d` by the complementary divisor `k / d`, then reduce to the
Möbius divisor sum of `k / l`.

Role: gives the finite interval cancellation needed to invert the Selberg
diagonal divisor transform.
-/
theorem moebius_sum_divisor_interval_eq_ite (k l : ℕ) (hk : k ≠ 0) (hlk : l ∣ k) :
    (∑ d ∈ k.divisors,
        if l ∣ d then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) else 0) =
      if k = l then 1 else 0 := by
  classical
  have hqk : k / l ∣ k := ⟨l, (Nat.div_mul_cancel hlk).symm⟩
  have hquot (e : ℕ) (he : e ∈ k.divisors) : l ∣ k / e ↔ e ∣ k / l := by
    rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors he)]
    rw [Nat.dvd_div_iff_mul_dvd hlk]
    constructor
    · intro h
      simpa only [Nat.mul_comm] using h
    · intro h
      simpa only [Nat.mul_comm] using h
  calc
    _ =
        ∑ d ∈ k.divisors,
          if l ∣ k / (k / d) then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d)
          else 0 :=
      by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hk]
    _ =
        ∑ d ∈ k.divisors,
          if l ∣ k / d then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0 :=
      by
      rw [Nat.sum_div_divisors k
          (fun e => if l ∣ k / e then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) e else 0)]
    _ =
        ∑ d ∈ k.divisors,
          if d ∣ k / l then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d else 0 :=
      by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : l ∣ k / d
      · have h' : d ∣ k / l := (hquot d hd).mp h
        simp only [ite_eq_left h, ite_eq_left h']
      · have h' : ¬d ∣ k / l := fun h' => h ((hquot d hd).mpr h')
        simp only [ite_eq_right h, ite_eq_right h']
    _ =
        ∑ d ∈ k.divisors.filter (fun d => d ∣ k / l),
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d :=
      by rw [← Finset.sum_filter]
    _ = ∑ d ∈ (k / l).divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d := by
      rw [Nat.divisors_filter_dvd_of_dvd hk hqk]
    _ = if k / l = 1 then 1 else 0 := moebius_sum_divisors_eq_ite_one (k / l)
    _ = if k = l then 1 else 0 := by
      by_cases hkl : k = l
      · have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hk hlk
        have hq : k / l = 1 := by rw [hkl, Nat.div_self (Nat.pos_of_ne_zero hl0)]
        change (if k / l = 1 then (1 : ℝ) else 0) = if k = l then 1 else 0
        simp only [ite_eq_left hq, ite_eq_left hkl]
      · have hq : k / l ≠ 1 := by
          intro hq
          have hdiv := Nat.div_mul_cancel hlk
          rw [hq, one_mul] at hdiv
          exact hkl hdiv.symm
        change (if k / l = 1 then (1 : ℝ) else 0) = if k = l then 1 else 0
        simp only [ite_eq_right hq, ite_eq_right hkl]

/--
Inputs: a nonzero sieve product `P`, a real diagonal vector `v`, and an
integer `d`.

Definition: `selbergDiagonalInverseWeight P v d` is `d` times the Möbius sum
of `v k` over divisors `k` of `P` that are multiples of `d`.

Output: the weight whose divisor transform is prescribed by `v`.

Role: constructs finite Λ² weights from desired Selberg diagonal variables.
-/
def selbergDiagonalInverseWeight (P : ℕ) (v : ℕ → ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) *
    ∑ k ∈ P.divisors,
      if d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) * v k else 0

/--
Inputs: a nonzero sieve product `P`, a real diagonal vector `v`, and a divisor
`l` of `P`.

Claim: the divisor transform of `selbergDiagonalInverseWeight P v` at `l` is
exactly `v l`.

Proof: exchange the finite divisor sums, restrict each inner sum to divisors
of `k`, and apply interval Möbius cancellation.

Role: proves that arbitrary diagonal coordinates can be realized by actual
Λ² sieve weights.
-/
theorem selbergDiagonalInverseWeight_realizes (P : ℕ) (hP : P ≠ 0) (v : ℕ → ℝ) {l : ℕ}
    (hl : l ∈ P.divisors) :
    (∑ d ∈ P.divisors, if l ∣ d then selbergDiagonalInverseWeight P v d / (d : ℝ) else 0) =
      v l := by
  classical
  have hweight (d : ℕ) (hd : d ∈ P.divisors) :
    selbergDiagonalInverseWeight P v d / (d : ℝ) =
      ∑ k ∈ P.divisors,
        if d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) * v k else 0 := by
    unfold selbergDiagonalInverseWeight
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast ne_zero_of_dvd_ne_zero hP (Nat.mem_divisors.mp hd).1
    exact mul_div_cancel_left₀ _ hd0
  have hcoeff (k : ℕ) (hk : k ∈ P.divisors) :
    (∑ d ∈ P.divisors,
        if l ∣ d ∧ d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) else 0) =
      if l ∣ k then (if k = l then 1 else 0) else 0 := by
    by_cases hlk : l ∣ k
    · have hk0 : k ≠ 0 := ne_zero_of_dvd_ne_zero hP (Nat.mem_divisors.mp hk).1
      have hfilter :
        P.divisors.filter (fun d => l ∣ d ∧ d ∣ k) = k.divisors.filter (fun d => l ∣ d) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hdP, hP0⟩, hld, hdk⟩
          exact ⟨⟨hdk, hk0⟩, hld⟩
        · rintro ⟨⟨hdk, hk0'⟩, hld⟩
          exact ⟨⟨hdk.trans (Nat.mem_divisors.mp hk).1, hP⟩, hld, hdk⟩
      calc
        _ =
            ∑ d ∈ P.divisors.filter (fun d => l ∣ d ∧ d ∣ k),
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) :=
          by rw [← Finset.sum_filter]
        _ =
            ∑ d ∈ k.divisors.filter (fun d => l ∣ d),
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) :=
          by rw [hfilter]
        _ = if k = l then 1 else 0 := by
          rw [Finset.sum_filter]
          exact moebius_sum_divisor_interval_eq_ite k l hk0 hlk
        _ = if l ∣ k then (if k = l then 1 else 0) else 0 := by simp only [hlk, ite_true]
    · have hz :
        ∀ d ∈ P.divisors,
          (if l ∣ d ∧ d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d)
            else 0) =
            0 := by
        intro d hd
        split_ifs with h
        · exact (hlk (h.1.trans h.2)).elim
        · rfl
      simp only [hlk, ite_false]
      exact Finset.sum_eq_zero fun d hd => hz d hd
  calc
    _ =
        ∑ d ∈ P.divisors,
          if l ∣ d then
            ∑ k ∈ P.divisors,
              if d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) * v k else 0
          else 0 :=
      by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hweight d hd]
    _ =
        ∑ d ∈ P.divisors,
          ∑ k ∈ P.divisors,
            if l ∣ d ∧ d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) * v k
            else 0 :=
      by simp_rw [Finset.ite_sum_zero, ← ite_and]
    _ =
        ∑ k ∈ P.divisors,
          ∑ d ∈ P.divisors,
            if l ∣ d ∧ d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) * v k
            else 0 :=
      by rw [Finset.sum_comm]
    _ =
        ∑ k ∈ P.divisors,
          (∑ d ∈ P.divisors,
              if l ∣ d ∧ d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d)
              else 0) *
            v k :=
      by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ =
            ∑ d ∈ P.divisors,
              (if l ∣ d ∧ d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d)
                else 0) *
                v k :=
          by
          apply Finset.sum_congr rfl
          intro d hd
          split_ifs with h
          · rfl
          · simp only [zero_mul]
        _ = _ :=
          (Finset.sum_mul P.divisors
              (fun d =>
                if l ∣ d ∧ d ∣ k then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d)
                else 0)
              (v k)).symm
    _ = ∑ k ∈ P.divisors, (if l ∣ k then (if k = l then 1 else 0) else 0) * v k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcoeff k hk]
    _ = v l := by
      rw [Finset.sum_eq_single l]
      · simp only [Nat.dvd_refl, ite_true, one_mul]
      · intro k hk hkl
        by_cases h : l ∣ k
        · simp only [h, ite_true, hkl, ite_false, zero_mul]
        · simp only [h, ite_false, zero_mul]
      · exact fun h => (h hl).elim

/--
Inputs: a nonzero finite sieve product `P` and real weights `w`.

Claim: the Möbius-weighted sum of the diagonal variables
`∑_{d ∈ P.divisors, l ∣ d} w(d) / d` equals `w 1`.

Proof: exchange the two finite divisor sums and apply Möbius cancellation to
the divisors of each `d`.

Role: provides the normalization needed to apply the weighted Cauchy inequality
to the Selberg quadratic main term.
-/
theorem selbergDiagonal_moebius_normalization (P : ℕ) (hP : P ≠ 0) (w : ℕ → ℝ) :
    (∑ l ∈ P.divisors,
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l *
          (∑ d ∈ P.divisors, if l ∣ d then w d / (d : ℝ) else 0)) =
      w 1 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hfilter (y : ℕ) (hy : y ∈ P.divisors) : P.divisors.filter (fun x => x ∣ y) = y.divisors := by
    ext x
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hxp, hP0⟩, hxy⟩
      exact ⟨hxy, ne_zero_of_dvd_ne_zero hP (Nat.mem_divisors.mp hy).1⟩
    · rintro ⟨hxy, hy0⟩
      exact ⟨⟨hxy.trans (Nat.mem_divisors.mp hy).1, hP⟩, hxy⟩
  have hinner (y : ℕ) (hy : y ∈ P.divisors) :
    (∑ x ∈ P.divisors,
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) x *
          if x ∣ y then w y / (y : ℝ) else 0) =
      (∑ x ∈ P.divisors,
          if x ∣ y then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) x else 0) *
        (w y / (y : ℝ)) := by
    calc
      _ =
          ∑ x ∈ P.divisors,
            (if x ∣ y then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) x else 0) *
              (w y / (y : ℝ)) :=
        by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxy : x ∣ y
        · simp only [ite_eq_left hxy]
        · simp only [ite_eq_right hxy, mul_zero, zero_mul]
      _ = _ := by rw [Finset.sum_mul]
  have hmu (y : ℕ) (hy : y ∈ P.divisors) :
    (∑ x ∈ P.divisors, if x ∣ y then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) x else 0) =
      if y = 1 then 1 else 0 := by
    rw [← Finset.sum_filter, hfilter y hy]
    exact moebius_sum_divisors_eq_ite_one y
  have hone : (1 : ℕ) ∈ P.divisors := by exact Nat.mem_divisors.mpr ⟨one_dvd P, hP⟩
  calc
    _ = ∑ y ∈ P.divisors, (if y = 1 then 1 else 0) * (w y / (y : ℝ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hinner y hy, hmu y hy]
    _ = w 1 := by
      rw [Finset.sum_eq_single 1]
      · simp only [ite_true, Nat.cast_one, div_one, one_mul]
      · intro y hy hyne
        simp only [ite_eq_right hyne, zero_mul]
      · intro hnot
        exact (hnot hone).elim

/--
Inputs: a range length `N`, a positive modulus `Q`, and a residue `a`.

Claim: the number of integers in `range N` congruent to `a` modulo `Q` is
`N / Q` plus one exactly when the residue occurs in the final incomplete
block.

Proof: rewrite the filtered range cardinality as `Nat.count`, then use
`Nat.count_modEq_card`.

Role: gives an exact count for the progression sieve's total mass and the
starting point for its divisor-counting remainder estimates.
-/
theorem progressionRangeCard_eq_quotient_add_last_block (N Q a : ℕ) (hQ : 0 < Q) :
    ((Finset.range N).filter (fun n => n % Q = a % Q)).card =
      N / Q + if a % Q < N % Q then 1 else 0 := by
  rw [← Nat.count_eq_card_filter_range]
  change Nat.count (fun n => Nat.ModEq Q n a) N = _
  exact Nat.count_modEq_card N hQ a

/--
Inputs: a bound `Y`, a modulus `Q`, a residue `a`, a sieve product `P`, and a
proof that `P` is squarefree.

Definition: the support is the progression `n ≤ Y`, `n ≡ a mod Q`; all
weights are one, the total mass is the support cardinality, and the local
density is the multiplicative function `1/n` on positive integers.

Output: a `BoundingSieve` with the requested support and sieve product.

Role: gives the concrete Selberg sieve used for progression prime counts;
divisor-counting remainders must still be bounded separately.
-/
noncomputable def progressionBoundingSieve (Y Q a P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := by
    intro n
    norm_num only
  totalMass := (((Finset.range (Y + 1)).filter (fun n => n % Q = a % Q)).card : ℝ)
  nu := ArithmeticFunction.pdiv ArithmeticFunction.zeta ArithmeticFunction.id
  nu_mult :=
    (ArithmeticFunction.isMultiplicative_zeta.natCast).pdiv
      (ArithmeticFunction.isMultiplicative_id.natCast)
  nu_pos_of_prime := by
    intro p hp hdiv
    have hp0 : p ≠ 0 := hp.ne_zero
    have hν :
      (ArithmeticFunction.pdiv ArithmeticFunction.zeta ArithmeticFunction.id) p = 1 / (p : ℝ) := by
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply, ite_eq_right hp0,
        ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
      norm_num only
    rw [hν]
    exact one_div_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp hdiv
    have hp0 : p ≠ 0 := hp.ne_zero
    have hν :
      (ArithmeticFunction.pdiv ArithmeticFunction.zeta ArithmeticFunction.id) p = 1 / (p : ℝ) := by
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply, ite_eq_right hp0,
        ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
      norm_num only
    rw [hν]
    have hpone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    rw [div_lt_iff₀ (by exact_mod_cast hp.pos)]
    simpa only [one_mul] using hpone

/--
Inputs: the canonical progression sieve and a positive modulus.

Claim: its total mass is the exact residue-class count from the quotient and
the final incomplete block.

Proof: unfold the total mass and apply
`progressionRangeCard_eq_quotient_add_last_block`.

Role: makes the progression's main scale explicit for later remainder bounds.
-/
theorem progressionBoundingSieve_totalMass_eq {Y Q a P : ℕ} (hP : Squarefree P) (hQ : 0 < Q) :
    (progressionBoundingSieve Y Q a P hP).totalMass =
      (((Y + 1) / Q + if a % Q < (Y + 1) % Q then 1 else 0 : ℕ) : ℝ) := by
  change (((Finset.range (Y + 1)).filter (fun n => n % Q = a % Q)).card : ℝ) = _
  exact_mod_cast progressionRangeCard_eq_quotient_add_last_block (Y + 1) Q a hQ

/--
Inputs: a divisor parameter `d` and the canonical progression sieve.

Claim: the sieve's `multSum d` equals the number of progression support
elements divisible by `d`.

Proof: all sieve weights are one, so the weighted divisibility sum is the
indicator sum for the filtered support.

Role: turns the abstract sieve remainder into a finite progression count.
-/
theorem progressionBoundingSieve_multSum_eq_card_filter {Y Q a P d : ℕ} (hP : Squarefree P) :
    (progressionBoundingSieve Y Q a P hP).multSum d =
      (((progressionBoundingSieve Y Q a P hP).support.filter (fun n => d ∣ n)).card : ℝ) := by
  change
    (∑ n ∈ (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q), if d ∣ n then (1 : ℝ) else 0) = _
  exact Finset.sum_boole (fun n => d ∣ n) ((Finset.range (Y + 1)).filter (fun n => n % Q = a % Q))

/--
Inputs: positive modulus `Q`, divisor `d` coprime to `Q`, and a residue `a`.

Claim: integers up to `Y` that are `a` modulo `Q` and divisible by `d` form
one residue class modulo `Q*d`, represented by the Chinese remainder theorem.

Proof: combine the two congruences using coprimality and the specification of
`Nat.chineseRemainder`.

Role: converts each sieve divisor count into a single progression count, so
`Nat.count_modEq_card` can give its exact value.
-/
theorem progressionDivisorFilter_eq_crtFilter (Y Q a d : ℕ) (hcop : Nat.Coprime d Q) :
    (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q ∧ d ∣ n) =
      (Finset.range (Y + 1)).filter
        (fun n => Nat.ModEq (Q * d) n (Nat.chineseRemainder hcop.symm a 0).val) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hn, hqa, hdiv⟩
    have hq : Nat.ModEq Q n a := by simpa only [Nat.ModEq] using hqa
    have hd : Nat.ModEq d n 0 := Nat.modEq_zero_iff_dvd.mpr hdiv
    have hqc : Nat.ModEq Q n (Nat.chineseRemainder hcop.symm a 0).val :=
      hq.trans (Nat.chineseRemainder hcop.symm a 0).property.1.symm
    have hdc : Nat.ModEq d n (Nat.chineseRemainder hcop.symm a 0).val :=
      hd.trans (Nat.chineseRemainder hcop.symm a 0).property.2.symm
    exact ⟨hn, (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp ⟨hqc, hdc⟩⟩
  · rintro ⟨hn, hprod⟩
    have hparts := (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mpr hprod
    have hqa : Nat.ModEq Q n a := hparts.1.trans (Nat.chineseRemainder hcop.symm a 0).property.1
    have hd : Nat.ModEq d n 0 := hparts.2.trans (Nat.chineseRemainder hcop.symm a 0).property.2
    exact ⟨hn, by simpa only [Nat.ModEq] using hqa, Nat.modEq_zero_iff_dvd.mp hd⟩

/--
Inputs: positive moduli `Q` and `d`, with `d` coprime to `Q`.

Claim: the number of multiples of `d` in the residue class `a` modulo `Q`,
up to `Y`, is the quotient by `Q*d` plus the final-block indicator for the
CRT residue.

Proof: identify the two congruences with their CRT residue modulo `Q*d`, then
apply the exact residue-class count on a finite range.

Role: gives an explicit formula for every divisor term in the progression
sieve's remainder sum.
-/
theorem progressionDivisorFilter_card_eq_quotient_add_last_block (Y Q a d : ℕ) (hQ : 0 < Q)
    (hd : 0 < d) (hcop : Nat.Coprime d Q) :
    ((Finset.range (Y + 1)).filter (fun n => n % Q = a % Q ∧ d ∣ n)).card =
      (Y + 1) / (Q * d) +
        if (Nat.chineseRemainder hcop.symm a 0).val % (Q * d) < (Y + 1) % (Q * d) then 1
        else 0 := by
  rw [progressionDivisorFilter_eq_crtFilter Y Q a d hcop]
  change
    ((Finset.range (Y + 1)).filter
          (fun n => n % (Q * d) = (Nat.chineseRemainder hcop.symm a 0).val % (Q * d))).card =
      _
  exact
    progressionRangeCard_eq_quotient_add_last_block (Y + 1) (Q * d)
      (Nat.chineseRemainder hcop.symm a 0).val (Nat.mul_pos hQ hd)

/--
Inputs: the canonical progression sieve and a positive divisor `d` coprime
to `Q`.

Claim: the weighted count of support elements divisible by `d` equals the
explicit quotient and final-block formula for the CRT residue modulo `Q*d`.

Proof: rewrite the weight sum as a filtered cardinality, split the filters,
and apply the CRT count formula.

Role: gives a closed arithmetic expression for the sieve's divisor sums.
-/
theorem progressionBoundingSieve_multSum_eq_crt_quotient {Y Q a P d : ℕ} (hP : Squarefree P)
    (hQ : 0 < Q) (hd : 0 < d) (hcop : Nat.Coprime d Q) :
    (progressionBoundingSieve Y Q a P hP).multSum d =
      (((Y + 1) / (Q * d) +
            if (Nat.chineseRemainder hcop.symm a 0).val % (Q * d) < (Y + 1) % (Q * d) then 1
            else 0 :
          ℕ) :
        ℝ) := by
  rw [progressionBoundingSieve_multSum_eq_card_filter]
  change
    ((((Finset.range (Y + 1)).filter (fun n => n % Q = a % Q)).filter (fun n => d ∣ n)).card : ℝ) =
      _
  rw [Finset.filter_filter]
  exact_mod_cast progressionDivisorFilter_card_eq_quotient_add_last_block Y Q a d hQ hd hcop

/--
Inputs: a canonical progression sieve and a positive natural number `d`.

Claim: the sieve's local density at `d` is exactly `1/d`.

Proof: unfold the multiplicative-function quotient defining the local density
and use positivity of `d` to select its nonzero branch.

Role: supplies the concrete local density for the diagonalized Λ² main term.
-/
theorem progressionBoundingSieve_nu_eq_inv {Y Q a P d : ℕ} (hP : Squarefree P) (hd : 0 < d) :
    (progressionBoundingSieve Y Q a P hP).nu d = 1 / (d : ℝ) := by
  dsimp only [progressionBoundingSieve]
  simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply,
    ite_eq_right (Nat.ne_of_gt hd), ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
  norm_num only

/--
Inputs: a canonical progression sieve and a positive natural number `d`.

Claim: the Selberg term at `d` equals the reciprocal of Euler's totient.

Proof: substitute the local density `1/d` in Selberg's product formula and
use Euler's product formula for the totient.

Role: identifies the diagonal coefficients in the Λ² main sum explicitly.
-/
theorem progressionBoundingSieve_selbergTerms_eq_totient_inv {Y Q a P d : ℕ} (hP : Squarefree P)
    (hd : 0 < d) :
    (BoundingSieve.selbergTerms (s := progressionBoundingSieve Y Q a P hP) d) =
      1 / (Nat.totient d : ℝ) := by
  rw [BoundingSieve.selbergTerms_apply, progressionBoundingSieve_nu_eq_inv hP hd]
  have hprod :
    ∏ p ∈ d.primeFactors, (1 - (progressionBoundingSieve Y Q a P hP).nu p)⁻¹ =
      (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [progressionBoundingSieve_nu_eq_inv hP (Nat.pos_of_mem_primeFactors hp)]
    simp only [one_div]
  rw [hprod]
  have hphiQ := Nat.totient_eq_mul_prod_factors d
  have hphiR := congrArg (fun x : ℚ => (x : ℝ)) hphiQ
  simp only [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv,
    Rat.cast_natCast] at hphiR
  let F : ℝ := ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)
  have hphi : (Nat.totient d : ℝ) = (d : ℝ) * F := by simpa only [F] using hphiR
  have hdR : (d : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hd)
  have hphiRpos : (Nat.totient d : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast Nat.totient_pos.mpr hd)
  have hF : F ≠ 0 := by
    intro hf
    apply hphiRpos
    rw [hphi, hf]
    simp only [mul_zero]
  change (1 / (d : ℝ)) * F⁻¹ = 1 / (Nat.totient d : ℝ)
  rw [hphi]
  field_simp [hdR, hF]

/--
Inputs: a canonical progression sieve and a positive natural number `d`.

Claim: the inverse Selberg term at `d` is `φ(d)`.

Proof: invert the totient formula and use positivity of the totient.

Role: gives the coefficient in the diagonal Λ² main-term quadratic form.
-/
theorem progressionBoundingSieve_selbergTerms_inv_eq_totient {Y Q a P d : ℕ} (hP : Squarefree P)
    (hd : 0 < d) :
    (BoundingSieve.selbergTerms (s := progressionBoundingSieve Y Q a P hP) d)⁻¹ =
      (Nat.totient d : ℝ) := by
  rw [progressionBoundingSieve_selbergTerms_eq_totient_inv hP hd]
  field_simp

/--
Inputs: the canonical progression sieve and a positive divisor `d` coprime
to the progression modulus `Q`.

Claim: the absolute value of the sieve remainder at `d` is at most one.

Proof: the exact CRT count gives `multSum d`; the exact support count gives
`totalMass`. Their quotient decompositions differ by two indicators in
`{0, 1}`, and the incomplete block has length less than `d`.

Role: bounds each term in the Selberg remainder sum whenever every sieve
divisor is coprime to `Q`.
-/
theorem progressionBoundingSieve_rem_abs_le_one {Y Q a P d : ℕ} (hP : Squarefree P) (hQ : 0 < Q)
    (hd : 0 < d) (hcop : Nat.Coprime d Q) : |(progressionBoundingSieve Y Q a P hP).rem d| ≤ 1 := by
  dsimp only [BoundingSieve.rem]
  let q : ℕ := (Y + 1) / Q
  let k : ℕ := (Y + 1) / (Q * d)
  let r : ℕ := q % d
  let eQ : ℕ := if a % Q < (Y + 1) % Q then 1 else 0
  let eQD : ℕ :=
    if (Nat.chineseRemainder hcop.symm a 0).val % (Q * d) < (Y + 1) % (Q * d) then 1 else 0
  have hmass : (progressionBoundingSieve Y Q a P hP).totalMass = (q : ℝ) + (eQ : ℝ) := by
    rw [progressionBoundingSieve_totalMass_eq hP hQ]
    simp only [q, eQ, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hmult : (progressionBoundingSieve Y Q a P hP).multSum d = (k : ℝ) + (eQD : ℝ) := by
    rw [progressionBoundingSieve_multSum_eq_crt_quotient hP hQ hd hcop]
    simp only [k, eQD, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hnu : (progressionBoundingSieve Y Q a P hP).nu d = 1 / (d : ℝ) := by
    dsimp only [progressionBoundingSieve]
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply,
      ite_eq_right (Nat.ne_of_gt hd), ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
    norm_num only
  have hdecomp : q = r + d * k := by
    dsimp only [q, r, k]
    rw [← Nat.div_div_eq_div_mul]
    exact (Nat.mod_add_div ((Y + 1) / Q) d).symm
  have hdecompReal : (q : ℝ) = (r : ℝ) + (d : ℝ) * (k : ℝ) := by exact_mod_cast hdecomp
  have hrlt : r < d := by
    dsimp only [r]
    exact Nat.mod_lt q hd
  have heQNat : eQ ≤ 1 := by
    dsimp only [eQ]
    split_ifs <;> norm_num only
  have heQd : r + eQ ≤ d := by
    have hsucc : r + 1 ≤ d := Nat.succ_le_iff.mpr hrlt
    exact (Nat.add_le_add_left heQNat r).trans hsucc
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnum : (r : ℝ) + (eQ : ℝ) ≤ (d : ℝ) := by exact_mod_cast heQd
  have hnumNonneg : 0 ≤ (r : ℝ) + (eQ : ℝ) := by positivity
  have hfracNonneg : 0 ≤ ((r : ℝ) + (eQ : ℝ)) / (d : ℝ) := div_nonneg hnumNonneg hdReal.le
  have hfracLe : ((r : ℝ) + (eQ : ℝ)) / (d : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hdReal]
    simpa only [one_mul] using hnum
  have heQD0 : (0 : ℝ) ≤ (eQD : ℝ) := by
    dsimp only [eQD]
    split_ifs <;> norm_num only
  have heQD1 : (eQD : ℝ) ≤ 1 := by
    dsimp only [eQD]
    split_ifs <;> norm_num only
  have hrem :
    (progressionBoundingSieve Y Q a P hP).multSum d -
        (progressionBoundingSieve Y Q a P hP).nu d *
          (progressionBoundingSieve Y Q a P hP).totalMass =
      (eQD : ℝ) - ((r : ℝ) + (eQ : ℝ)) / (d : ℝ) := by
    rw [hmult, hnu, hmass, hdecompReal]
    field_simp [ne_of_gt hdReal]
    ring
  rw [hrem, abs_le]
  constructor
  · linarith only [heQD0, hfracLe]
  · linarith only [heQD1, hfracNonneg]

/--
Inputs: a squarefree sieve product coprime to the progression modulus and an
upper Moebius coefficient function.

Claim: the absolute remainder sum of the concrete progression sieve is at
most the sum of the absolute upper coefficients over divisors of the product.

Proof: every divisor remains coprime to the modulus, so its progression
remainder has absolute value at most one; apply this termwise in `errSum`.

Role: reduces the Selberg remainder estimate to a finite coefficient sum.
-/
theorem progressionBoundingSieve_errSum_le_sum_abs {Y Q a P : ℕ} (hP : Squarefree P) (hQ : 0 < Q)
    (hPQ : Nat.Coprime P Q) (muPlus : ℕ → ℝ) :
    (progressionBoundingSieve Y Q a P hP).errSum muPlus ≤ ∑ d ∈ P.divisors, |muPlus d| := by
  rw [BoundingSieve.errSum]
  apply Finset.sum_le_sum
  intro d hd
  have hdiv : d ∣ P := (Nat.mem_divisors.mp hd).1
  have hP0 : P ≠ 0 := (Nat.mem_divisors.mp hd).2
  have hd0 : d ≠ 0 := by
    intro hz
    subst d
    rcases hdiv with ⟨k, hk⟩
    simp only [zero_mul] at hk
    exact hP0 hk
  have hcopd : Nat.Coprime d Q := Nat.Coprime.of_dvd_left hdiv hPQ
  have hrem :=
    progressionBoundingSieve_rem_abs_le_one (Y := Y) (Q := Q) (a := a) (P := P) (d := d) hP hQ
      (Nat.pos_of_ne_zero hd0) hcopd
  calc
    |muPlus d| * |(progressionBoundingSieve Y Q a P hP).rem d| ≤ |muPlus d| * 1 :=
      mul_le_mul_of_nonneg_left hrem (abs_nonneg _)
    _ = |muPlus d| := mul_one _

/--
Inputs: a weight function and a divisor `d`.

Claim: the absolute value of the Λ² coefficient at `d` is bounded by the
double sum of the absolute products of its input weights over divisors of `d`.

Proof: apply the triangle inequality to both finite sums and bound each
filtered summand by the corresponding absolute product.

Role: converts an error estimate for Λ² coefficients into a finite estimate
on the underlying sieve weights.
-/
theorem lambdaSquared_abs_le_divisor_weight_sum (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
  unfold BoundingSieve.lambdaSquared
  calc
    |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| ≤
        ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
      apply Finset.sum_le_sum
      intro d1 hd1
      calc
        |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| ≤
            ∑ d2 ∈ d.divisors, |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
          apply Finset.sum_le_sum
          intro d2 hd2
          by_cases heq : d = Nat.lcm d1 d2
          · simp only [heq, ite_true, abs_mul]
            exact le_rfl
          · simp only [heq, ite_false, abs_zero]
            exact mul_nonneg (abs_nonneg (w d1)) (abs_nonneg (w d2))

/--
Inputs: a squarefree sieve product coprime to the progression modulus and a
weight function for the Λ² construction.

Claim: the concrete progression sieve's error sum is bounded by the divisor
double sum of absolute products of the input weights.

Proof: first bound the remainder term by one for each product divisor, then
apply `lambdaSquared_abs_le_divisor_weight_sum` termwise.

Role: makes the remaining error estimate depend directly on the chosen
Selberg weights.
-/
theorem progressionBoundingSieve_lambdaSquared_errSum_le {Y Q a P : ℕ} (hP : Squarefree P)
    (hQ : 0 < Q) (hPQ : Nat.Coprime P Q) (w : ℕ → ℝ) :
    (progressionBoundingSieve Y Q a P hP).errSum (BoundingSieve.lambdaSquared w) ≤
      ∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
  calc
    (progressionBoundingSieve Y Q a P hP).errSum (BoundingSieve.lambdaSquared w) ≤
        ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| :=
      progressionBoundingSieve_errSum_le_sum_abs hP hQ hPQ _
    _ ≤ ∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
      apply Finset.sum_le_sum
      intro d hd
      exact lambdaSquared_abs_le_divisor_weight_sum w d

/--
Inputs: a weight function and a divisor `d`.

Claim: the absolute Λ² coefficient is bounded by the sum of absolute weight
products over divisor pairs whose least common multiple is exactly `d`.

Proof: apply the triangle inequality to both sums and take absolute values
only for terms selected by the least-common-multiple condition.

Role: retains the support condition needed to sum coefficient errors without
counting the same divisor pair once for every common multiple.
-/
theorem lambdaSquared_abs_le_lcm_sum (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤
      ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
  unfold BoundingSieve.lambdaSquared
  calc
    |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| ≤
        ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
      apply Finset.sum_le_sum
      intro d1 hd1
      calc
        |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| ≤
            ∑ d2 ∈ d.divisors, |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
          simp only [abs_ite, abs_zero, abs_mul]

/--
Inputs: a natural number `P` and a weight function on the natural numbers.

Claim: the sum of absolute Λ² coefficients over `P`'s divisors is at most
the square of the absolute input-weight sum over those divisors.

Proof: retain the least-common-multiple condition in the triangle bound,
enlarge divisor sets to those of `P`, then sum each pair at its unique lcm.

Role: gives an error bound that does not multiply by the number of divisors
of `P`.
-/
theorem lambdaSquared_divisor_abs_sum_le_square (P : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤ (∑ d ∈ P.divisors, |w d|) ^ 2 := by
  have hsub : ∀ d ∈ P.divisors, d.divisors ⊆ P.divisors := by
    intro d hd e he
    have hd' := Nat.mem_divisors.mp hd
    have he' := Nat.mem_divisors.mp he
    exact Nat.mem_divisors.mpr ⟨he'.1.trans hd'.1, hd'.2⟩
  have hterm : ∀ d d1 d2, 0 ≤ (if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0) := by
    intro d d1 d2
    by_cases h : d = Nat.lcm d1 d2
    · simp only [h, ite_true]
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    · simp only [h, ite_false]
      exact le_of_eq rfl
  have hbound :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤
      ∑ d ∈ P.divisors,
        ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
    apply Finset.sum_le_sum
    intro d hd
    have hsubd := hsub d hd
    calc
      |BoundingSieve.lambdaSquared w d| ≤
          ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 :=
        lambdaSquared_abs_le_lcm_sum w d
      _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ P.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 :=
        by
        apply Finset.sum_le_sum
        intro d1 hd1
        exact
          Finset.sum_le_sum_of_subset_of_nonneg hsubd
            (by
              intro d2 hd2 _
              exact hterm d d1 d2)
      _ ≤ ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubd
          (by
            intro d1 hd1 _
            exact
              Finset.sum_nonneg
                (by
                  intro d2 hd2
                  exact hterm d d1 d2))
  have hcollapse :
    (∑ d ∈ P.divisors,
        ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0) =
      ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2| := by
    calc
      (∑ d ∈ P.divisors,
            ∑ d1 ∈ P.divisors,
              ∑ d2 ∈ P.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0) =
          ∑ d1 ∈ P.divisors,
            ∑ d ∈ P.divisors, ∑ d2 ∈ P.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 :=
        by
        rw [Finset.sum_comm (s := P.divisors) (t := P.divisors) (f := fun d d1 =>
            ∑ d2 ∈ P.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0)]
      _ =
          ∑ d1 ∈ P.divisors,
            ∑ d2 ∈ P.divisors, ∑ d ∈ P.divisors, if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 :=
        by
        apply Finset.sum_congr rfl
        intro d1 hd1
        rw [Finset.sum_comm (s := P.divisors) (t := P.divisors) (f := fun d d2 =>
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0)]
      _ = ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2| := by
        apply Finset.sum_congr rfl
        intro d1 hd1
        apply Finset.sum_congr rfl
        intro d2 hd2
        have hlcm : Nat.lcm d1 d2 ∈ P.divisors := by
          apply Nat.mem_divisors.mpr
          exact
            ⟨Nat.lcm_dvd_iff.mpr ⟨(Nat.mem_divisors.mp hd1).1, (Nat.mem_divisors.mp hd2).1⟩,
              (Nat.mem_divisors.mp hd1).2⟩
        rw [Finset.sum_ite_eq_of_mem' P.divisors (Nat.lcm d1 d2) (fun _ => |w d1| * |w d2|) hlcm]
  calc
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤
        ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2| :=
      by
      rw [← hcollapse]
      exact hbound
    _ = (∑ d ∈ P.divisors, |w d|) ^ 2 := by
      rw [← Finset.sum_mul_sum]
      simp only [pow_two]

/--
Inputs: a natural number `P` and a weight function on the natural numbers.

Claim: the nested divisor sum over `d ∣ P`, `d₁ ∣ d`, and `d₂ ∣ d` is at
most the number of divisors of `P` times the unrestricted double divisor sum.

Proof: each divisor set of `d` is contained in the divisor set of `P`; all
summands are nonnegative, so enlarge both inner sums termwise.

Role: gives a uniform finite bound for the Λ² remainder coefficients.
-/
theorem divisorTripleWeightSum_le_card_mul_doubleSum (P : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2|) ≤
      (P.divisors.card : ℝ) * (∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2|) := by
  have hsub : ∀ d ∈ P.divisors, d.divisors ⊆ P.divisors := by
    intro d hd e he
    have hd' := Nat.mem_divisors.mp hd
    have he' := Nat.mem_divisors.mp he
    exact Nat.mem_divisors.mpr ⟨he'.1.trans hd'.1, hd'.2⟩
  have hnonneg : ∀ d1 d2, 0 ≤ |w d1| * |w d2| := by
    intro d1 d2
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc
    (∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2|) ≤
        ∑ d ∈ P.divisors, (∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2|) :=
      by
      apply Finset.sum_le_sum
      intro d hd
      have hsubd := hsub d hd
      calc
        (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2|) ≤
            ∑ d1 ∈ d.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2| :=
          by
          apply Finset.sum_le_sum
          intro d1 hd1
          exact
            Finset.sum_le_sum_of_subset_of_nonneg hsubd
              (by
                intro d2 hd2 _
                exact hnonneg d1 d2)
        _ ≤ ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2| :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubd
            (by
              intro d1 hd1 _
              exact
                Finset.sum_nonneg
                  (by
                    intro d2 hd2
                    exact hnonneg d1 d2))
    _ = (P.divisors.card : ℝ) * (∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2|) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/--
Inputs: a squarefree sieve product coprime to the progression modulus and a
weight function for the Λ² construction.

Claim: the concrete progression sieve's error sum is at most the square of
the absolute weight sum over divisors of `P`.

Proof: the remainder is at most one, and each divisor pair contributes only
at its unique least common multiple; express the resulting double sum as a
square.

Role: supplies the error estimate for selecting and truncating Selberg weights.
-/
theorem progressionBoundingSieve_lambdaSquared_errSum_le_square {Y Q a P : ℕ} (hP : Squarefree P)
    (hQ : 0 < Q) (hPQ : Nat.Coprime P Q) (w : ℕ → ℝ) :
    (progressionBoundingSieve Y Q a P hP).errSum (BoundingSieve.lambdaSquared w) ≤
      (∑ d ∈ P.divisors, |w d|) ^ 2 := by
  calc
    (progressionBoundingSieve Y Q a P hP).errSum (BoundingSieve.lambdaSquared w) ≤
        ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| :=
      progressionBoundingSieve_errSum_le_sum_abs hP hQ hPQ _
    _ ≤ (∑ d ∈ P.divisors, |w d|) ^ 2 := lambdaSquared_divisor_abs_sum_le_square P w

/--
Inputs: the canonical progression sieve and a weight function for its Λ² sieve.

Claim: the Λ² main sum is the diagonalized finite quadratic form over divisors
of the sieve product.

Proof: specialize mathlib's Selberg diagonalization theorem to the concrete
progression sieve.

Role: exposes the exact main-term expression to be optimized for the
Brun–Titchmarsh estimate; its local density is `1/d` by
`progressionBoundingSieve_nu_eq_inv`.
-/
theorem progressionBoundingSieve_lambdaSquared_mainSum_diagonalized {Y Q a P : ℕ}
    (hP : Squarefree P) (w : ℕ → ℝ) :
    (progressionBoundingSieve Y Q a P hP).mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ P.divisors,
        (BoundingSieve.selbergTerms (s := progressionBoundingSieve Y Q a P hP) l)⁻¹ *
          (∑ d ∈ P.divisors,
              if l ∣ d then (progressionBoundingSieve Y Q a P hP).nu d * w d else 0) ^
            2 := by
  exact
    BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq (s := progressionBoundingSieve Y Q a P hP)
      w

/--
Inputs: a canonical progression sieve and a weight function for its Λ² sieve.

Claim: its Λ² main sum is the sum of the squared divisor-weight expressions
with Euler totient coefficients.

Proof: rewrite mathlib's diagonalization using the concrete local density and
the identity between inverse Selberg terms and totients.

Role: puts the main-term optimization into its explicit arithmetic form.
-/
theorem progressionBoundingSieve_lambdaSquared_mainSum_totient_form {Y Q a P : ℕ}
    (hP : Squarefree P) (w : ℕ → ℝ) :
    (progressionBoundingSieve Y Q a P hP).mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ P.divisors,
        (Nat.totient l : ℝ) * (∑ d ∈ P.divisors, if l ∣ d then (1 / (d : ℝ)) * w d else 0) ^ 2 := by
  rw [progressionBoundingSieve_lambdaSquared_mainSum_diagonalized]
  apply Finset.sum_congr rfl
  intro l hl
  have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hl).1
  rw [progressionBoundingSieve_selbergTerms_inv_eq_totient hP (Nat.pos_of_ne_zero hl0)]
  apply congrArg (fun t : ℝ => (Nat.totient l : ℝ) * t)
  apply congrArg (fun t : ℝ => t ^ 2)
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hd).1
  by_cases hld : l ∣ d
  · simp only [hld, ite_true]
    rw [progressionBoundingSieve_nu_eq_inv hP (Nat.pos_of_ne_zero hd0)]
  · simp only [hld, ite_false]

/--
Inputs: a squarefree sieve product and any real vector on its divisors.

Claim: the inverse Möbius weight realizes the prescribed diagonal vector in the
Λ² main sum, which therefore equals the totient-weighted sum of its squares.

Proof: rewrite the main sum in totient form and apply
`selbergDiagonalInverseWeight_realizes` to each divisor coordinate.

Role: connects finite Möbius inversion to the exact optimization problem for
the Selberg main term.
-/
theorem progressionBoundingSieve_lambdaSquared_mainSum_inverseWeight_eq {Y Q a P : ℕ}
    (hP : Squarefree P) (v : ℕ → ℝ) :
    (progressionBoundingSieve Y Q a P hP).mainSum
        (BoundingSieve.lambdaSquared (selbergDiagonalInverseWeight P v)) =
      ∑ l ∈ P.divisors, (Nat.totient l : ℝ) * v l ^ 2 := by
  rw [progressionBoundingSieve_lambdaSquared_mainSum_totient_form]
  apply Finset.sum_congr rfl
  intro l hl
  have hdiag :
    (∑ d ∈ P.divisors, if l ∣ d then (1 / (d : ℝ)) * selbergDiagonalInverseWeight P v d else 0) =
      v l := by
    calc
      _ = ∑ d ∈ P.divisors, if l ∣ d then selbergDiagonalInverseWeight P v d / (d : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hld : l ∣ d
        · simp only [hld, ite_true]
          rw [one_div, div_eq_mul_inv, mul_comm]
        · simp only [hld, ite_false]
      _ = v l := selbergDiagonalInverseWeight_realizes P hP.ne_zero v hl
  rw [hdiag]

/--
Inputs: a real normalization constant `G` and an integer `l`.

Definition: `selbergOptimalDiagonal G l` is the Möbius coordinate divided by
`φ(l) G`, the candidate equality vector for the finite Selberg quadratic form.

Role: provides the diagonal vector whose inverse weight is expected to attain
the reciprocal totient-sum lower bound.
-/
noncomputable def selbergOptimalDiagonal (G : ℝ) (l : ℕ) : ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l / ((Nat.totient l : ℝ) * G)

/--
Inputs: a natural sieve product `P` and a divisor cutoff `z`.

Definition: `selbergTruncatedTotientSum P z` sums `1 / φ(l)` over divisors
`l` of `P` with `l ≤ z`.

Role: gives the normalizing constant for a Selberg weight supported on divisors
up to `z`.
-/
noncomputable def selbergTruncatedTotientSum (P z : ℕ) : ℝ :=
  ∑ l ∈ P.divisors, if l ≤ z then 1 / (Nat.totient l : ℝ) else 0

/--
Inputs: a divisor cutoff `z`, a real normalizer `G`, and a natural divisor `l`.

Definition: `selbergTruncatedOptimalDiagonal z G l` is the Möbius equality
coordinate below the cutoff and zero above it.

Role: its inverse Möbius transform produces Selberg weights supported on
divisors no larger than `z`.
-/
noncomputable def selbergTruncatedOptimalDiagonal (z : ℕ) (G : ℝ) (l : ℕ) : ℝ :=
  if l ≤ z then selbergOptimalDiagonal G l else 0

/--
Inputs: a sieve product `P`, cutoff `z`, normalizer `G`, and divisor `d`.

Definition: `selbergTruncatedOptimalWeight P z G d` is the inverse Möbius
weight of the cutoff diagonal vector.

Role: supplies the concrete coefficient function used in the truncated
Brun–Titchmarsh sieve bound.
-/
noncomputable def selbergTruncatedOptimalWeight (P z : ℕ) (G : ℝ) (d : ℕ) : ℝ :=
  selbergDiagonalInverseWeight P (selbergTruncatedOptimalDiagonal z G) d

/--
Inputs: a squarefree sieve product `P`, a cutoff `z`, and a divisibility
certificate for every positive squarefree integer at most `z`.

Claim: the truncated reciprocal-totient sum dominates the reciprocal sum of
the positive squarefree integers through `z`.

Proof: compare each reciprocal with `1 / φ(n)` using `φ(n) ≤ n`, then enlarge
the finite sum to all divisors of `P` below the cutoff.

Role: reduces a quantitative lower bound for the Selberg normalizer to a
reciprocal sum over squarefree integers once a suitable sieve product is constructed.
-/
theorem selbergTruncatedTotientSum_ge_reciprocal_sum {P z : ℕ} (hP : Squarefree P)
    (hdiv : ∀ n : ℕ, 1 ≤ n → n ≤ z → Squarefree n → n ∣ P) :
    (∑ n ∈ (Finset.range (z + 1)).filter (fun n => 0 < n ∧ Squarefree n), 1 / (n : ℝ)) ≤
      selbergTruncatedTotientSum P z := by
  classical
  unfold selbergTruncatedTotientSum
  calc
    _ ≤
        ∑ n ∈ (Finset.range (z + 1)).filter (fun n => 0 < n ∧ Squarefree n),
          if n ≤ z then 1 / (Nat.totient n : ℝ) else 0 :=
      by
      apply Finset.sum_le_sum
      intro n hn
      have hmem := Finset.mem_filter.mp hn
      have hnz : n ≤ z := Nat.le_of_lt_succ (Finset.mem_range.mp hmem.1)
      have hphi : 0 < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hmem.2.1
      have hphi_le : (Nat.totient n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.totient_le n
      simp only [hnz, ite_true]
      exact one_div_le_one_div_of_le hphi hphi_le
    _ ≤ ∑ n ∈ P.divisors, if n ≤ z then 1 / (Nat.totient n : ℝ) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hmem := Finset.mem_filter.mp hn
        have hnz : n ≤ z := Nat.le_of_lt_succ (Finset.mem_range.mp hmem.1)
        have hndvd := hdiv n (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmem.2.1)) hnz hmem.2.2
        exact Nat.mem_divisors.mpr ⟨hndvd, hP.ne_zero⟩
      · intro n hn hnot
        have hndvd := (Nat.mem_divisors.mp hn).1
        have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hndvd
        have hphi : 0 < (Nat.totient n : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
        by_cases hnz : n ≤ z
        · simp only [hnz, ite_true]
          exact le_of_lt (one_div_pos.mpr hphi)
        · simp only [hnz, ite_false]
          exact le_rfl

/--
Inputs: a squarefree sieve product `P`, a cutoff `z`, a modulus `Q`, and a
divisibility certificate for squarefree integers coprime to `Q`.

Claim: the truncated reciprocal-totient sum dominates the reciprocal sum of
the positive squarefree integers through `z` that are coprime to `Q`.

Proof: compare reciprocals with reciprocal totients, then include their
divisors in the sieve normalizer using the supplied divisibility certificate.

Role: supports sieve products that omit prime factors of the progression
modulus.
-/
theorem selbergTruncatedTotientSum_ge_coprime_reciprocal_sum {P z Q : ℕ} (hP : Squarefree P)
    (hdiv : ∀ n : ℕ, 1 ≤ n → n ≤ z → Squarefree n → Nat.Coprime n Q → n ∣ P) :
    (∑ n ∈ (Finset.range (z + 1)).filter (fun n => 0 < n ∧ Squarefree n ∧ Nat.Coprime n Q),
        1 / (n : ℝ)) ≤
      selbergTruncatedTotientSum P z := by
  classical
  unfold selbergTruncatedTotientSum
  calc
    _ ≤
        ∑ n ∈ (Finset.range (z + 1)).filter (fun n => 0 < n ∧ Squarefree n ∧ Nat.Coprime n Q),
          if n ≤ z then 1 / (Nat.totient n : ℝ) else 0 :=
      by
      apply Finset.sum_le_sum
      intro n hn
      have hmem := Finset.mem_filter.mp hn
      have hnz : n ≤ z := Nat.le_of_lt_succ (Finset.mem_range.mp hmem.1)
      have hphi : 0 < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hmem.2.1
      have hphi_le : (Nat.totient n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.totient_le n
      simp only [hnz, ite_true]
      exact one_div_le_one_div_of_le hphi hphi_le
    _ ≤ ∑ n ∈ P.divisors, if n ≤ z then 1 / (Nat.totient n : ℝ) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hmem := Finset.mem_filter.mp hn
        have hnz : n ≤ z := Nat.le_of_lt_succ (Finset.mem_range.mp hmem.1)
        have hndvd :=
          hdiv n (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmem.2.1)) hnz hmem.2.2.1 hmem.2.2.2
        exact Nat.mem_divisors.mpr ⟨hndvd, hP.ne_zero⟩
      · intro n hn hnot
        have hndvd := (Nat.mem_divisors.mp hn).1
        have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hndvd
        have hphi : 0 < (Nat.totient n : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
        by_cases hnz : n ≤ z
        · simp only [hnz, ite_true]
          exact le_of_lt (one_div_pos.mpr hphi)
        · simp only [hnz, ite_false]
          exact le_rfl

/--
Inputs: a nonzero natural number `P` and a cutoff `z ≥ 1`.

Claim: `selbergTruncatedTotientSum P z` is positive.

Proof: every included reciprocal totient is positive, and the divisor `1` is
included.

Role: proves that the truncated Selberg normalizer is nonzero.
-/
theorem selbergTruncatedTotientSum_pos {P z : ℕ} (hP : P ≠ 0) (hz : 1 ≤ z) :
    0 < selbergTruncatedTotientSum P z := by
  classical
  unfold selbergTruncatedTotientSum
  apply Finset.sum_pos'
  · intro l hl
    have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hP (Nat.mem_divisors.mp hl).1
    have hphi : 0 < (Nat.totient l : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0)
    by_cases hcut : l ≤ z
    · simp only [hcut, ite_true]
      exact le_of_lt (one_div_pos.mpr hphi)
    · simp only [hcut, ite_false]
      exact le_of_eq rfl
  · refine ⟨1, Nat.mem_divisors.mpr ⟨Nat.one_dvd P, hP⟩, ?_⟩
    simp only [hz, ite_true, Nat.totient_one, Nat.cast_one]
    norm_num only

/--
Inputs: a nonzero natural number `P`.

Claim: the sum of `1 / φ(l)` over divisors of `P` is positive.

Proof: every divisor is positive, so each totient reciprocal is positive; the
divisor set contains one.

Role: supplies the nonzero normalization constant for the optimal Selberg
diagonal vector.
-/
theorem reciprocalTotientDivisorSum_pos {P : ℕ} (hP : P ≠ 0) :
    0 < ∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ) := by
  classical
  apply Finset.sum_pos'
  · intro l hl
    have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hP (Nat.mem_divisors.mp hl).1
    have hphi : 0 < (Nat.totient l : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0)
    exact le_of_lt (one_div_pos.mpr hphi)
  · refine ⟨1, Nat.mem_divisors.mpr ⟨Nat.one_dvd P, hP⟩, ?_⟩
    simp only [Nat.totient_one, Nat.cast_one]
    norm_num only

/--
Inputs: a squarefree sieve product `P`, its reciprocal totient sum `G`, and
`G ≠ 0`.

Claim: the inverse Möbius weight of `selbergOptimalDiagonal G` has value one at
the integer one.

Proof: expand the inverse weight at one, use the Möbius-square identity on each
divisor of `P`, factor out `1 / G`, and apply the definition of `G`.

Role: provides the normalization hypothesis for the Selberg main-term lower
bound with an explicit candidate weight.
-/
theorem selbergOptimalDiagonal_inverseWeight_normalized {P : ℕ} (hP : Squarefree P) (G : ℝ)
    (hG : G = ∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ)) :
    selbergDiagonalInverseWeight P (selbergOptimalDiagonal G) 1 = 1 := by
  have hGpos := reciprocalTotientDivisorSum_pos hP.ne_zero
  rw [← hG] at hGpos
  have hG0 : G ≠ 0 := ne_of_gt hGpos
  classical
  unfold selbergDiagonalInverseWeight
  rw [Nat.cast_one, one_mul]
  simp only [Nat.one_dvd, ite_true, Nat.div_one]
  have hphi (l : ℕ) (hl : l ∈ P.divisors) : (Nat.totient l : ℝ) ≠ 0 := by
    have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hl).1
    exact ne_of_gt (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0))
  have hmu (l : ℕ) (hl : l ∈ P.divisors) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) l) ^ 2 = 1 := by
    have hmuZ : (ArithmeticFunction.moebius l) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hl).1 hP)
    change ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 = 1
    exact_mod_cast hmuZ
  have hterm (l : ℕ) (hl : l ∈ P.divisors) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l * selbergOptimalDiagonal G l =
      (1 / G) * (1 / (Nat.totient l : ℝ)) := by
    unfold selbergOptimalDiagonal
    rw [mul_div_assoc', ← sq, hmu l hl, one_div_mul_one_div_rev]
  calc
    _ = ∑ l ∈ P.divisors, (1 / G) * (1 / (Nat.totient l : ℝ)) := by
      apply Finset.sum_congr rfl
      intro l hl
      exact hterm l hl
    _ = (1 / G) * (∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ)) := by rw [← Finset.mul_sum]
    _ = (1 / G) * G := by rw [hG]
    _ = 1 := one_div_mul_cancel hG0

/--
Inputs: a squarefree sieve product `P`, a cutoff `z ≥ 1`, and the truncated
reciprocal totient sum `G`.

Claim: the inverse Möbius weight of `selbergTruncatedOptimalDiagonal z G` is
normalized at one.

Proof: reduce the value at one to a sum over cutoff divisors, use the
Möbius-square identity, and factor out `1 / G`.

Role: gives a normalized Selberg weight with support restricted by `z`.
-/
theorem selbergTruncatedOptimalDiagonal_inverseWeight_normalized {P z : ℕ} (hP : Squarefree P)
    (hz : 1 ≤ z) (G : ℝ) (hG : G = selbergTruncatedTotientSum P z) :
    selbergDiagonalInverseWeight P (selbergTruncatedOptimalDiagonal z G) 1 = 1 := by
  have hGpos := selbergTruncatedTotientSum_pos hP.ne_zero hz
  rw [← hG] at hGpos
  have hG0 : G ≠ 0 := ne_of_gt hGpos
  have hphi (l : ℕ) (hl : l ∈ P.divisors) : (Nat.totient l : ℝ) ≠ 0 := by
    have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hl).1
    exact ne_of_gt (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0))
  have hmu (l : ℕ) (hl : l ∈ P.divisors) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) l) ^ 2 = 1 := by
    have hmuZ : (ArithmeticFunction.moebius l) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hl).1 hP)
    change ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 = 1
    exact_mod_cast hmuZ
  have hterm (l : ℕ) (hl : l ∈ P.divisors) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l * selbergTruncatedOptimalDiagonal z G l =
      if l ≤ z then (1 / G) * (1 / (Nat.totient l : ℝ)) else 0 := by
    by_cases hcut : l ≤ z
    · simp only [selbergTruncatedOptimalDiagonal, hcut, ite_true]
      unfold selbergOptimalDiagonal
      rw [mul_div_assoc', ← sq, hmu l hl, one_div_mul_one_div_rev]
    · simp only [selbergTruncatedOptimalDiagonal, hcut, ite_false, mul_zero]
  calc
    _ =
        ∑ l ∈ P.divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l *
            selbergTruncatedOptimalDiagonal z G l :=
      by
      unfold selbergDiagonalInverseWeight
      rw [Nat.cast_one, one_mul]
      simp only [Nat.one_dvd, ite_true, Nat.div_one]
    _ = ∑ l ∈ P.divisors, if l ≤ z then (1 / G) * (1 / (Nat.totient l : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      exact hterm l hl
    _ = (1 / G) * G := by
      calc
        _ = ∑ l ∈ P.divisors, (1 / G) * (if l ≤ z then 1 / (Nat.totient l : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro l hl
          by_cases hcut : l ≤ z
          · simp only [hcut, ite_true]
          · simp only [hcut, ite_false, mul_zero]
        _ = (1 / G) * G := by
          rw [← Finset.mul_sum]
          change (1 / G) * selbergTruncatedTotientSum P z = (1 / G) * G
          rw [hG.symm]
    _ = 1 := one_div_mul_cancel hG0

/--
Inputs: a squarefree sieve product `P`, a cutoff `z ≥ 1`, and the truncated
reciprocal totient sum `G`.

Claim: the inverse weight of `selbergTruncatedOptimalDiagonal z G` attains the
Λ² main-term value `1 / G`.

Proof: use the exact inverse-weight main-sum formula and the Möbius-square
identity below the cutoff; all diagonal coordinates above it vanish.

Role: provides a cutoff-compatible main-term optimizer for the sieve bound.
-/
theorem progressionBoundingSieve_truncatedOptimal_mainSum_eq {Y Q a P z : ℕ} (hP : Squarefree P)
    (hz : 1 ≤ z) (G : ℝ) (hG : G = selbergTruncatedTotientSum P z) :
    (progressionBoundingSieve Y Q a P hP).mainSum
        (BoundingSieve.lambdaSquared
          (selbergDiagonalInverseWeight P (selbergTruncatedOptimalDiagonal z G))) =
      1 / G := by
  have hGpos := selbergTruncatedTotientSum_pos hP.ne_zero hz
  rw [← hG] at hGpos
  have hG0 : G ≠ 0 := ne_of_gt hGpos
  have hphi (l : ℕ) (hl : l ∈ P.divisors) : (Nat.totient l : ℝ) ≠ 0 := by
    have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hl).1
    exact ne_of_gt (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0))
  have hmu (l : ℕ) (hl : l ∈ P.divisors) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) l) ^ 2 = 1 := by
    have hmuZ : (ArithmeticFunction.moebius l) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hl).1 hP)
    change ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 = 1
    exact_mod_cast hmuZ
  have hterm (l : ℕ) (hl : l ∈ P.divisors) :
    (Nat.totient l : ℝ) * (selbergTruncatedOptimalDiagonal z G l) ^ 2 =
      if l ≤ z then (1 / G ^ 2) * (1 / (Nat.totient l : ℝ)) else 0 := by
    by_cases hcut : l ≤ z
    · simp only [selbergTruncatedOptimalDiagonal, hcut, ite_true]
      unfold selbergOptimalDiagonal
      field_simp [hphi l hl, hG0]
      nlinarith only [hmu l hl]
    · simp only [selbergTruncatedOptimalDiagonal, hcut, ite_false]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num only]
      exact mul_zero (Nat.totient l : ℝ)
  rw [progressionBoundingSieve_lambdaSquared_mainSum_inverseWeight_eq]
  calc
    _ = ∑ l ∈ P.divisors, if l ≤ z then (1 / G ^ 2) * (1 / (Nat.totient l : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      exact hterm l hl
    _ = (1 / G ^ 2) * G := by
      calc
        _ = ∑ l ∈ P.divisors, (1 / G ^ 2) * (if l ≤ z then 1 / (Nat.totient l : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro l hl
          by_cases hcut : l ≤ z
          · simp only [hcut, ite_true]
          · simp only [hcut, ite_false, mul_zero]
        _ = (1 / G ^ 2) * G := by
          rw [← Finset.mul_sum]
          change (1 / G ^ 2) * selbergTruncatedTotientSum P z = (1 / G ^ 2) * G
          rw [hG.symm]
    _ = 1 / G := by field_simp [hG0]

/--
Inputs: a divisor cutoff `z`, a divisor candidate `d`, and `z < d`.

Claim: the inverse Möbius weight of the truncated optimal diagonal is zero at
`d`.

Proof: every multiple of `d` in the divisor sum exceeds the cutoff, so its
truncated diagonal coordinate vanishes.

Role: proves that the explicit main-term optimizer is supported on divisors
no larger than the cutoff.
-/
theorem selbergTruncatedOptimalWeight_eq_zero_of_gt {P z d : ℕ} (G : ℝ) (hdz : z < d) :
    selbergDiagonalInverseWeight P (selbergTruncatedOptimalDiagonal z G) d = 0 := by
  classical
  unfold selbergDiagonalInverseWeight
  have hterm (k : ℕ) (hk : k ∈ P.divisors) :
    (if d ∣ k then
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) *
          selbergTruncatedOptimalDiagonal z G k
      else 0) =
      0 := by
    by_cases hdk : d ∣ k
    · have hdkle : d ≤ k := Nat.le_of_dvd (Nat.pos_of_mem_divisors hk) hdk
      have hkbig : z < k := lt_of_lt_of_le hdz hdkle
      simp only [hdk, ite_true, selbergTruncatedOptimalDiagonal, not_le_of_gt hkbig, ite_false,
        mul_zero]
    · simp only [hdk, ite_false]
  calc
    _ = (d : ℝ) * 0 := by
      congr 1
      exact Finset.sum_eq_zero fun k hk => hterm k hk
    _ = 0 := mul_zero _

/--
Inputs: a squarefree sieve product, a cutoff `z ≥ 1`, the truncated
reciprocal totient normalizer `G`, and an index `d`.

Claim: the absolute value of the truncated optimal weight at `d` is at most
`d`.

Proof: bound every Möbius factor by one, then use the defining sum for `G` to
control the normalized reciprocal-totient sum.

Role: gives a first explicit estimate for the weight error in the progression
prime-count bound.
-/
theorem selbergTruncatedOptimalWeight_abs_le {P z d : ℕ} (hP : Squarefree P) (hz : 1 ≤ z) (G : ℝ)
    (hG : G = selbergTruncatedTotientSum P z) :
    |selbergTruncatedOptimalWeight P z G d| ≤ (d : ℝ) := by
  classical
  have hGpos := selbergTruncatedTotientSum_pos hP.ne_zero hz
  rw [← hG] at hGpos
  have hG0 : G ≠ 0 := ne_of_gt hGpos
  have hphi (k : ℕ) (hk : k ∈ P.divisors) : 0 < (Nat.totient k : ℝ) := by
    have hk0 : k ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hk).1
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hmu (n : ℕ) : |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) n| ≤ 1 := by
    have hmuZ : |ArithmeticFunction.moebius n| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
    change |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1
    exact_mod_cast hmuZ
  have hterm (k : ℕ) (hk : k ∈ P.divisors) :
    |if d ∣ k then
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) *
            selbergTruncatedOptimalDiagonal z G k
        else 0| ≤
      if k ≤ z then 1 / ((Nat.totient k : ℝ) * G) else 0 := by
    by_cases hdk : d ∣ k
    · by_cases hkz : k ≤ z
      · simp only [hdk, ite_true, selbergTruncatedOptimalDiagonal, hkz, ite_true]
        unfold selbergOptimalDiagonal
        have hden : 0 < (Nat.totient k : ℝ) * G := mul_pos (hphi k hk) hGpos
        rw [abs_mul, abs_div, abs_of_pos hden]
        calc
          |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d)| *
                (|(ArithmeticFunction.moebius : ArithmeticFunction ℝ) k| /
                  ((Nat.totient k : ℝ) * G)) ≤
              1 * (1 / ((Nat.totient k : ℝ) * G)) :=
            by
            calc
              _ ≤
                  1 *
                    (|(ArithmeticFunction.moebius : ArithmeticFunction ℝ) k| /
                      ((Nat.totient k : ℝ) * G)) :=
                mul_le_mul_of_nonneg_right (hmu (k / d)) (div_nonneg (abs_nonneg _) (le_of_lt hden))
              _ ≤ 1 * (1 / ((Nat.totient k : ℝ) * G)) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hmu k) (le_of_lt hden))
                  (by norm_num only)
          _ = 1 / ((Nat.totient k : ℝ) * G) := one_mul _
      · simp only [hdk, ite_true, selbergTruncatedOptimalDiagonal, hkz, ite_false, mul_zero,
          abs_zero]
        norm_num only
    · by_cases hkz : k ≤ z
      · simp only [hdk, ite_false, hkz, ite_true]
        simp only [abs_zero]
        exact div_nonneg (by norm_num only) (le_of_lt (mul_pos (hphi k hk) hGpos))
      · simp only [hdk, ite_false, hkz, ite_false]
        norm_num only
  unfold selbergTruncatedOptimalWeight selbergDiagonalInverseWeight
  have hnormalized :
    (∑ k ∈ P.divisors, if k ≤ z then 1 / ((Nat.totient k : ℝ) * G) else 0) = 1 := by
    calc
      _ = (1 / G) * G := by
        calc
          _ = ∑ k ∈ P.divisors, (1 / G) * (if k ≤ z then 1 / (Nat.totient k : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hkz : k ≤ z
            · simp only [hkz, ite_true]
              field_simp [hG0, ne_of_gt (hphi k hk)]
            · simp only [hkz, ite_false, mul_zero]
          _ = (1 / G) * selbergTruncatedTotientSum P z := by
            rw [← Finset.mul_sum]
            rfl
          _ = (1 / G) * G := by rw [hG]
      _ = 1 := one_div_mul_cancel hG0
  have hsumabs :
    |∑ k ∈ P.divisors,
          if d ∣ k then
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) *
              selbergTruncatedOptimalDiagonal z G k
          else 0| ≤
      1 := by
    calc
      _ ≤
          ∑ k ∈ P.divisors,
            |if d ∣ k then
                (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) *
                  selbergTruncatedOptimalDiagonal z G k
              else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ P.divisors, if k ≤ z then 1 / ((Nat.totient k : ℝ) * G) else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = 1 := hnormalized
  calc
    _ =
        (d : ℝ) *
          |∑ k ∈ P.divisors,
              if d ∣ k then
                (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) *
                  selbergTruncatedOptimalDiagonal z G k
              else 0| :=
      by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
    _ ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left hsumabs (Nat.cast_nonneg d)
    _ = (d : ℝ) := by rw [mul_one]

/--
Inputs: a squarefree sieve product `P`, cutoff `z ≥ 1`, normalizer `G`, and
an integer `d`.

Claim: the absolute truncated optimal weight at `d` is bounded by `d` times
the normalized reciprocal-totient mass on multiples of `d` below the cutoff.

Proof: bound each Möbius factor by one, use positivity of `φ(k) G`, and apply
the triangle inequality before summing over divisor multiples.

Role: retains the divisor structure of each coefficient so later estimates can
sum the weights by first grouping on the multiple `k`.
-/
theorem selbergTruncatedOptimalWeight_abs_le_divisor_mass {P z d : ℕ} (hP : Squarefree P)
    (hz : 1 ≤ z) (G : ℝ) (hG : G = selbergTruncatedTotientSum P z) :
    |selbergTruncatedOptimalWeight P z G d| ≤
      (d : ℝ) * ∑ k ∈ P.divisors, if d ∣ k ∧ k ≤ z then 1 / ((Nat.totient k : ℝ) * G) else 0 := by
  classical
  have hGpos := selbergTruncatedTotientSum_pos hP.ne_zero hz
  rw [← hG] at hGpos
  have hphi (k : ℕ) (hk : k ∈ P.divisors) : 0 < (Nat.totient k : ℝ) := by
    have hk0 : k ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hk).1
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hmu (n : ℕ) : |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) n| ≤ 1 := by
    have hmuZ : |ArithmeticFunction.moebius n| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
    change |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1
    exact_mod_cast hmuZ
  have hterm (k : ℕ) (hk : k ∈ P.divisors) :
    |if d ∣ k then
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) *
            selbergTruncatedOptimalDiagonal z G k
        else 0| ≤
      if d ∣ k ∧ k ≤ z then 1 / ((Nat.totient k : ℝ) * G) else 0 := by
    by_cases hdk : d ∣ k
    · by_cases hkz : k ≤ z
      · simp only [hdk, ite_true, selbergTruncatedOptimalDiagonal, hkz, ite_true, and_self,
          ite_true]
        unfold selbergOptimalDiagonal
        have hden : 0 < (Nat.totient k : ℝ) * G := mul_pos (hphi k hk) hGpos
        rw [abs_mul, abs_div, abs_of_pos hden]
        calc
          |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d)| *
                (|(ArithmeticFunction.moebius : ArithmeticFunction ℝ) k| /
                  ((Nat.totient k : ℝ) * G)) ≤
              1 * (1 / ((Nat.totient k : ℝ) * G)) :=
            by
            apply mul_le_mul (hmu (k / d)) (div_le_div_of_nonneg_right (hmu k) (le_of_lt hden))
            · exact div_nonneg (abs_nonneg _) (le_of_lt hden)
            · norm_num only
          _ = 1 / ((Nat.totient k : ℝ) * G) := by rw [one_mul]
      · simp only [hdk, ite_true, selbergTruncatedOptimalDiagonal, hkz, ite_false, mul_zero,
          abs_zero, and_false, ite_false]
        norm_num only
    · by_cases hkz : k ≤ z
      · simp only [hdk, hkz, false_and, ite_false, abs_zero]
        norm_num only
      · simp only [hdk, hkz, false_and, ite_false, abs_zero]
        norm_num only
  unfold selbergTruncatedOptimalWeight selbergDiagonalInverseWeight
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  calc
    (d : ℝ) *
          |∑ k ∈ P.divisors,
              if d ∣ k then
                (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) *
                  selbergTruncatedOptimalDiagonal z G k
              else 0| ≤
        (d : ℝ) *
          ∑ k ∈ P.divisors,
            |if d ∣ k then
                (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (k / d) *
                  selbergTruncatedOptimalDiagonal z G k
              else 0| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg d)
    _ ≤ (d : ℝ) * ∑ k ∈ P.divisors, if d ∣ k ∧ k ≤ z then 1 / ((Nat.totient k : ℝ) * G) else 0 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      exact Finset.sum_le_sum fun k hk => hterm k hk

/-!
The divisor-mass expression groups the absolute-weight estimate by the
multiple `k`; for a primorial sieve product, its inner sum is a truncated sum
of divisors of `k`.
-/

/--
Inputs: a sieve product `P`, cutoff `z`, and positive normalizer `G`.

Definition: sum over `k ∣ P` and `d ∣ P` of `d / (φ(k) G)`, retaining only
the pairs with `d ∣ k` and `k ≤ z`.

Output: an explicit finite upper-bound expression for the total absolute
truncated optimal weight.

Role: separates the Selberg weight error from the main-term optimization so
the divisor sum can be bounded arithmetically.
-/
noncomputable def selbergTruncatedOptimalWeightDivisorMass (P z : ℕ) (G : ℝ) : ℝ :=
  ∑ k ∈ P.divisors,
    ∑ d ∈ P.divisors, if d ∣ k ∧ k ≤ z then (d : ℝ) / ((Nat.totient k : ℝ) * G) else 0

/-!
The following finite reindexing lemmas put this error expression in a form
that can be estimated using the divisor sum of each `k`.
-/

/--
Inputs: a nonzero natural `P` encoded by a divisor `k ∈ P.divisors`.

Claim: summing `d` over divisors of `P` that also divide `k` equals the sum
over all divisors of `k`.

Proof: show the filtered divisor sets agree, using transitivity of divisibility.

Role: removes the ambient sieve product from the inner divisor sum.
-/
theorem selbergTruncatedOptimalWeightDivisorSum_reindex {P k : ℕ} (hk : k ∈ P.divisors) :
    (∑ d ∈ P.divisors, if d ∣ k then (d : ℝ) else 0) = ∑ d ∈ k.divisors, (d : ℝ) := by
  classical
  have hkdiv := Nat.mem_divisors.mp hk
  have hk0 : k ≠ 0 := ne_zero_of_dvd_ne_zero hkdiv.2 hkdiv.1
  have hset : P.divisors.filter (fun d => d ∣ k) = k.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdkP, hP0⟩, hdk⟩
      exact ⟨hdk, hk0⟩
    · rintro ⟨hdk, hk0'⟩
      exact ⟨⟨Nat.dvd_trans hdk hkdiv.1, hkdiv.2⟩, hdk⟩
  rw [← Finset.sum_filter, hset]

/--
Inputs: a sieve product `P`, cutoff `z`, and normalizer `G`.

Claim: `selbergTruncatedOptimalWeightDivisorMass` is the sum, over divisors
`k ≤ z` of `P`, of the divisor sum of `k` divided by `φ(k) G`.

Proof: split on the cutoff, factor out the common denominator, and reindex the
inner sum with `selbergTruncatedOptimalWeightDivisorSum_reindex`.

Role: isolates the arithmetic sum that remains to be bounded quantitatively.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_eq_divisor_sum {P z : ℕ} (G : ℝ) :
    selbergTruncatedOptimalWeightDivisorMass P z G =
      ∑ k ∈ P.divisors,
        if k ≤ z then (∑ d ∈ k.divisors, (d : ℝ)) / ((Nat.totient k : ℝ) * G) else 0 := by
  classical
  unfold selbergTruncatedOptimalWeightDivisorMass
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkz : k ≤ z
  · simp only [hkz, and_true, ite_true]
    have hdiv := selbergTruncatedOptimalWeightDivisorSum_reindex hk
    calc
      (∑ d ∈ P.divisors, if d ∣ k then (d : ℝ) / ((Nat.totient k : ℝ) * G) else 0) =
          (∑ d ∈ P.divisors, (if d ∣ k then (d : ℝ) else 0) * (((Nat.totient k : ℝ) * G)⁻¹)) :=
        by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdk : d ∣ k
        · simp only [hdk, ite_true]
          rw [div_eq_mul_inv]
        · simp only [hdk, ite_false, zero_mul]
      _ = (∑ d ∈ P.divisors, if d ∣ k then (d : ℝ) else 0) * (((Nat.totient k : ℝ) * G)⁻¹) := by
        rw [Finset.sum_mul]
      _ = (∑ d ∈ k.divisors, (d : ℝ)) * (((Nat.totient k : ℝ) * G)⁻¹) := by rw [hdiv]
      _ = (∑ d ∈ k.divisors, (d : ℝ)) / ((Nat.totient k : ℝ) * G) := by rw [div_eq_mul_inv]
  · simp only [hkz, and_false, ite_false, Finset.sum_const_zero]

/--
Inputs: a squarefree sieve product `P`, cutoff `z ≥ 1`, and the truncated
reciprocal-totient normalizer `G`.

Claim: the sum of absolute optimal weights is bounded by a divisor sum grouped
by the multiple `k` occurring in the inverse Möbius formula.

Proof: apply the coefficient bound, distribute the factor `d` into its finite
sum, and exchange the two divisor sums.

Role: reduces the total weight error to an explicit sum involving
`∑_{d ∣ k} d / φ(k)`, which can be estimated separately from the main term.
-/
theorem selbergTruncatedOptimalWeight_abs_sum_le_reordered_divisor_mass {P z : ℕ}
    (hP : Squarefree P) (hz : 1 ≤ z) (G : ℝ) (hG : G = selbergTruncatedTotientSum P z) :
    (∑ d ∈ P.divisors, |selbergTruncatedOptimalWeight P z G d|) ≤
      selbergTruncatedOptimalWeightDivisorMass P z G := by
  have hsum :
    (∑ d ∈ P.divisors, |selbergTruncatedOptimalWeight P z G d|) ≤
      ∑ d ∈ P.divisors,
        (d : ℝ) * ∑ k ∈ P.divisors, if d ∣ k ∧ k ≤ z then 1 / ((Nat.totient k : ℝ) * G) else 0 := by
    apply Finset.sum_le_sum
    intro d hd
    exact selbergTruncatedOptimalWeight_abs_le_divisor_mass hP hz G hG
  calc
    _ ≤
        ∑ d ∈ P.divisors,
          (d : ℝ) * ∑ k ∈ P.divisors, if d ∣ k ∧ k ≤ z then 1 / ((Nat.totient k : ℝ) * G) else 0 :=
      hsum
    _ =
        ∑ d ∈ P.divisors,
          ∑ k ∈ P.divisors, if d ∣ k ∧ k ≤ z then (d : ℝ) / ((Nat.totient k : ℝ) * G) else 0 :=
      by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hcond : d ∣ k ∧ k ≤ z
      · simp only [hcond, and_self, ite_true]
        ring_nf
      · simp only [hcond, ite_false, mul_zero]
    _ =
        ∑ k ∈ P.divisors,
          ∑ d ∈ P.divisors, if d ∣ k ∧ k ≤ z then (d : ℝ) / ((Nat.totient k : ℝ) * G) else 0 :=
      by exact Finset.sum_comm

/--
Inputs: a squarefree sieve product `P`, a cutoff `z ≥ 1`, and the truncated
reciprocal totient sum `G`.

Claim: the sum of absolute values of the truncated optimal weights through
the cutoff is at most `z * (z + 1)`.

Proof: bound each coefficient by its index, restrict the divisor sum to the
cutoff range, and bound that finite sum by its cardinality times `z`.

Role: gives a direct quantitative estimate for the square error term in the
progression prime-count inequality.
-/
theorem selbergTruncatedOptimalWeight_cutoff_abs_sum_le {P z : ℕ} (hP : Squarefree P) (hz : 1 ≤ z)
    (G : ℝ) (hG : G = selbergTruncatedTotientSum P z) :
    (∑ d ∈ P.divisors, if d ≤ z then |selbergTruncatedOptimalWeight P z G d| else 0) ≤
      (z : ℝ) * (z + 1 : ℕ) := by
  classical
    calc
    _ ≤ ∑ d ∈ P.divisors, if d ≤ z then (d : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hdz : d ≤ z
      · simp only [hdz, ite_true]
        exact selbergTruncatedOptimalWeight_abs_le hP hz G hG
      · simp only [hdz, ite_false]
        norm_num only
    _ = ∑ d ∈ P.divisors.filter (fun d => d ≤ z), (d : ℝ) := by rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ Finset.range (z + 1), (d : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_filter] at hd
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hd.2)
      · intro d hd hnot
        exact Nat.cast_nonneg d
    _ ≤ (Finset.range (z + 1)).card • (z : ℝ) := by
      apply Finset.sum_le_card_nsmul
      intro d hd
      exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))
    _ = ((z + 1 : ℕ) : ℝ) * (z : ℝ) := by simp only [Finset.card_range, nsmul_eq_mul]
    _ = (z : ℝ) * (z + 1 : ℕ) := by rw [Nat.cast_add, Nat.cast_one, mul_comm]

/--
Inputs: a squarefree sieve product `P`, its reciprocal totient sum `G`, and
`G ≠ 0`.

Claim: the inverse weight of `selbergOptimalDiagonal G` attains the reciprocal
totient-sum lower bound for the Λ² main term.

Proof: rewrite the main sum using the exact inverse-weight formula. Clear the
positive totient and nonzero normalization denominators in each term, apply
the Möbius-square identity, then factor out `1 / G ^ 2` and cancel one factor
of `G`.

Role: proves equality in the finite Selberg quadratic optimization problem.
-/
theorem progressionBoundingSieve_lambdaSquared_mainSum_inverseWeight_attains_lower_bound
    {Y Q a P : ℕ} (hP : Squarefree P) (G : ℝ) (hG : G = ∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ)) :
    (progressionBoundingSieve Y Q a P hP).mainSum
        (BoundingSieve.lambdaSquared (selbergDiagonalInverseWeight P (selbergOptimalDiagonal G))) =
      1 / G := by
  have hGpos := reciprocalTotientDivisorSum_pos hP.ne_zero
  rw [← hG] at hGpos
  have hG0 : G ≠ 0 := ne_of_gt hGpos
  have hphi (l : ℕ) (hl : l ∈ P.divisors) : (Nat.totient l : ℝ) ≠ 0 := by
    have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hl).1
    exact ne_of_gt (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0))
  have hmu (l : ℕ) (hl : l ∈ P.divisors) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) l) ^ 2 = 1 := by
    have hmuZ : (ArithmeticFunction.moebius l) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hl).1 hP)
    change ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 = 1
    exact_mod_cast hmuZ
  have hterm (l : ℕ) (hl : l ∈ P.divisors) :
    (Nat.totient l : ℝ) * (selbergOptimalDiagonal G l) ^ 2 =
      (1 / G ^ 2) * (1 / (Nat.totient l : ℝ)) := by
    unfold selbergOptimalDiagonal
    field_simp [hphi l hl, hG0]
    nlinarith only [hmu l hl]
  rw [progressionBoundingSieve_lambdaSquared_mainSum_inverseWeight_eq]
  calc
    _ = ∑ l ∈ P.divisors, (1 / G ^ 2) * (1 / (Nat.totient l : ℝ)) := by
      apply Finset.sum_congr rfl
      intro l hl
      exact hterm l hl
    _ = (1 / G ^ 2) * G := by rw [← Finset.mul_sum, hG]
    _ = 1 / G := by field_simp [hG0]

/--
Inputs: a squarefree sieve product and a Λ² weight normalized by `w 1 = 1`.

Claim: the main sum is at least the reciprocal of the divisor sum
`∑_{l ∣ P} 1 / φ(l)`.

Proof: apply the weighted Cauchy inequality to the Möbius-normalized diagonal
variables and use that every divisor of a squarefree number is squarefree.

Role: identifies the optimal scale of the Selberg quadratic main term before
constructing weights with a matching upper bound.
-/
theorem progressionBoundingSieve_lambdaSquared_mainSum_lower_bound {Y Q a P : ℕ} (hP : Squarefree P)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    1 / (∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ)) ≤
      (progressionBoundingSieve Y Q a P hP).mainSum (BoundingSieve.lambdaSquared w) := by
  classical
  rw [progressionBoundingSieve_lambdaSquared_mainSum_totient_form]
  let y := fun l => ∑ d ∈ P.divisors, if l ∣ d then (1 / (d : ℝ)) * w d else 0
  have hnorm :
    (∑ l ∈ P.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l * y l) = 1 := by
    change
      (∑ l ∈ P.divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l *
            (∑ d ∈ P.divisors, if l ∣ d then (1 / (d : ℝ)) * w d else 0)) =
        1
    calc
      _ =
          ∑ l ∈ P.divisors,
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l *
              (∑ d ∈ P.divisors, if l ∣ d then w d / (d : ℝ) else 0) :=
        by
        apply Finset.sum_congr rfl
        intro l hl
        apply congrArg (fun z : ℝ => (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l * z)
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hld : l ∣ d
        · simp only [ite_eq_left hld]
          rw [one_div, div_eq_mul_inv, mul_comm]
        · simp only [ite_eq_right hld]
      _ = w 1 := selbergDiagonal_moebius_normalization P hP.ne_zero w
      _ = 1 := hw
  have hphi (l : ℕ) (hl : l ∈ P.divisors) : 0 < (Nat.totient l : ℝ) := by
    have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.mem_divisors.mp hl).1
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0)
  have hcs :=
    Finset.sq_sum_div_le_sum_sq_div P.divisors
      (fun l => (ArithmeticFunction.moebius : ArithmeticFunction ℝ) l * y l)
      (fun l hl => one_div_pos.mpr (hphi l hl))
  rw [hnorm] at hcs
  have hterms :
    (∑ l ∈ P.divisors,
        ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) l * y l) ^ 2 /
          (1 / (Nat.totient l : ℝ))) =
      ∑ l ∈ P.divisors, (Nat.totient l : ℝ) * y l ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    have hsqZ : (ArithmeticFunction.moebius l) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hl).1 hP)
    have hsq : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) l) ^ 2 = 1 := by
      change ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 = 1
      exact_mod_cast hsqZ
    rw [mul_pow, hsq, one_mul]
    calc
      y l ^ 2 / (1 / (Nat.totient l : ℝ)) = y l ^ 2 * (1 / (Nat.totient l : ℝ))⁻¹ := by
        rw [div_eq_mul_inv]
      _ = y l ^ 2 * (Nat.totient l : ℝ) := by rw [one_div, inv_inv]
      _ = (Nat.totient l : ℝ) * y l ^ 2 := mul_comm _ _
  change
    1 / (∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ)) ≤
      ∑ l ∈ P.divisors, (Nat.totient l : ℝ) * y l ^ 2
  calc
    1 / (∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ)) =
        1 ^ 2 / (∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ)) :=
      by rw [one_pow]
    _ ≤
        ∑ l ∈ P.divisors,
          ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) l * y l) ^ 2 /
            (1 / (Nat.totient l : ℝ)) :=
      hcs
    _ = ∑ l ∈ P.divisors, (Nat.totient l : ℝ) * y l ^ 2 := hterms

/--
Inputs: a squarefree sieve product `P` and its reciprocal totient sum `G`.

Claim: among normalized Λ² weights, the least possible main sum is exactly
`1 / G`, and the inverse Möbius weight attains it.

Proof: apply the general lower bound to every normalized weight, then use the
explicit normalized inverse weight for equality.

Role: closes the finite-dimensional main-term optimization needed by the
Brun–Titchmarsh sieve reduction.
-/
theorem progressionBoundingSieve_lambdaSquared_mainSum_minimum {Y Q a P : ℕ} (hP : Squarefree P)
    (G : ℝ) (hG : G = ∑ l ∈ P.divisors, 1 / (Nat.totient l : ℝ)) :
    (∀ w : ℕ → ℝ,
        w 1 = 1 →
          1 / G ≤ (progressionBoundingSieve Y Q a P hP).mainSum (BoundingSieve.lambdaSquared w)) ∧
      ∃ w : ℕ → ℝ,
        w 1 = 1 ∧
          (progressionBoundingSieve Y Q a P hP).mainSum (BoundingSieve.lambdaSquared w) =
            1 / G := by
  constructor
  · intro w hw
    have hmain :=
      progressionBoundingSieve_lambdaSquared_mainSum_lower_bound (Y := Y) (Q := Q) (a := a) hP w hw
    rw [← hG] at hmain
    exact hmain
  · refine ⟨selbergDiagonalInverseWeight P (selbergOptimalDiagonal G), ?_, ?_⟩
    · exact selbergOptimalDiagonal_inverseWeight_normalized hP G hG
    · exact progressionBoundingSieve_lambdaSquared_mainSum_inverseWeight_attains_lower_bound hP G hG

/--
Inputs: a `BoundingSieve` supported on the integers up to `Y` in the residue
class `a` modulo `Q`, with unit weights and a sieve product whose prime
divisors are at most `z`.

Claim: the prime count in the progression is at most the number of primes up
to `z` plus the sieve's sifted sum.

Proof: use the finite split at `z`; the sifted sum equals the number of
progression integers in the support coprime to the sieve product.

Role: supplies the finite counting interface for applying Selberg's upper
sieve to the AGP Brun–Titchmarsh input.
-/
theorem progressionPrimeCount_le_small_primes_add_sieve {Y Q a z : ℕ} (s : BoundingSieve)
    (hsupport : s.support = (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q))
    (hweights : ∀ n ∈ s.support, s.weights n = 1)
    (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ s.prodPrimes → p ≤ z) :
    primeCountInProgression Y Q a ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card + s.siftedSum := by
  have hbridge := primeCountInProgression_le_small_primes_add_coprime Y Q a s.prodPrimes z hPsmall
  let C := (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q ∧ Nat.Coprime s.prodPrimes n)
  have hC : C = s.support.filter (fun n => Nat.Coprime s.prodPrimes n) := by
    dsimp only [C]
    rw [Finset.filter_and, hsupport]
    ext n
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn, hcong⟩, ⟨_, hcop⟩⟩
      exact ⟨⟨hn, hcong⟩, hcop⟩
    · rintro ⟨⟨hn, hcong⟩, hcop⟩
      exact ⟨⟨hn, hcong⟩, ⟨hn, hcop⟩⟩
  have hcount : (C.card : ℝ) = s.siftedSum := by
    rw [hC, ← Finset.sum_boole, BoundingSieve.siftedSum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hweights n hn]
  have hbridge' :
    (primeCountInProgression Y Q a : ℝ) ≤
      (((Finset.range (z + 1)).filter Nat.Prime).card : ℝ) + C.card := by
    exact_mod_cast hbridge
  rw [hcount] at hbridge'
  exact hbridge'

/--
Inputs: a squarefree sieve product whose prime divisors are at most `z`.

Claim: the progression prime count is bounded by the number of primes up to
`z` plus the sifted sum of the canonical progression sieve.

Proof: instantiate the generic finite reduction with
`progressionBoundingSieve`.

Role: removes the support and unit-weight bookkeeping from later applications
of the Selberg sieve.
-/
theorem progressionPrimeCount_le_small_primes_add_concrete_sieve {Y Q a z P : ℕ} (hP : Squarefree P)
    (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z) :
    primeCountInProgression Y Q a ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        (progressionBoundingSieve Y Q a P hP).siftedSum := by
  let s := progressionBoundingSieve Y Q a P hP
  have hsupport : s.support = (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q) := rfl
  have hweights : ∀ n ∈ s.support, s.weights n = 1 := by
    intro n hn
    rfl
  exact
    progressionPrimeCount_le_small_primes_add_sieve (Y := Y) (Q := Q) (a := a) (z := z) s hsupport
      hweights hPsmall

/--
Inputs: the progression sieve data above and upper Moebius coefficients for
the sieve.

Claim: the progression prime count is bounded by the small primes plus the
Selberg main term and its remainder sum.

Proof: combine the finite reduction with mathlib's upper Moebius sieve bound.

Role: isolates the exact quantitative estimates still needed to derive the
Brun–Titchmarsh input from the Selberg sieve.
-/
theorem progressionPrimeCount_le_small_primes_add_selberg_bound {Y Q a z : ℕ} (s : BoundingSieve)
    (muPlus : ℕ → ℝ) (hsupport : s.support = (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q))
    (hweights : ∀ n ∈ s.support, s.weights n = 1)
    (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ s.prodPrimes → p ≤ z)
    (hupper : BoundingSieve.IsUpperMoebius muPlus) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        (s.totalMass * s.mainSum muPlus + s.errSum muPlus) := by
  have hprime := progressionPrimeCount_le_small_primes_add_sieve s hsupport hweights hPsmall
  have hsieve := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius (s := s) muPlus hupper
  linarith only [hprime, hsieve]

/--
Inputs: a squarefree sieve product with prime divisors at most `z`, and upper
Moebius coefficients for the corresponding Selberg sieve.

Claim: the progression prime count is bounded by the small primes plus the
Selberg main term and remainder sum for the canonical progression sieve.

Proof: instantiate the general main-term estimate with
`progressionBoundingSieve`.

Role: this is the concrete finite endpoint to which divisor-counting and
Selberg-weight estimates can be connected in a proof of Brun–Titchmarsh.
-/
theorem progressionPrimeCount_le_small_primes_add_concrete_selberg_bound {Y Q a z P : ℕ}
    (hP : Squarefree P) (muPlus : ℕ → ℝ) (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z)
    (hupper : BoundingSieve.IsUpperMoebius muPlus) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass *
            (progressionBoundingSieve Y Q a P hP).mainSum muPlus +
          (progressionBoundingSieve Y Q a P hP).errSum muPlus) := by
  let s := progressionBoundingSieve Y Q a P hP
  have hsupport : s.support = (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q) := rfl
  have hweights : ∀ n ∈ s.support, s.weights n = 1 := by
    intro n hn
    rfl
  exact
    progressionPrimeCount_le_small_primes_add_selberg_bound (Y := Y) (Q := Q) (a := a) (z := z) s
      muPlus hsupport hweights hPsmall hupper

/--
Inputs: a squarefree sieve product coprime to the progression modulus, an
upper Moebius coefficient function, and a bound on its prime divisors.

Claim: the progression prime count is bounded by the small primes, the
Selberg main term, and the sum of absolute coefficients over product divisors.

Proof: combine the concrete Selberg bound with the divisor-wise remainder
estimate above.

Role: exposes the remaining finite coefficient estimate needed for the
Brun–Titchmarsh specialization.
-/
theorem progressionPrimeCount_le_concrete_selberg_coeff_sum {Y Q a z P : ℕ} (hP : Squarefree P)
    (hQ : 0 < Q) (hPQ : Nat.Coprime P Q) (muPlus : ℕ → ℝ)
    (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z)
    (hupper : BoundingSieve.IsUpperMoebius muPlus) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass *
            (progressionBoundingSieve Y Q a P hP).mainSum muPlus +
          ∑ d ∈ P.divisors, |muPlus d|) := by
  have hbase :=
    progressionPrimeCount_le_small_primes_add_concrete_selberg_bound (Y := Y) (Q := Q) (a := a)
      (z := z) (P := P) hP muPlus hPsmall hupper
  have herr :=
    progressionBoundingSieve_errSum_le_sum_abs (Y := Y) (Q := Q) (a := a) (P := P) hP hQ hPQ muPlus
  linarith only [hbase, herr]

/--
Inputs: a squarefree sieve product coprime to the progression modulus, a
weight function normalized at `1`, and a bound on the product's prime divisors.

Claim: the progression prime count is bounded using the Λ² main sum and a
finite double sum of absolute products of the input weights.

Proof: use `upperMoebius_lambdaSquared`, then bound each absolute Λ²
coefficient by its divisor double sum.

Role: reduces both Selberg terms to explicit expressions in the chosen weights.
-/
theorem progressionPrimeCount_le_concrete_selberg_lambdaSquared {Y Q a z P : ℕ} (hP : Squarefree P)
    (hQ : 0 < Q) (hPQ : Nat.Coprime P Q) (w : ℕ → ℝ) (hw : w 1 = 1)
    (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass *
            (progressionBoundingSieve Y Q a P hP).mainSum (BoundingSieve.lambdaSquared w) +
          ∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2|) := by
  have hbase :=
    progressionPrimeCount_le_concrete_selberg_coeff_sum (Y := Y) (Q := Q) (a := a) (z := z) (P := P)
      hP hQ hPQ (BoundingSieve.lambdaSquared w) hPsmall
      (BoundingSieve.upperMoebius_lambdaSquared w hw)
  have hcoeff :
    ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| ≤
      ∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
    apply Finset.sum_le_sum
    intro d hd
    exact lambdaSquared_abs_le_divisor_weight_sum w d
  linarith only [hbase, hcoeff]

/--
Inputs: a squarefree sieve product coprime to the progression modulus, a
weight function normalized at `1`, and a bound on the product's prime divisors.

Claim: the progression prime count is bounded by the small primes, the Λ²
main term, and the square of the absolute weight sum.

Proof: apply the Λ² upper-bound coefficients and the unique-lcm error estimate.

Role: isolates the quantitative weight sum that must be optimized with the
main term to obtain the Brun–Titchmarsh estimate.
-/
theorem progressionPrimeCount_le_concrete_selberg_lambdaSquared_square_error {Y Q a z P : ℕ}
    (hP : Squarefree P) (hQ : 0 < Q) (hPQ : Nat.Coprime P Q) (w : ℕ → ℝ) (hw : w 1 = 1)
    (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass *
            (progressionBoundingSieve Y Q a P hP).mainSum (BoundingSieve.lambdaSquared w) +
          (∑ d ∈ P.divisors, |w d|) ^ 2) := by
  have hbase :=
    progressionPrimeCount_le_concrete_selberg_coeff_sum (Y := Y) (Q := Q) (a := a) (z := z) (P := P)
      hP hQ hPQ (BoundingSieve.lambdaSquared w) hPsmall
      (BoundingSieve.upperMoebius_lambdaSquared w hw)
  have hcoeff := lambdaSquared_divisor_abs_sum_le_square P w
  linarith only [hbase, hcoeff]

/--
Inputs: a squarefree sieve product coprime to the progression modulus, a
cutoff `z ≥ 1`, and the truncated reciprocal totient sum `G`.

Claim: the progression prime count is bounded using the truncated optimal
Selberg weight, with its exact `1 / G` main term and a cutoff weight error.

Proof: instantiate the concrete Λ² square-error bound, use the normalization
and main-term identities, and remove the zero weights above the cutoff.

Role: exposes the quantitative error term needed for the Brun–Titchmarsh
estimate with the cutoff optimizer.
-/
theorem progressionPrimeCount_le_truncatedOptimal_selberg {Y Q a z P : ℕ} (hP : Squarefree P)
    (hQ : 0 < Q) (hPQ : Nat.Coprime P Q) (hz : 1 ≤ z) (G : ℝ)
    (hG : G = selbergTruncatedTotientSum P z) (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) +
          (∑ d ∈ P.divisors, if d ≤ z then |selbergTruncatedOptimalWeight P z G d| else 0) ^
            2) := by
  classical
  let w := selbergTruncatedOptimalWeight P z G
  have hnorm : w 1 = 1 := by
    change selbergDiagonalInverseWeight P (selbergTruncatedOptimalDiagonal z G) 1 = 1
    exact selbergTruncatedOptimalDiagonal_inverseWeight_normalized hP hz G hG
  have hmain :
    (progressionBoundingSieve Y Q a P hP).mainSum (BoundingSieve.lambdaSquared w) = 1 / G := by
    change
      (progressionBoundingSieve Y Q a P hP).mainSum
          (BoundingSieve.lambdaSquared
            (selbergDiagonalInverseWeight P (selbergTruncatedOptimalDiagonal z G))) =
        1 / G
    exact progressionBoundingSieve_truncatedOptimal_mainSum_eq hP hz G hG
  have hweight :
    (∑ d ∈ P.divisors, |w d|) =
      ∑ d ∈ P.divisors, if d ≤ z then |selbergTruncatedOptimalWeight P z G d| else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hcut : d ≤ z
    · change
        |selbergTruncatedOptimalWeight P z G d| =
          if d ≤ z then |selbergTruncatedOptimalWeight P z G d| else 0
      simp only [hcut, ite_true]
    · have hzero := selbergTruncatedOptimalWeight_eq_zero_of_gt (P := P) G (Nat.lt_of_not_ge hcut)
      change
        |selbergDiagonalInverseWeight P (selbergTruncatedOptimalDiagonal z G) d| =
          if d ≤ z then |selbergTruncatedOptimalWeight P z G d| else 0
      rw [hzero]
      simp only [hcut, ite_false, abs_zero]
  have hbound :=
    progressionPrimeCount_le_concrete_selberg_lambdaSquared_square_error (Y := Y) (Q := Q) (a := a)
      (z := z) (P := P) hP hQ hPQ w hnorm hPsmall
  rw [hmain, hweight] at hbound
  exact hbound

/--
Inputs: the hypotheses of `progressionPrimeCount_le_truncatedOptimal_selberg`.

Claim: the progression prime count is bounded by the small primes, the exact
truncated main term, and the square of `selbergTruncatedOptimalWeightDivisorMass`.

Proof: bound the cutoff weight sum by the divisor-mass expression, then use
monotonicity of squaring on nonnegative reals.

Role: exposes the divisor-grouped error estimate directly at the prime-count
interface for later arithmetic evaluation.
-/
theorem progressionPrimeCount_le_truncatedOptimal_selberg_divisor_mass_error {Y Q a z P : ℕ}
    (hP : Squarefree P) (hQ : 0 < Q) (hPQ : Nat.Coprime P Q) (hz : 1 ≤ z) (G : ℝ)
    (hG : G = selbergTruncatedTotientSum P z) (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) +
          (selbergTruncatedOptimalWeightDivisorMass P z G) ^ 2) := by
  classical
  let W := ∑ d ∈ P.divisors, if d ≤ z then |selbergTruncatedOptimalWeight P z G d| else 0
  let B := selbergTruncatedOptimalWeightDivisorMass P z G
  have hcut : W ≤ ∑ d ∈ P.divisors, |selbergTruncatedOptimalWeight P z G d| := by
    dsimp only [W]
    apply Finset.sum_le_sum
    intro d hd
    by_cases hdz : d ≤ z
    · simp only [hdz, ite_true]
      exact le_rfl
    · simp only [hdz, ite_false]
      exact abs_nonneg _
  have hweight : (∑ d ∈ P.divisors, |selbergTruncatedOptimalWeight P z G d|) ≤ B := by
    exact selbergTruncatedOptimalWeight_abs_sum_le_reordered_divisor_mass hP hz G hG
  have hWB : W ≤ B := le_trans hcut hweight
  have hWnonneg : 0 ≤ W := by
    dsimp only [W]
    apply Finset.sum_nonneg
    intro d hd
    by_cases hdz : d ≤ z
    · simp only [hdz, ite_true]
      exact abs_nonneg _
    · simp only [hdz, ite_false]
      norm_num only
  have hBnonneg : 0 ≤ B := le_trans hWnonneg hWB
  have hWsq : W ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hWnonneg hBnonneg).2 hWB
  have hbase :=
    progressionPrimeCount_le_truncatedOptimal_selberg (Y := Y) (Q := Q) (a := a) (z := z) (P := P)
      hP hQ hPQ hz G hG hPsmall
  change
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + W ^ 2) at hbase
  calc
    (primeCountInProgression Y Q a : ℝ) ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + W ^ 2) :=
      hbase
    _ ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + B ^ 2) :=
      by linarith only [hWsq]

/--
Inputs: the hypotheses of `progressionPrimeCount_le_truncatedOptimal_selberg`.

Claim: the progression prime count is bounded by the small primes, the exact
truncated main term, and the explicit error `(z * (z + 1)) ^ 2`.

Proof: apply the cutoff weight sum bound and monotonicity of squaring on
nonnegative reals to the finite Selberg count inequality.

Role: removes the weight function from the quantitative finite sieve bound.
-/
theorem progressionPrimeCount_le_truncatedOptimal_selberg_explicit_error {Y Q a z P : ℕ}
    (hP : Squarefree P) (hQ : 0 < Q) (hPQ : Nat.Coprime P Q) (hz : 1 ≤ z) (G : ℝ)
    (hG : G = selbergTruncatedTotientSum P z) (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) +
          ((z : ℝ) * (z + 1 : ℕ)) ^ 2) := by
  classical
  have hweight := selbergTruncatedOptimalWeight_cutoff_abs_sum_le hP hz G hG
  let S := ∑ d ∈ P.divisors, if d ≤ z then |selbergTruncatedOptimalWeight P z G d| else 0
  have hS : S ≤ (z : ℝ) * (z + 1 : ℕ) := by
    change (∑ d ∈ P.divisors, if d ≤ z then |selbergTruncatedOptimalWeight P z G d| else 0) ≤ _
    exact hweight
  have hSpos : 0 ≤ S := by
    dsimp only [S]
    apply Finset.sum_nonneg
    intro d hd
    by_cases hdz : d ≤ z
    · simp only [hdz, ite_true]
      exact abs_nonneg _
    · simp only [hdz, ite_false]
      norm_num only
  have hZpos : 0 ≤ (z : ℝ) * (z + 1 : ℕ) := mul_nonneg (Nat.cast_nonneg z) (Nat.cast_nonneg (z + 1))
  have hsquare : S ^ 2 ≤ ((z : ℝ) * (z + 1 : ℕ)) ^ 2 := (sq_le_sq₀ hSpos hZpos).2 hS
  have hbase :=
    progressionPrimeCount_le_truncatedOptimal_selberg (Y := Y) (Q := Q) (a := a) (z := z) (P := P)
      hP hQ hPQ hz G hG hPsmall
  change
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + S ^ 2) at hbase
  calc
    (primeCountInProgression Y Q a : ℝ) ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + S ^ 2) :=
      hbase
    _ ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) +
            ((z : ℝ) * (z + 1 : ℕ)) ^ 2) :=
      by
      apply add_le_add_right
      exact add_le_add_right hsquare _

end PseudoPrime.AnalyticNumberTheory.AGP
