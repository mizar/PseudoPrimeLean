/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
public import PseudoPrime.NumberTheory.PrimeProductSubgroupCounting
public import PseudoPrime.Data.Finset.FiniteCounting

/-! # ProgressionCounting

Finite progression and divisor-counting lemmas used by the AGP prime-supply argument.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

open PseudoPrime.Data.Finset in
/--
Inputs: finite sets of divisor labels `D` and parameter choices `K`, a bound
`x`, and a threshold `T`.

Claim: if the total number of pairs `(d, k)` for which `d * k + 1` is prime
and at most `x` exceeds `K.card * T`, then some `k ∈ K` has more than `T`
such divisors `d ∈ D`.

Content: the hypothesis counts good pairs first by `d`; the conclusion fixes
one `k` and counts its good `d` values.

Proof: exchange the two finite sums using `Finset.sum_comm`, then apply the
finite averaging lemma to the sum over `K`.

Role: this is the direct finite averaging step needed after the analytic
prime-pair total in paper95 Theorem 3.1 has been bounded below.
-/
theorem exists_k_with_many_prime_divisors (D K : Finset ℕ) (x T : ℕ)
    (h : K.card * T < ∑ d ∈ D, (K.filter (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x)).card) :
    ∃ k ∈ K, T < (D.filter (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x)).card := by
  classical
  have hswap :
    (∑ d ∈ D, (K.filter (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x)).card) =
      ∑ k ∈ K, (D.filter (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x)).card := by
    simp only [Finset.card_filter]
    exact
      Finset.sum_comm (s := D) (t := K) (f := fun d k =>
        if Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x then 1 else 0)
  rw [hswap] at h
  exact
    exists_index_with_value_gt_of_sum_gt_card_mul K
      (fun k => (D.filter (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x)).card) T h

/--
Purpose: count primes at most `x` in the residue class `a` modulo `D`.

Definition: filter the natural numbers from `0` through `x` by primality and
the congruence `n % D = a % D`, then take the finite-set cardinality.

Inputs: a natural-number bound `x`, a modulus `D`, and a residue representative
`a`.

Output: the number of primes in that finite arithmetic progression segment.

Role: this is the counting function used to state finite-range estimates for
the analytic input to the AGP prime-supply theorem.
-/
def primeCountInProgression (x D a : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n => Nat.Prime n ∧ n % D = a % D)).card

/--
Inputs: a progression bound `Y`, a modulus `Q`, a residue `a`, a sieve product
`P`, and a threshold `z` above every prime divisor of `P`.

Claim: the progression prime count is at most the number of primes up to `z`
plus the number of integers in the same progression up to `Y` that are
coprime to `P`.

Proof: split the progression primes at `z`. A prime above `z` cannot divide
`P`, so it is counted among the integers coprime to `P`.

Role: reduces an arithmetic progression prime bound to a sifted-set bound,
which can then be estimated by Selberg sieve inputs.
-/
theorem primeCountInProgression_le_small_primes_add_coprime (Y Q a P z : ℕ)
    (hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z) :
    primeCountInProgression Y Q a ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((Finset.range (Y + 1)).filter (fun n => n % Q = a % Q ∧ Nat.Coprime P n)).card := by
  classical
  let A := (Finset.range (Y + 1)).filter (fun n => Nat.Prime n ∧ n % Q = a % Q)
  let B := A.filter (fun n => n ≤ z)
  let C := (Finset.range (Y + 1)).filter (fun n => n % Q = a % Q ∧ Nat.Coprime P n)
  have hA : A.card = primeCountInProgression Y Q a := rfl
  have hsmall : B ⊆ (Finset.range (z + 1)).filter Nat.Prime := by
    intro n hn
    have hnB := (Finset.mem_filter.mp hn)
    have hnA := (Finset.mem_filter.mp hnB.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnA.2.1⟩
  have hlarge : A \ B ⊆ C := by
    intro n hn
    have hnDiff := Finset.mem_sdiff.mp hn
    have hnA := (Finset.mem_filter.mp hnDiff.1)
    have hnleY := Finset.mem_range.mp hnA.1
    have hnnotle : ¬n ≤ z := by
      intro hnle
      exact hnDiff.2 (Finset.mem_filter.mpr ⟨hnDiff.1, hnle⟩)
    have hnlarge : z < n := Nat.lt_of_not_ge hnnotle
    have hnotdvd : ¬n ∣ P := by
      intro hdiv
      exact (Nat.not_le_of_gt hnlarge) (hPsmall n hnA.2.1 hdiv)
    have hcop : Nat.Coprime P n := Nat.Coprime.symm (hnA.2.1.coprime_iff_not_dvd.mpr hnotdvd)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnleY, ⟨hnA.2.2, hcop⟩⟩
  rw [← hA]
  calc
    A.card ≤ (A \ B).card + B.card := Finset.card_le_card_sdiff_add_card
    _ ≤ C.card + ((Finset.range (z + 1)).filter Nat.Prime).card :=
      Nat.add_le_add (Finset.card_le_card hlarge) (Finset.card_le_card hsmall)
    _ = ((Finset.range (z + 1)).filter Nat.Prime).card + C.card := Nat.add_comm _ _

/--
Purpose: state the classical Brun–Titchmarsh estimate for prime counts in
arithmetic progressions.

Inputs: natural bounds `Y` and `Q` with `1 ≤ Q < Y`, and a residue coprime to
`Q`.

Claim: the count is at most `2 * Y / (φ(Q) * log(Y/Q))` for every such
progression.

Role: this analytic input is consumed by the AGP specialization. It names the
classical theorem and does not prove it.
-/
def AGPBrunTitchmarshInput : Prop :=
  ∀ (Y Q a : ℕ),
    1 ≤ Q →
      Q < Y →
      Nat.Coprime a Q →
      (primeCountInProgression Y Q a : ℝ) ≤
        2 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((Y : ℝ) / (Q : ℝ)))

/--
Purpose: construct the residue class used to combine `p ≡ 1 (mod d)` with
`p ≡ l (mod m)`.

Definition: take the natural representative supplied by the Chinese remainder
theorem for the residues `1` modulo `d` and `l` modulo `m`.

Inputs: coprime moduli `d` and `m`, a residue `l`, and the proof that `d` and
`m` are coprime.

Output: a natural number representing the combined residue modulo `d*m`.

Role: this is the residue class to which the arithmetic progression prime
estimate is applied in reliable, Proposition 1.5.
-/
def progressionCoprimeResidue (d m l : ℕ) (hdm : Nat.Coprime d m) : ℕ :=
  (Nat.chineseRemainder hdm 1 l).val

/--
Inputs: coprime moduli `d` and `m`, a residue `l`, and proofs that `d` is
coprime to `m` and `l` is coprime to `m`.

Claim: `progressionCoprimeResidue d m l hdm` is `1` modulo `d`, is `l` modulo
`m`, and is coprime to the product modulus `d*m`.

Content: the two congruences combine the divisor progression with the target
progression, while the coprimality makes the combined class admissible for a
prime-counting theorem in arithmetic progressions.

Proof: use the two components of `Nat.chineseRemainder`; coprimality with each
factor follows from invariance under reduction modulo that factor.

Role: this supplies the arithmetic progression data needed before applying
Brun–Titchmarsh to modulus `d*m`.
-/
theorem progressionCoprimeResidue_spec (d m l : ℕ) (hdm : Nat.Coprime d m) (hlm : Nat.Coprime l m) :
    progressionCoprimeResidue d m l hdm % d = 1 % d ∧
      progressionCoprimeResidue d m l hdm % m = l % m ∧
      Nat.Coprime (progressionCoprimeResidue d m l hdm) (d * m) := by
  have hmodD : progressionCoprimeResidue d m l hdm % d = 1 % d := by
    change (Nat.chineseRemainder hdm 1 l).val % d = 1 % d
    exact (Nat.chineseRemainder hdm 1 l).property.1
  have hmodM : progressionCoprimeResidue d m l hdm % m = l % m := by
    change (Nat.chineseRemainder hdm 1 l).val % m = l % m
    exact (Nat.chineseRemainder hdm 1 l).property.2
  have hcopD : (progressionCoprimeResidue d m l hdm).Coprime d := by
    apply (ZMod.coprime_mod_iff_coprime (progressionCoprimeResidue d m l hdm) d).1
    rw [hmodD]
    exact (ZMod.coprime_mod_iff_coprime 1 d).2 (Nat.coprime_one_left d)
  have hcopM : (progressionCoprimeResidue d m l hdm).Coprime m := by
    apply (ZMod.coprime_mod_iff_coprime (progressionCoprimeResidue d m l hdm) m).1
    rw [hmodM]
    exact (ZMod.coprime_mod_iff_coprime l m).2 hlm
  exact ⟨hmodD, hmodM, Nat.Coprime.mul_right hcopD hcopM⟩

/--
Inputs: coprime moduli `d` and `m`, residues `1` and `l`, and a prime
candidate `p`.

Claim: `p` lies in the combined residue class modulo `d*m` exactly when it is
`1` modulo `d` and `l` modulo `m`.

Content: this identifies the divisor progression and the target arithmetic
progression with the single class counted by `primeCountInProgression`.

Proof: apply the Chinese remainder characterization of congruence modulo a
product, then use the component residues of `progressionCoprimeResidue`.

Role: this is the finite residue-class bridge needed to apply a prime-counting
estimate modulo `d*m` in the proof of reliable, Proposition 1.5.
-/
theorem progressionCoprimeResidue_modEq_iff (d m l p : ℕ) (hdm : Nat.Coprime d m)
    (hlm : Nat.Coprime l m) :
    p ≡ progressionCoprimeResidue d m l hdm [MOD d * m] ↔ p ≡ 1 [MOD d] ∧ p ≡ l [MOD m] := by
  have hspec := progressionCoprimeResidue_spec d m l hdm hlm
  constructor
  · intro hp
    have hpParts := (Nat.modEq_and_modEq_iff_modEq_mul hdm).mpr hp
    constructor
    · change p % d = 1 % d
      calc
        p % d = progressionCoprimeResidue d m l hdm % d := hpParts.1
        _ = 1 % d := hspec.1
    · change p % m = l % m
      calc
        p % m = progressionCoprimeResidue d m l hdm % m := hpParts.2
        _ = l % m := hspec.2.1
  · rintro ⟨hpD, hpM⟩
    apply (Nat.modEq_and_modEq_iff_modEq_mul hdm).mp
    constructor
    · change p % d = progressionCoprimeResidue d m l hdm % d
      calc
        p % d = 1 % d := hpD
        _ = progressionCoprimeResidue d m l hdm % d := hspec.1.symm
    · change p % m = progressionCoprimeResidue d m l hdm % m
      calc
        p % m = l % m := hpM
        _ = progressionCoprimeResidue d m l hdm % m := hspec.2.1.symm

/--
Inputs: a natural number `p ≥ 2`, a positive divisor `d`, and the congruence
`p ≡ 1 (mod d)`.

Claim: there is a parameter `k ≤ p / d` such that `p = d*k+1`.

Content: this converts a prime in the residue class `1 mod d` to the linear
form counted over the parameter `k` in the AGP argument.

Proof: if `d = 1`, take `k = p-1`; otherwise Euclidean division and the
remainder condition give the representation with `k = p/d`.

Role: this is the integer reparameterization from the progression-prime count
to the divisor-indexed pair count in reliable, Proposition 1.5.
-/
theorem exists_factorization_of_residue_one (p d : ℕ) (hp : 2 ≤ p) (hd : 0 < d)
    (hmod : p % d = 1 % d) : ∃ k, p = d * k + 1 ∧ k ≤ p / d := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)) with hdEq | hdGt
  · have hdOne : d = 1 := hdEq.symm
    subst d
    refine ⟨p - 1, ?_, ?_⟩
    · simp only [one_mul]
      exact (Nat.sub_add_cancel (le_trans (by decide : 1 ≤ 2) hp)).symm
    · simpa only [Nat.div_one] using Nat.sub_le p 1
  · have hmodOne : p % d = 1 := by
      calc
        p % d = 1 % d := hmod
        _ = 1 := Nat.mod_eq_of_lt hdGt
    refine ⟨p / d, ?_, le_rfl⟩
    calc
      p = d * (p / d) + p % d := (Nat.div_add_mod p d).symm
      _ = d * (p / d) + 1 := by rw [hmodOne]

/--
Inputs: an upper bound `x`, coprime moduli `d` and `m`, and a residue `l`
coprime to `m`.

Claim: counting primes in the combined residue class modulo `d*m` is the same
as counting primes that are `1` modulo `d` and `l` modulo `m` separately.

Content: this rewrites the source's simultaneous congruence conditions as one
arithmetic progression count, without changing the finite range or primality
condition.

Proof: extensionality reduces equality of cardinalities to membership; apply
`progressionCoprimeResidue_modEq_iff` to the residue condition.

Role: this identifies the exact finite counting function needed when applying
an arithmetic-progression prime estimate with modulus `d*m`.
-/
theorem primeCountInProgression_eq_card_filter_crt (x d m l : ℕ) (hdm : Nat.Coprime d m)
    (hlm : Nat.Coprime l m) :
    primeCountInProgression x (d * m) (progressionCoprimeResidue d m l hdm) =
      ((Finset.range (x + 1)).filter
          (fun p => Nat.Prime p ∧ p % d = 1 % d ∧ p % m = l % m)).card := by
  unfold primeCountInProgression
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hrange, hprime, hmod⟩
    refine ⟨hrange, hprime, ?_⟩
    exact (progressionCoprimeResidue_modEq_iff d m l p hdm hlm).mp hmod
  · rintro ⟨hrange, hprime, hmodD, hmodM⟩
    refine ⟨hrange, hprime, ?_⟩
    exact (progressionCoprimeResidue_modEq_iff d m l p hdm hlm).mpr ⟨hmodD, hmodM⟩

/--
Inputs: a bound `x`, coprime moduli `d` and `m`, a residue `l` coprime to `m`,
and `0 < d`.

Claim: the prime count in the CRT progression equals the count of parameters
`k` for which `d * k + 1` is prime, at most `x`, and congruent to `l` modulo
`m`.

Content: this is the exact counting reformulation needed to compare the finite
prime supply with Proposition 1.5 of *On the difficulty of finding reliable
witnesses*.

Proof: map each admissible `k` to `d * k + 1`. The inverse uses Euclidean
division and the residue `1` modulo `d`; injectivity follows from `0 < d`.

Role: this connects the arithmetic-progression prime count to the parameter
count used in the AGP construction.
-/
theorem primeCountInProgression_eq_card_good_parameters (x d m l : ℕ) (hdm : Nat.Coprime d m)
    (hlm : Nat.Coprime l m) (hd : 0 < d) :
    primeCountInProgression x (d * m) (progressionCoprimeResidue d m l hdm) =
      ((Finset.range (x / d + 1)).filter
          (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)).card := by
  let P := (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % d = 1 % d ∧ p % m = l % m)
  let K :=
    (Finset.range (x / d + 1)).filter
      (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)
  have hImage : K.image (fun k => d * k + 1) = P := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
      have hk' := Finset.mem_filter.mp hk
      change
        d * k + 1 ∈
          (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % d = 1 % d ∧ p % m = l % m)
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le hk'.2.2.1, ?_⟩
      have hmodD : (d * k + 1) % d = 1 % d := by
        calc
          (d * k + 1) % d = ((d * k) % d + 1 % d) % d := Nat.add_mod _ _ _
          _ = (0 + 1 % d) % d := by rw [Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]
          _ = 1 % d := by rw [Nat.zero_add, Nat.mod_mod]
      exact ⟨hk'.2.1, hmodD, hk'.2.2.2⟩
    · intro hp
      change
        p ∈
          (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % d = 1 % d ∧ p % m = l % m) at hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨k, hfactor, hkbound⟩ :=
        exists_factorization_of_residue_one p d (Nat.Prime.two_le hp.2.1) hd hp.2.2.1
      have hkboundX : k ≤ x / d := le_trans hkbound (Nat.div_le_div_right (Nat.lt_succ_iff.mp hp.1))
      change p ∈ K.image (fun k => d * k + 1)
      apply Finset.mem_image.mpr
      refine ⟨k, ?_, hfactor.symm⟩
      change
        k ∈
          (Finset.range (x / d + 1)).filter
            (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le hkboundX, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [← hfactor]
        exact hp.2.1
      · refine ⟨?_, ?_⟩
        · rw [← hfactor]
          exact Nat.le_of_lt_succ hp.1
        · rw [← hfactor]
          exact hp.2.2.2
  have hInj : Set.InjOn (fun k => d * k + 1) (K : Set ℕ) := by
    intro k hk j hj hEq
    exact Nat.mul_left_cancel hd (Nat.add_right_cancel hEq)
  calc
    primeCountInProgression x (d * m) (progressionCoprimeResidue d m l hdm) = P.card := by
      rw [primeCountInProgression_eq_card_filter_crt x d m l hdm hlm]
    _ = (K.image (fun k => d * k + 1)).card := congrArg Finset.card hImage.symm
    _ = K.card := Finset.card_image_of_injOn hInj
    _ = _ := rfl

/--
Inputs: the progression count data, a positive divisor `d`, a parameter bound
`K`, and the cutoff `x ≤ d * K + 1`.

Claim: the progression count equals the good-parameter count restricted to
`k ≤ K`.

Content: the cutoff bounds every parameter in the progression by `K`, including
the case `d = 1`.

Proof: identify the image of the bounded parameter set with the CRT-filtered
prime set. Injectivity follows from `0 < d`.

Role: this exposes a bounded parameter range for the finite averaging used in
the AGP prime-supply argument.
-/
theorem primeCountInProgression_eq_card_good_parameters_of_cutoff (x d m l K : ℕ)
    (hdm : Nat.Coprime d m) (hlm : Nat.Coprime l m) (hd : 0 < d) (hcut : x ≤ d * K + 1) :
    primeCountInProgression x (d * m) (progressionCoprimeResidue d m l hdm) =
      ((Finset.range (K + 1)).filter
          (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)).card := by
  let P := (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % d = 1 % d ∧ p % m = l % m)
  let Kset :=
    (Finset.range (K + 1)).filter
      (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)
  have hImage : Kset.image (fun k => d * k + 1) = P := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
      have hk' := Finset.mem_filter.mp hk
      change
        d * k + 1 ∈
          (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % d = 1 % d ∧ p % m = l % m)
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le hk'.2.2.1, ?_⟩
      have hmodD : (d * k + 1) % d = 1 % d := by
        calc
          (d * k + 1) % d = ((d * k) % d + 1 % d) % d := Nat.add_mod _ _ _
          _ = (0 + 1 % d) % d := by rw [Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]
          _ = 1 % d := by rw [Nat.zero_add, Nat.mod_mod]
      exact ⟨hk'.2.1, hmodD, hk'.2.2.2⟩
    · intro hp
      change
        p ∈
          (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % d = 1 % d ∧ p % m = l % m) at hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨k, hfactor, hkbound⟩ :=
        exists_factorization_of_residue_one p d (Nat.Prime.two_le hp.2.1) hd hp.2.2.1
      have hkboundK : k ≤ K :=
        Nat.le_of_mul_le_mul_left
          (Nat.le_of_succ_le_succ
            (by
              calc
                d * k + 1 = p := hfactor.symm
                _ ≤ x := Nat.le_of_lt_succ hp.1
                _ ≤ d * K + 1 := hcut))
          hd
      change p ∈ Kset.image (fun k => d * k + 1)
      apply Finset.mem_image.mpr
      refine ⟨k, ?_, hfactor.symm⟩
      change
        k ∈
          (Finset.range (K + 1)).filter
            (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le hkboundK, ?_⟩
      rw [← hfactor]
      exact ⟨hp.2.1, Nat.le_of_lt_succ hp.1, hp.2.2.2⟩
  have hInj : Set.InjOn (fun k => d * k + 1) (Kset : Set ℕ) := by
    intro k hk j hj hEq
    exact Nat.mul_left_cancel hd (Nat.add_right_cancel hEq)
  calc
    primeCountInProgression x (d * m) (progressionCoprimeResidue d m l hdm) = P.card := by
      rw [primeCountInProgression_eq_card_filter_crt x d m l hdm hlm]
    _ = (Kset.image (fun k => d * k + 1)).card := congrArg Finset.card hImage.symm
    _ = Kset.card := Finset.card_image_of_injOn hInj
    _ = _ := rfl

/--
Inputs: a finite divisor set `D`, a prime cutoff `x d` for each divisor, a
parameter bound `K`, and coprime progression data.

Claim: summing the progression counts over `D.attach` equals the total number
of good divisor-parameter pairs with `k ≤ K`.

Content: each local cutoff satisfies `x d ≤ d*K+1`, so its progression count
has exactly the bounded parameter range. `D.attach` retains the membership
proofs needed to construct the CRT residue for each divisor.

Proof: apply `primeCountInProgression_eq_card_good_parameters_of_cutoff` at
each attached divisor, then remove the attachment on the parameter-count sum.

Role: this converts a family of arithmetic-progression estimates into the
finite pair count used by the averaging lemmas below.
-/
theorem sum_progression_counts_eq_good_parameter_pairs (D : Finset ℕ) (x : ℕ → ℕ) (K m l : ℕ)
    (hpos : ∀ d ∈ D, 0 < d) (hdm : ∀ d ∈ D, Nat.Coprime d m) (hlm : Nat.Coprime l m)
    (hcut : ∀ d ∈ D, x d ≤ d * K + 1) :
    (∑ d ∈ D.attach,
        primeCountInProgression (x d.val) (d.val * m)
          (progressionCoprimeResidue d.val m l (hdm d.val d.property))) =
      ∑ d ∈ D,
        ((Finset.range (K + 1)).filter
            (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x d ∧ (d * k + 1) % m = l % m)).card := by
  calc
    (∑ d ∈ D.attach,
          primeCountInProgression (x d.val) (d.val * m)
            (progressionCoprimeResidue d.val m l (hdm d.val d.property))) =
        ∑ d ∈ D.attach,
          ((Finset.range (K + 1)).filter
              (fun k =>
                Nat.Prime (d.val * k + 1) ∧
                  d.val * k + 1 ≤ x d.val ∧ (d.val * k + 1) % m = l % m)).card :=
      by
      apply Finset.sum_congr rfl
      intro d hdD
      exact
        primeCountInProgression_eq_card_good_parameters_of_cutoff (x d.val) d.val m l K
          (hdm d.val d.property) hlm (hpos d.val d.property) (hcut d.val d.property)
    _ = _ :=
      Finset.sum_attach D
        (fun d =>
          ((Finset.range (K + 1)).filter
              (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x d ∧ (d * k + 1) % m = l % m)).card)

/--
Purpose: count primes in the simultaneous residue classes `1 mod d` and `l
mod m` whose quotient parameter is coprime to `L`.

Definition: count `p ≤ x` satisfying `Nat.Prime p`, both congruences, and
`Nat.Coprime ((p - 1) / d) L`.

Inputs: the prime bound `x`, moduli `d` and `m`, residue `l`, and integer `L`.

Output: the finite count of primes whose associated parameter is coprime to
`L`.

Role: this represents the coprimality restriction used in reliable,
Proposition 1.5 before converting the progression count to a parameter count.
-/
def primeCountInProgressionWithCoprimeQuotient (x d m l L : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter
      (fun p => Nat.Prime p ∧ ((p % d = 1 % d) ∧ p % m = l % m) ∧ Nat.Coprime ((p - 1) / d) L)).card

/--
Inputs: the coprime-quotient progression count, coprime moduli `d,m`, and
`l` coprime to `m`.

Claim: the simultaneous residue conditions are exactly the CRT class modulo
`d*m`, with the quotient coprimality condition retained.

Proof: apply `progressionCoprimeResidue_modEq_iff` to the two congruences.

Role: this lets arithmetic-progression estimates be stated using one CRT
residue while retaining the source's restriction on the parameter.
-/
theorem primeCountInProgressionWithCoprimeQuotient_eq_crt_filter (x d m l L : ℕ)
    (hdm : Nat.Coprime d m) (hlm : Nat.Coprime l m) :
    primeCountInProgressionWithCoprimeQuotient x d m l L =
      ((Finset.range (x + 1)).filter
          (fun p =>
            Nat.Prime p ∧
              p % (d * m) = progressionCoprimeResidue d m l hdm % (d * m) ∧
              Nat.Coprime ((p - 1) / d) L)).card := by
  unfold primeCountInProgressionWithCoprimeQuotient
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hrange, hprime, hmods, hcop⟩
    refine ⟨hrange, hprime, ?_, hcop⟩
    exact (progressionCoprimeResidue_modEq_iff d m l p hdm hlm).mpr hmods
  · rintro ⟨hrange, hprime, hmod, hcop⟩
    refine ⟨hrange, hprime, ?_, hcop⟩
    exact (progressionCoprimeResidue_modEq_iff d m l p hdm hlm).mp hmod

/--
Inputs: the coprime-quotient progression count, a positive divisor `d`, and
the cutoff `x ≤ d*K+1`.

Claim: this count equals the number of good parameters `k ≤ K` with
`Nat.Coprime k L`.

Content: the quotient `(p - 1) / d` is exactly the unique `k` in
`p = d*k+1`; the cutoff bounds that parameter by `K`.

Proof: identify the image of the filtered parameter set with the filtered
prime set. The map `k ↦ d*k+1` is injective since `d > 0`.

Role: this preserves the coprimality condition required by the AGP
Carmichael-number construction.
-/
theorem primeCountInProgressionWithCoprimeQuotient_eq_card_good_parameters (x d m l L K : ℕ)
    (hd : 0 < d) (hcut : x ≤ d * K + 1) :
    primeCountInProgressionWithCoprimeQuotient x d m l L =
      ((Finset.range (K + 1)).filter
          (fun k =>
            Nat.Prime (d * k + 1) ∧
              (d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m) ∧ Nat.Coprime k L)).card := by
  let P :=
    (Finset.range (x + 1)).filter
      (fun p => Nat.Prime p ∧ ((p % d = 1 % d) ∧ p % m = l % m) ∧ Nat.Coprime ((p - 1) / d) L)
  let Kset :=
    (Finset.range (K + 1)).filter
      (fun k => Nat.Prime (d * k + 1) ∧ (d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m) ∧ Nat.Coprime k L)
  have hImage : Kset.image (fun k => d * k + 1) = P := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
      have hk' := Finset.mem_filter.mp hk
      change
        d * k + 1 ∈
          (Finset.range (x + 1)).filter
            (fun p => Nat.Prime p ∧ ((p % d = 1 % d) ∧ p % m = l % m) ∧ Nat.Coprime ((p - 1) / d) L)
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le hk'.2.2.1.1, ?_⟩
      have hmodD : (d * k + 1) % d = 1 % d := by
        calc
          (d * k + 1) % d = ((d * k) % d + 1 % d) % d := Nat.add_mod _ _ _
          _ = (0 + 1 % d) % d := by rw [Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]
          _ = 1 % d := by rw [Nat.zero_add, Nat.mod_mod]
      have hquot : (d * k + 1 - 1) / d = k := by
        rw [Nat.add_sub_cancel_right]
        exact Nat.mul_div_right k hd
      exact
        ⟨hk'.2.1, ⟨hmodD, hk'.2.2.1.2⟩, by
          rw [hquot]; exact hk'.2.2.2⟩
    · intro hp
      change
        p ∈
          (Finset.range (x + 1)).filter
            (fun p =>
              Nat.Prime p ∧ ((p % d = 1 % d) ∧ p % m = l % m) ∧ Nat.Coprime ((p - 1) / d) L) at hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨k, hfactor, _⟩ :=
        exists_factorization_of_residue_one p d (Nat.Prime.two_le hp.2.1) hd hp.2.2.1.1
      have hkboundK : k ≤ K :=
        Nat.le_of_mul_le_mul_left
          (Nat.le_of_succ_le_succ
            (by
              calc
                d * k + 1 = p := hfactor.symm
                _ ≤ x := Nat.le_of_lt_succ hp.1
                _ ≤ d * K + 1 := hcut))
          hd
      have hquot : (p - 1) / d = k := by
        rw [hfactor, Nat.add_sub_cancel_right]
        exact Nat.mul_div_right k hd
      change p ∈ Kset.image (fun k => d * k + 1)
      apply Finset.mem_image.mpr
      refine ⟨k, ?_, hfactor.symm⟩
      change
        k ∈
          (Finset.range (K + 1)).filter
            (fun k =>
              Nat.Prime (d * k + 1) ∧ (d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m) ∧ Nat.Coprime k L)
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le hkboundK, ?_⟩
      rw [← hfactor]
      refine ⟨hp.2.1, ⟨Nat.le_of_lt_succ hp.1, hp.2.2.1.2⟩, ?_⟩
      rw [← hquot]
      exact hp.2.2.2
  have hInj : Set.InjOn (fun k => d * k + 1) (Kset : Set ℕ) := by
    intro k hk j hj hEq
    exact Nat.mul_left_cancel hd (Nat.add_right_cancel hEq)
  calc
    primeCountInProgressionWithCoprimeQuotient x d m l L = P.card := rfl
    _ = (Kset.image (fun k => d * k + 1)).card := congrArg Finset.card hImage.symm
    _ = Kset.card := Finset.card_image_of_injOn hInj
    _ = _ := rfl

/--
Inputs: a finite divisor set, divisor-dependent prime cutoffs, a parameter
bound `K`, and a coprimality modulus `L`.

Claim: the sum of the corresponding coprime-quotient progression counts is
the total number of good pairs `(d,k)` with `k ≤ K` and `k` coprime to `L`.

Proof: apply the fixed-divisor parameter-count identity term by term and sum.

Role: this is the finite counting interface for the coprime-parameter
restriction used in reliable, Proposition 1.5.
-/
theorem sum_progression_counts_with_coprime_quotient_eq_good_pairs (D : Finset ℕ) (x : ℕ → ℕ)
    (K m l L : ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcut : ∀ d ∈ D, x d ≤ d * K + 1) :
    (∑ d ∈ D, primeCountInProgressionWithCoprimeQuotient (x d) d m l L) =
      ∑ d ∈ D,
        ((Finset.range (K + 1)).filter
            (fun k =>
              Nat.Prime (d * k + 1) ∧
                (d * k + 1 ≤ x d ∧ (d * k + 1) % m = l % m) ∧ Nat.Coprime k L)).card := by
  apply Finset.sum_congr rfl
  intro d hdD
  exact
    primeCountInProgressionWithCoprimeQuotient_eq_card_good_parameters (x d) d m l L K (hpos d hdD)
      (hcut d hdD)

/--
Purpose: select positive parameters at most `K` that are coprime to `L`.

Definition: filter `Finset.Icc 1 K` by `Nat.Coprime k L`.

Inputs: the coprimality modulus `L` and the parameter bound `K`.

Output: the finite set of admissible positive parameters.

Role: this is the parameter set used by the finite averaging step; positivity
ensures `k ↦ d*k+1` preserves cardinality.
-/
def positiveCoprimeParameters (L K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun k => Nat.Coprime k L)

/--
Inputs: a parameter `k`, a coprimality modulus `L`, and a bound `K`.

Claim: membership in `positiveCoprimeParameters L K` is equivalent to
`1 ≤ k`, `k ≤ K`, and `Nat.Coprime k L`.

Proof: unfold the filtered interval and its membership condition.

Role: this exposes the range and positivity assumptions needed by the
finite prime-set extraction lemmas.
-/
theorem mem_positiveCoprimeParameters {k L K : ℕ} :
    k ∈ positiveCoprimeParameters L K ↔ 1 ≤ k ∧ k ≤ K ∧ Nat.Coprime k L := by
  simp only [positiveCoprimeParameters, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hcop⟩
    exact ⟨hlo, hhi, hcop⟩
  · rintro ⟨hlo, hhi, hcop⟩
    exact ⟨⟨hlo, hhi⟩, hcop⟩

/--
Inputs: the bounded good-parameter count and a finite bound `K`.

Claim: filtering `k ≤ K` by primality and coprimality gives the same count as
filtering `positiveCoprimeParameters L K` by the prime and progression
conditions.

Content: the omitted parameter `k = 0` would give `d*k+1 = 1`, which is not
prime.

Proof: identify the two filtered sets by membership; all other conditions are
unchanged.

Role: this presents the progression count over a parameter set whose elements
are positive and coprime to `L`.
-/
theorem card_good_parameters_eq_positive_coprime_filter (x d m l L K : ℕ) :
    ((Finset.range (K + 1)).filter
          (fun k =>
            Nat.Prime (d * k + 1) ∧
              (d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m) ∧ Nat.Coprime k L)).card =
      ((positiveCoprimeParameters L K).filter
          (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = l % m)).card := by
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, positiveCoprimeParameters, Finset.mem_Icc]
  constructor
  · rintro ⟨hkRange, hprime, hdata, hcop⟩
    have hkpos : 0 < k := by
      by_contra hnot
      have hk0 := Nat.eq_zero_of_not_pos hnot
      have hprimeOne := hprime
      rw [hk0] at hprimeOne
      have hprime1 : Nat.Prime 1 := by simpa only [Nat.mul_zero, Nat.zero_add] using hprimeOne
      exact Nat.not_prime_one hprime1
    exact
      ⟨⟨⟨Nat.succ_le_iff.mpr hkpos, Nat.lt_succ_iff.mp hkRange⟩, hcop⟩, hprime, hdata.1, hdata.2⟩
  · rintro ⟨⟨⟨hlo, hhi⟩, hcop⟩, hprime, hbound, hmod⟩
    exact ⟨Nat.lt_succ_of_le hhi, hprime, ⟨hbound, hmod⟩, hcop⟩

/--
Inputs: divisor-dependent prime cutoffs, a parameter bound, and the coprimality
modulus `L`.

Claim: the sum of coprime-quotient progression counts equals the total good
pair count over `positiveCoprimeParameters L K`.

Proof: use the bounded parameter identity at each divisor, then remove the
zero parameter, which cannot produce a prime.

Role: this gives the positive parameter set required by finite averaging and
preserves the coprimality condition from reliable, Proposition 1.5.
-/
theorem sum_progression_counts_with_coprime_quotient_eq_positive_good_pairs (D : Finset ℕ)
    (x : ℕ → ℕ) (K m l L : ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcut : ∀ d ∈ D, x d ≤ d * K + 1) :
    (∑ d ∈ D, primeCountInProgressionWithCoprimeQuotient (x d) d m l L) =
      ∑ d ∈ D,
        ((positiveCoprimeParameters L K).filter
            (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x d ∧ (d * k + 1) % m = l % m)).card := by
  rw [sum_progression_counts_with_coprime_quotient_eq_good_pairs D x K m l L hpos hcut]
  apply Finset.sum_congr rfl
  intro d hdD
  exact card_good_parameters_eq_positive_coprime_filter (x d) d m l L K

/--
Inputs: a bound `x`, a modulus `D`, and a residue representative `a`.

Claim: the number of primes at most `x` in one residue class modulo `D` is at
most `x / D + 1`.

Content: this elementary bound counts all integers in the class, without using
primality or a sieve estimate.

Proof: map each counted integer to its quotient by `D`. Equal quotients and the
fixed residue imply equal integers by Euclidean division, so this map is
injective into `range (x / D + 1)`.

Role: this supplies a finite counting baseline for the stronger analytic
arithmetic-progression estimate required by P3.
-/
theorem primeCountInProgression_le (x D a : ℕ) : primeCountInProgression x D a ≤ x / D + 1 := by
  classical
  unfold primeCountInProgression
  calc
    ((Finset.range (x + 1)).filter (fun n => Nat.Prime n ∧ n % D = a % D)).card ≤
        (Finset.range (x / D + 1)).card :=
      by
      apply
        Finset.card_le_card_of_injOn (s :=
          (Finset.range (x + 1)).filter (fun n => Nat.Prime n ∧ n % D = a % D)) (t :=
          Finset.range (x / D + 1)) (fun n => n / D)
      · intro n hn
        have hnmem : n ∈ (Finset.range (x + 1)).filter (fun n => Nat.Prime n ∧ n % D = a % D) :=
          Finset.mem_coe.mp hn
        simp only [Finset.mem_filter, Finset.mem_range] at hnmem
        change (n / D) ∈ (Finset.range (x / D + 1) : Set ℕ)
        simp only [Finset.mem_coe, Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.mp hnmem.1))
      · intro n hn m hm hdiv
        have hnmem : n ∈ (Finset.range (x + 1)).filter (fun n => Nat.Prime n ∧ n % D = a % D) :=
          Finset.mem_coe.mp hn
        have hmmem : m ∈ (Finset.range (x + 1)).filter (fun n => Nat.Prime n ∧ n % D = a % D) :=
          Finset.mem_coe.mp hm
        simp only [Finset.mem_filter] at hnmem hmmem
        have hmod : n % D = m % D := hnmem.2.2.trans hmmem.2.2.symm
        change n / D = m / D at hdiv
        calc
          n = D * (n / D) + n % D := (Nat.div_add_mod n D).symm
          _ = D * (m / D) + m % D := by rw [hdiv, hmod]
          _ = m := Nat.div_add_mod m D
    _ = x / D + 1 := Finset.card_range _

/--
Inputs: a finite set `P` of natural numbers, a bound `x`, a modulus `D`, and a
residue representative `a`.

Claim: if every member of `P` is a prime at most `x` in the residue class `a`
modulo `D`, then `P.card` is at most `primeCountInProgression x D a`.

Content: this compares a finite set supplied by an analytic argument with the
canonical finite count used in this module.

Proof: show that `P` is a subset of the filtered range defining the count, then
apply monotonicity of finite-set cardinality.

Role: this transfers divisor-indexed prime counts from the source papers to
the finite progression count and its analytic upper bounds.
-/
theorem card_le_primeCountInProgression (x D a : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % D = a % D) :
    P.card ≤ primeCountInProgression x D a := by
  classical
  unfold primeCountInProgression
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.lt_succ_of_le (hP p hp).2.1, ?_⟩
  exact ⟨(hP p hp).1, (hP p hp).2.2⟩

/--
Inputs: a finite set `P` of primes in one residue class, together with an
integer bound `x` and modulus `D`.

Claim: `P.card ≤ x / D + 1`.

Content: this is the direct finite-set form of the elementary progression
count, ready to combine with stronger analytic estimates.

Proof: bound `P.card` by the canonical progression count, then apply
`primeCountInProgression_le`.

Role: this gives the elementary comparison interface for finite prime sets in
the P3 development.
-/
theorem card_le_arithmetic_progression_integer_bound (x D a : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % D = a % D) : P.card ≤ x / D + 1 := by
  exact (card_le_primeCountInProgression x D a P hP).trans (primeCountInProgression_le x D a)

/--
Inputs: a finite set `Q` of exceptional prime factors, a prime bound `x`, a
base modulus `D`, and a residue `a`.

Claim: the total number of primes counted in the progressions modulo `D*q` is
at most the sum of the corresponding elementary integer-progression bounds.

Content: for each `q`, apply `primeCountInProgression_le` with modulus `D*q`;
the result bounds contributions that are removed before averaging over
`(p,d)` pairs in the AGP argument.

Role: this is the finite sum interface for the elementary large-prime-factor
error estimate used alongside the Brun–Titchmarsh bound.
-/
theorem sum_prime_progression_count_le_sum_integer_progression_bound (Q : Finset ℕ) (x D a : ℕ) :
    (∑ q ∈ Q, primeCountInProgression x (D * q) a) ≤ ∑ q ∈ Q, (x / (D * q) + 1) := by
  exact Finset.sum_le_sum (fun q hq => primeCountInProgression_le x (D * q) a)

/--
Inputs: a finite set `P` of primes, a bound `x`, and natural numbers `d` and
`k` such that each prime has the form `d * k + 1`.

Claim: `P.card ≤ x / d + 1`.

Content: all such primes belong to the single residue class `1` modulo `d`.

Proof: reduce the equation `d * k + 1` modulo `d`, then use the finite
arithmetic-progression bound.

Role: this bounds the number of supplied primes attached to one divisor `d`;
P3 must combine counts over many divisors using its analytic input.
-/
theorem card_le_progression_primes_of_fixed_divisor (x d k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p = d * k + 1) : P.card ≤ x / d + 1 := by
  classical
    calc
    P.card ≤ primeCountInProgression x d 1 := by
      unfold primeCountInProgression
      apply
        Finset.card_le_card_of_injOn (s := P) (t :=
          (Finset.range (x + 1)).filter (fun n => Nat.Prime n ∧ n % d = 1 % d)) (fun n => n)
      · intro p hp
        have hpdata := hP p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.lt_succ_of_le hpdata.2.1, ?_⟩
        refine ⟨hpdata.1, ?_⟩
        rw [hpdata.2.2]
        calc
          (d * k + 1) % d = ((d * k) % d + 1 % d) % d := Nat.add_mod _ _ _
          _ = (0 + 1 % d) % d := by rw [Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]
          _ = 1 % d := by rw [Nat.zero_add, Nat.mod_mod]
      · intro p hp q hq hpq
        exact hpq
    _ ≤ x / d + 1 := primeCountInProgression_le x d 1

/--
Inputs: finite divisor labels `D`, parameters `k`, `x`, `m`, and `a`.

Definition: retain divisors `d` for which `d * k + 1` is prime, at most `x`,
and congruent to `a` modulo `m`; map each such divisor to the resulting prime.

Output: the finite set of distinct prime values produced by those divisors.

Role: this turns the divisor count in the source propositions into the finite
prime set consumed by the later Carmichael construction.
-/
def primesFromDivisorsInProgression (D : Finset ℕ) (k x m a : ℕ) : Finset ℕ :=
  (D.filter (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).image
    (fun d => d * k + 1)

/--
Inputs: the parameters of `primesFromDivisorsInProgression` and a positive `k`.

Claim: its prime set has the same cardinality as the filtered divisor set.

Content: distinct divisors give distinct values `d * k + 1` when `k > 0`.

Proof: cancel the positive factor `k` from an equality of two image values.

Role: this preserves the lower bound on good divisors when converting them to
distinct primes.
-/
theorem primesFromDivisorsInProgression_card (D : Finset ℕ) (k x m a : ℕ) (hk : 0 < k) :
    (primesFromDivisorsInProgression D k x m a).card =
      (D.filter
          (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card := by
  unfold primesFromDivisorsInProgression
  apply Finset.card_image_of_injOn
  intro d hd e he h
  exact Nat.mul_right_cancel hk (Nat.add_right_cancel h)

/--
Inputs: the parameters of `primesFromDivisorsInProgression` and a member `p` of
the resulting prime set.

Claim: `p` is prime, at most `x`, lies in the residue class `a mod m`, and is
`d * k + 1` for some `d ∈ D`.

Content: every member comes from one divisor retained by the defining filter.

Proof: unpack the finite-set image and filter membership.

Role: this exposes the arithmetic properties required by the P2 prime-set
interface.
-/
theorem mem_primesFromDivisorsInProgression (D : Finset ℕ) (k x m a p : ℕ)
    (hp : p ∈ primesFromDivisorsInProgression D k x m a) :
    Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  unfold primesFromDivisorsInProgression at hp
  rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
  have hdgood := Finset.mem_filter.mp hd
  exact ⟨hdgood.2.1, hdgood.2.2.1, hdgood.2.2.2, d, hdgood.1, rfl⟩

/--
Inputs: a positive progression parameter, divisor labels `D`, and a finite
prime set whose members have the form `d * k + 1` for good `d ∈ D`.

Claim: the number of supplied primes is at most the number of good divisors.

Proof: map every supplied prime into `primesFromDivisorsInProgression`, then
use the injectivity of `d ↦ d * k + 1` for positive `k`.

Role: this converts prime-set lower bounds into the fixed-parameter divisor
count stored in `AGPProgressionCountData`.
-/
theorem card_le_good_divisor_count_of_prime_set (D P : Finset ℕ) (k x m a : ℕ) (hk : 0 < k)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d ∈ D, p = d * k + 1) :
    P.card ≤
      (D.filter
          (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card := by
  have hsubset : P ⊆ primesFromDivisorsInProgression D k x m a := by
    intro p hp
    obtain ⟨hpPrime, hpx, hpm, d, hd, hpeq⟩ := hP p hp
    have hgood : Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m := by
      rw [← hpeq]
      exact ⟨hpPrime, hpx, hpm⟩
    apply Finset.mem_image.mpr
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, hgood⟩, hpeq.symm⟩
  calc
    P.card ≤ (primesFromDivisorsInProgression D k x m a).card := Finset.card_le_card hsubset
    _ =
        (D.filter
            (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :=
      primesFromDivisorsInProgression_card D k x m a hk

open PseudoPrime.Data.Finset in
/--
Inputs: finite divisor labels `D`, candidate parameters `K`, a prime bound `x`,
a modulus and residue, and a threshold `T`.

Claim: if the total number of pairs `(d, k)` producing primes `d*k+1 ≤ x` in
the specified residue class exceeds `K.card * T`, then one `k ∈ K` has more
than `T` such divisors.

Content: this is the finite average of the divisor counts over `K`.

Proof: exchange the finite sums over `D` and `K`, then apply the averaging
lemma to the sum over `K`.

Role: this is the combinatorial output step for the progression-prime count in
reliable Proposition 1.5.
-/
theorem exists_k_with_many_prime_divisors_in_progression (D K : Finset ℕ) (x m a T : ℕ)
    (h :
      K.card * T <
        ∑ d ∈ D,
          (K.filter
              (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card) :
    ∃ k ∈ K,
      T <
        (D.filter
            (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card := by
  classical
  have hswap :
    (∑ d ∈ D,
        (K.filter
            (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card) =
      ∑ k ∈ K,
        (D.filter
            (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card := by
    simp only [Finset.card_filter]
    exact
      Finset.sum_comm (s := D) (t := K) (f := fun d k =>
        if Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m then 1 else 0)
  rw [hswap] at h
  exact
    exists_index_with_value_gt_of_sum_gt_card_mul K
      (fun k =>
        (D.filter (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card)
      T h

/--
Inputs: finite divisor labels `D`, candidate parameters `K`, a prime bound `x`,
a modulus and residue, a threshold `T`, and positivity of every `k ∈ K`.

Claim: if the total prime-producing pair count exceeds `K.card * T`, then one
parameter `k` gives a finite set `P` of more than `T` distinct primes. Each
prime is at most `x`, lies in the requested residue class, and equals `d*k+1`
for some `d ∈ D`.

Content: this combines the finite averaging result with the injection from
good divisors to distinct prime values.

Proof: select `k` with many good divisors, form the image prime set, and use
positivity of `k` to preserve its cardinality.

Role: this is the combinatorial and finite-set part of reliable Proposition
1.5, conditional on the analytic lower bound for the total pair count.
-/
theorem exists_prime_set_from_divisor_pair_count (D K : Finset ℕ) (x m a T : ℕ)
    (hK : ∀ k ∈ K, 0 < k)
    (h :
      K.card * T <
        ∑ d ∈ D,
          (K.filter
              (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card) :
    ∃ k ∈ K,
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  obtain ⟨k, hkK, hkCount⟩ := exists_k_with_many_prime_divisors_in_progression D K x m a T h
  refine ⟨k, hkK, primesFromDivisorsInProgression D k x m a, ?_, ?_⟩
  · rw [primesFromDivisorsInProgression_card D k x m a (hK k hkK)]
    exact hkCount
  · intro p hp
    exact mem_primesFromDivisorsInProgression D k x m a p hp

/--
Inputs: finite divisor and parameter sets, progression data, a threshold `T`,
and a real lower bound for the total number of good divisor-parameter pairs.

Claim: some parameter `k` yields more than `T` distinct primes in the
progression, each of the form `d*k+1` for a divisor `d ∈ D`.

Content: this converts a real estimate for the total pair count to the natural
threshold required by the finite averaging and image arguments.

Proof: combine the real inequalities, cast the strict inequality to `ℕ`, and
apply `exists_prime_set_from_divisor_pair_count`.

Role: this is the bridge from the real-valued sieve estimates in reliable,
Proposition 1.5, to the finite prime set used by the AGP construction.
-/
theorem exists_prime_set_from_real_divisor_pair_lower_bound (D K : Finset ℕ) (x m a T : ℕ) (c : ℝ)
    (hK : ∀ k ∈ K, 0 < k) (hlower : ((K.card * T : ℕ) : ℝ) < c * (D.card : ℝ))
    (hanalytic :
      c * (D.card : ℝ) ≤
        (↑(∑ d ∈ D,
              (K.filter
                  (fun k =>
                    Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card) :
          ℝ)) :
    ∃ k ∈ K,
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  have hpair :
    K.card * T <
      ∑ d ∈ D,
        (K.filter
            (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :=
    Nat.cast_lt.mp (lt_of_lt_of_le hlower hanalytic)
  exact exists_prime_set_from_divisor_pair_count D K x m a T hK hpair

/--
Inputs: divisor-dependent cutoffs, a common prime bound, positive coprime
parameters, and a real lower estimate for the progression counts.

Claim: one parameter yields more than `T` distinct primes below the common
bound, in the requested residue class, with each prime represented as `d*k+1`
for some divisor label `d`.

Proof: replace each divisor-dependent cutoff by the common bound, then apply
the real-valued finite averaging theorem.

Role: this connects progression estimates with varying cutoffs to the prime
set interface consumed by the AGP construction.
-/
theorem exists_prime_set_from_variable_coprime_progression_lower_bound (D : Finset ℕ) (x : ℕ → ℕ)
    (xmax Kmax m a L T : ℕ) (c : ℝ) (hpos : ∀ d ∈ D, 0 < d) (hcut : ∀ d ∈ D, x d ≤ d * Kmax + 1)
    (hcommon : ∀ d ∈ D, x d ≤ xmax)
    (hlower : ((positiveCoprimeParameters L Kmax).card * T : ℕ) < c * (D.card : ℝ))
    (hanalytic :
      c * (D.card : ℝ) ≤
        (↑(∑ d ∈ D, primeCountInProgressionWithCoprimeQuotient (x d) d m a L) : ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L Kmax,
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ xmax ∧ p % m = a % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  have hcount_le :
    (∑ d ∈ D,
        ((positiveCoprimeParameters L Kmax).filter
            (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x d ∧ (d * k + 1) % m = a % m)).card) ≤
      ∑ d ∈ D,
        ((positiveCoprimeParameters L Kmax).filter
            (fun k =>
              Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ xmax ∧ (d * k + 1) % m = a % m)).card := by
    apply Finset.sum_le_sum
    intro d hdD
    apply Finset.card_le_card
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    exact
      Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hk).1, ⟨hk'.1, le_trans hk'.2.1 (hcommon d hdD), hk'.2.2⟩⟩
  have hsum_eq :=
    sum_progression_counts_with_coprime_quotient_eq_positive_good_pairs D x Kmax m a L hpos hcut
  have hreal :
    (↑(∑ d ∈ D,
            ((positiveCoprimeParameters L Kmax).filter
                (fun k =>
                  Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ xmax ∧ (d * k + 1) % m = a % m)).card) :
        ℝ) ≥
      c * (D.card : ℝ) := by
    rw [hsum_eq] at hanalytic
    exact le_trans hanalytic (Nat.cast_le.mpr hcount_le)
  have hKpos : ∀ k ∈ positiveCoprimeParameters L Kmax, 0 < k := by
    intro k hk
    exact Nat.zero_lt_of_lt (Nat.succ_le_iff.mp (mem_positiveCoprimeParameters.mp hk).1)
  exact
    exists_prime_set_from_real_divisor_pair_lower_bound D (positiveCoprimeParameters L Kmax) xmax m
      a T c hKpos hlower hreal

/--
Purpose: select the divisors of `L` below a prescribed cutoff.

Definition: filter `L.divisors` by `d ≤ y`; membership is exactly divisibility
by nonzero `L` together with the cutoff condition.

Inputs: a natural number `L` and a cutoff `y`.

Output: the finite set `{d | d ∣ L ∧ d ≤ y}` when `L ≠ 0`.

Role: this is the divisor set appearing in the lower bound of paper95,
Theorem 3.1, and the divisor side of reliable, Proposition 1.5.
-/
def restrictedDivisors (L y : ℕ) : Finset ℕ :=
  L.divisors.filter (fun d => d ≤ y)

/--
Inputs: a nonzero integer `L`, a cutoff `y`, and a natural number `d`.

Claim: `d` belongs to `restrictedDivisors L y` exactly when `d` divides `L`
and `d ≤ y`.

Content: the characterization identifies this finite set with the small
divisors counted in paper95, Theorem 3.1.

Proof: unfold the filtered divisor set and use `Nat.mem_divisors`.

Role: this connects the paper's divisor range to the finite prime-pair
averaging interface in this module.
-/
theorem mem_restrictedDivisors {L y d : ℕ} (hL : L ≠ 0) :
    d ∈ restrictedDivisors L y ↔ d ∣ L ∧ d ≤ y := by
  simp only [restrictedDivisors, Finset.mem_filter, Nat.mem_divisors, hL, ne_eq, not_false_eq_true,
    and_true]

/--
Inputs: a nonzero natural number `L` and a cutoff `y` with `L ≤ y`.

Claim: `restrictedDivisors L y` is exactly the full divisor set of `L`.

Content: every divisor of `L` is at most `L`, so a cutoff at least `L` removes
no divisors.

Proof: compare memberships using `mem_restrictedDivisors` and `Nat.mem_divisors`.

Role: this removes the cutoff from the initial Proposition 1.5 divisor count
when the chosen prime bound is large enough.
-/
theorem restrictedDivisors_eq_divisors_of_le {L y : ℕ} (hL : L ≠ 0) (hLy : L ≤ y) :
    restrictedDivisors L y = L.divisors := by
  ext d
  rw [mem_restrictedDivisors hL, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, _⟩
    exact ⟨hd, hL⟩
  · rintro ⟨hd, _⟩
    exact ⟨hd, le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hd) hLy⟩

/--
Inputs: a nonzero squarefree natural number `L`.

Claim: the number of divisors of `L` is `2 ^ L.primeFactors.card`.

Content: each prime factor contributes exactly the two exponent choices zero
and one to the divisor count.

Proof: use `Nat.card_divisors` and the factorization exponent of a prime
divisor of a squarefree number.

Role: this gives the divisor-count lower bound used in the initial modulus
construction.
-/
theorem card_divisors_eq_two_pow_primeFactors_card {L : ℕ} (hL : L ≠ 0)
    (hSquarefree : Squarefree L) : L.divisors.card = 2 ^ L.primeFactors.card := by
  rw [Nat.card_divisors hL]
  calc
    L.primeFactors.prod (fun p => L.factorization p + 1) = L.primeFactors.prod (fun _ => 2) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpPrime := (Nat.mem_primeFactors.mp hp).1
      have hpDiv := (Nat.mem_primeFactors.mp hp).2.1
      rw [Nat.factorization_eq_one_of_squarefree hSquarefree hpPrime hpDiv]
    _ = 2 ^ L.primeFactors.card := by simp

/--
Inputs: a nonzero squarefree natural number `L` and a divisor cutoff `y` at
least `L`.

Claim: `restrictedDivisors L y` contains all divisors of `L` and has cardinality
`2 ^ L.primeFactors.card`.

Content: choosing `x` with `x^(2/5) ≥ L` makes the restricted divisor count in
Proposition 1.5 attain the full squarefree divisor count.

Proof: identify the restricted set with `L.divisors`, then apply the squarefree
divisor-count formula.

Role: this turns the first Proposition 1.5 lower bound into an exponential
factor-count lower bound when the cutoff covers `L`.
-/
theorem card_restrictedDivisors_eq_two_pow_primeFactors_card {L y : ℕ} (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hLy : L ≤ y) :
    (restrictedDivisors L y).card = 2 ^ L.primeFactors.card := by
  rw [restrictedDivisors_eq_divisors_of_le hL hLy]
  exact card_divisors_eq_two_pow_primeFactors_card hL hSquarefree

/--
Inputs: a nonzero integer `L` and the natural square-root cutoff.

Claim: at least half of the divisors of `L` are at most `Nat.sqrt L`.

Content: for every divisor above the cutoff, its complementary divisor `L / d`
is at most the cutoff. Complementation is injective on the large divisors.

Role: this is the finite pairing estimate needed for the initial divisor count
with the smaller cutoff in reliable, §2.
-/
theorem card_divisors_le_twice_restrictedDivisors_sqrt {L : ℕ} (hL : L ≠ 0) :
    L.divisors.card ≤ 2 * (restrictedDivisors L (Nat.sqrt L)).card := by
  classical
  let A : Finset ℕ := restrictedDivisors L (Nat.sqrt L)
  let B : Finset ℕ := L.divisors.filter (fun d => ¬d ≤ Nat.sqrt L)
  have hpartition : A.card + B.card = L.divisors.card := by
    simpa only [A, B, restrictedDivisors] using
      Finset.card_filter_add_card_filter_not (s := L.divisors) (p := fun d => d ≤ Nat.sqrt L)
  have hB : B.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun d => L / d)
    · intro d hd
      have hdD : d ∈ L.divisors := (Finset.mem_filter.mp hd).1
      have hdDiv : d ∣ L := (Nat.mem_divisors.mp hdD).1
      have hdAbove : Nat.sqrt L < d := lt_of_not_ge (Finset.mem_filter.mp hd).2
      have hquot : L / d ≤ Nat.sqrt L := by
        by_contra hnot
        have hdLower : Nat.sqrt L + 1 ≤ d := Nat.succ_le_of_lt hdAbove
        have hqAbove : Nat.sqrt L < L / d := lt_of_not_ge hnot
        have hqLower : Nat.sqrt L + 1 ≤ L / d := Nat.succ_le_of_lt hqAbove
        have hprod := Nat.mul_le_mul hdLower hqLower
        have hfactor : d * (L / d) = L := Nat.mul_div_cancel' hdDiv
        have hcontra : (Nat.sqrt L + 1) * (Nat.sqrt L + 1) ≤ L := le_trans hprod (by rw [hfactor])
        exact (not_lt_of_ge hcontra) (Nat.lt_succ_sqrt L)
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdDiv, hL⟩, hquot⟩
    · intro a ha b hb hab
      have haDiv : a ∣ L := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1).1
      have hbDiv : b ∣ L := (Nat.mem_divisors.mp (Finset.mem_filter.mp hb).1).1
      exact (Nat.div_eq_iff_eq_of_dvd_dvd hL haDiv hbDiv).mp hab
  calc
    L.divisors.card = A.card + B.card := hpartition.symm
    _ ≤ A.card + A.card := Nat.add_le_add_left hB _
    _ = 2 * A.card := (two_mul A.card).symm

/--
Inputs: a nonzero squarefree integer `L`.

Claim: twice the number of divisors at most `Nat.sqrt L` is at least
`2 ^ L.primeFactors.card`.

Content: the squarefree divisor formula and the complementary-divisor pairing
give the lower bound without requiring the cutoff to contain all divisors.

Role: this supplies the initial Proposition 1.5 count at the square-root
cutoff used by reliable, §2.
-/
theorem two_pow_primeFactors_card_le_twice_restrictedDivisors_sqrt {L : ℕ} (hL : L ≠ 0)
    (hSquarefree : Squarefree L) :
    2 ^ L.primeFactors.card ≤ 2 * (restrictedDivisors L (Nat.sqrt L)).card := by
  rw [← card_divisors_eq_two_pow_primeFactors_card hL hSquarefree]
  exact card_divisors_le_twice_restrictedDivisors_sqrt hL

/--
Purpose: retain the restricted divisors of `L` that exceed a chosen cutoff.

Definition: `largeRestrictedDivisors L y q` consists of `d ∣ L` with `d ≤ y`
and `q < d`.

Inputs: a nonzero modulus `L`, an upper divisor cutoff `y`, and a lower cutoff
`q`.

Output: the finite divisor set after removing all `d ≤ q`.

Role: for squarefree `L`, a divisor `d` above every prime factor of `L`
ensures that `p=d*k+1` is larger than every prime factor of `L` when `k>0`.
-/
def largeRestrictedDivisors (L y q : ℕ) : Finset ℕ :=
  (restrictedDivisors L y).filter (fun d => q < d)

/--
Inputs: nonzero `L`, cutoffs `y` and `q`, and a natural number `d`.

Claim: membership in `largeRestrictedDivisors L y q` means `d ∣ L`, `d ≤ y`,
and `q < d`.

Proof: unfold both finite filters and use `mem_restrictedDivisors`.

Role: this exposes the divisor conditions retained in the large-divisor
prime-supply interface.
-/
theorem mem_largeRestrictedDivisors {L y q d : ℕ} (hL : L ≠ 0) :
    d ∈ largeRestrictedDivisors L y q ↔ d ∣ L ∧ d ≤ y ∧ q < d := by
  simp only [largeRestrictedDivisors, Finset.mem_filter, mem_restrictedDivisors hL]
  constructor
  · rintro ⟨⟨hdL, hdy⟩, hqd⟩
    exact ⟨hdL, hdy, hqd⟩
  · rintro ⟨hdL, hdy, hqd⟩
    exact ⟨⟨hdL, hdy⟩, hqd⟩

/--
Inputs: a divisor cutoff `y`, a strict lower threshold `q`, and any modulus `L`.

Claim: removing divisors at most `q` loses at most `q + 1` elements.

Proof: the discarded divisors lie in `Finset.range (q + 1)`; partition the
restricted divisors into retained and discarded filters.

Role: this bounds the finite loss when only large moduli use the progression
prime estimate.
-/
theorem restrictedDivisors_card_sub_threshold_le_large (L y q : ℕ) :
    (restrictedDivisors L y).card - (q + 1) ≤ (largeRestrictedDivisors L y q).card := by
  have hsmallSubset : {d ∈ restrictedDivisors L y | ¬q < d} ⊆ Finset.range (q + 1) := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_lt hd'.2))
  have hsmallBound : {d ∈ restrictedDivisors L y | ¬q < d}.card ≤ q + 1 := by
    calc
      {d ∈ restrictedDivisors L y | ¬q < d}.card ≤ (Finset.range (q + 1)).card :=
        Finset.card_le_card hsmallSubset
      _ = q + 1 := Finset.card_range (q + 1)
  have hpartition :=
    Finset.card_filter_add_card_filter_not (s := restrictedDivisors L y) (p := fun d => q < d)
  apply Nat.sub_le_iff_le_add.mpr
  calc
    (restrictedDivisors L y).card =
        (largeRestrictedDivisors L y q).card + {d ∈ restrictedDivisors L y | ¬q < d}.card :=
      hpartition.symm
    _ ≤ (largeRestrictedDivisors L y q).card + (q + 1) := Nat.add_le_add_left hsmallBound _

/--
Inputs: a modulus `m`, a target residue `l`, a divisor `d` in the restricted
divisor set of `L`, and coprimality of `L` and `m` and of `l` and `m`.

Claim: there is a residue modulo `d*m` that is `1` modulo `d`, equals `l`
modulo `m`, and is coprime to `d*m`.

Content: every restricted divisor inherits coprimality with `m` from `L`, so
the Chinese remainder construction applies to each divisor in the source
count.

Proof: extract `d ∣ L`, transfer coprimality to `d`, then use
`progressionCoprimeResidue_spec`.

Role: this supplies the admissible residue classes modulo `d*m` used in the
prime-counting step of reliable, Proposition 1.5.
-/
theorem exists_coprime_residue_for_restricted_divisor {L y m l d : ℕ} (hLm : Nat.Coprime L m)
    (hlm : Nat.Coprime l m) (hd : d ∈ restrictedDivisors L y) :
    ∃ a, a % d = 1 % d ∧ a % m = l % m ∧ Nat.Coprime a (d * m) := by
  have hdL : d ∣ L := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdm : Nat.Coprime d m := Nat.Coprime.of_dvd_left hdL hLm
  refine ⟨progressionCoprimeResidue d m l hdm, ?_⟩
  exact progressionCoprimeResidue_spec d m l hdm hlm

/--
Inputs: nonzero `L`, a divisor cutoff `y`, a finite parameter set `K`, a prime
bound `x`, a residue class, and a lower bound on the total good-pair count.

Claim: some `k ∈ K` yields more than `T` distinct primes `p ≤ x` in the chosen
residue class, each represented by `p = d*k+1` for a divisor `d ∣ L` with
`d ≤ y`.

Content: this is the paper95 Theorem 3.1 divisor range followed by the finite
averaging and image arguments. The analytic lower bound on the pair count
remains a separate hypothesis.

Proof: apply the general pair-count theorem to `restrictedDivisors L y` and
translate membership using `mem_restrictedDivisors`.

Role: this exposes the source-shaped finite conclusion for the later analytic
estimate and the application in reliable, Proposition 1.5.
-/
theorem exists_prime_set_from_restricted_divisor_pair_count (L y : ℕ) (hL : L ≠ 0) (K : Finset ℕ)
    (x m a T : ℕ) (hK : ∀ k ∈ K, 0 < k)
    (h :
      K.card * T <
        ∑ d ∈ restrictedDivisors L y,
          (K.filter
              (fun k => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card) :
    ∃ k ∈ K,
      ∃ P : Finset ℕ,
        T < P.card ∧
          ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d, d ∣ L ∧ d ≤ y ∧ p = d * k + 1 := by
  obtain ⟨k, hk, P, hcard, hP⟩ :=
    exists_prime_set_from_divisor_pair_count (restrictedDivisors L y) K x m a T hK h
  refine ⟨k, hk, P, hcard, ?_⟩
  intro p hp
  rcases hP p hp with ⟨hpPrime, hpx, hpm, d, hd, hpeq⟩
  have hd' := (mem_restrictedDivisors hL).mp hd
  exact ⟨hpPrime, hpx, hpm, d, hd'.1, hd'.2, hpeq⟩

/--
Inputs: a nonzero modulus `L`, divisor and parameter cutoffs, variable prime
bounds, and a real lower estimate for the coprime-quotient progression counts.

Claim: there is a parameter coprime to `L` and a finite set of more than `T`
primes below the common bound, in the requested residue class, each of the
form `d*k+1` for a divisor `d ∣ L` below the divisor cutoff.

Proof: specialize the variable-cutoff averaging theorem to
`restrictedDivisors L y` and translate its output using
`mem_restrictedDivisors`.

Role: this is the finite output interface shaped like reliable, Proposition
1.5, conditional on its analytic prime-count lower bound.
-/
theorem exists_prime_set_from_restricted_coprime_progression_lower_bound (L y : ℕ) (hL : L ≠ 0)
    (x : ℕ → ℕ) (xmax Kmax m a T : ℕ) (c : ℝ) (hpos : ∀ d ∈ restrictedDivisors L y, 0 < d)
    (hcut : ∀ d ∈ restrictedDivisors L y, x d ≤ d * Kmax + 1)
    (hcommon : ∀ d ∈ restrictedDivisors L y, x d ≤ xmax)
    (hlower :
      ((positiveCoprimeParameters L Kmax).card * T : ℕ) < c * ((restrictedDivisors L y).card : ℝ))
    (hanalytic :
      c * ((restrictedDivisors L y).card : ℝ) ≤
        (↑(∑ d ∈ restrictedDivisors L y, primeCountInProgressionWithCoprimeQuotient (x d) d m a L) :
          ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L Kmax,
      ∃ P : Finset ℕ,
        T < P.card ∧
          ∀ p ∈ P, Nat.Prime p ∧ p ≤ xmax ∧ p % m = a % m ∧ ∃ d, d ∣ L ∧ d ≤ y ∧ p = d * k + 1 := by
  obtain ⟨k, hk, P, hPcard, hP⟩ :=
    exists_prime_set_from_variable_coprime_progression_lower_bound (restrictedDivisors L y) x xmax
      Kmax m a L T c hpos hcut hcommon hlower hanalytic
  refine ⟨k, hk, P, hPcard, ?_⟩
  intro p hp
  rcases hP p hp with ⟨hpPrime, hpx, hpm, d, hd, hpeq⟩
  have hd' := (mem_restrictedDivisors hL).mp hd
  exact ⟨hpPrime, hpx, hpm, d, hd'.1, hd'.2, hpeq⟩

/--
Inputs: a nonzero modulus `L`, a divisor range, a bound `q` for
prime factors of `L`, a lower bound `C ≤ q`, and a real lower estimate for
the coprime-quotient progression counts over divisors above `q`.

Claim: there is a positive parameter coprime to `L` and a finite set of more
than `T` primes in the requested residue class. Each prime exceeds `C`, is
coprime to `L`, and has the form `d*k+1` with `d ∣ L`, `d ≤ y`, and `q < d`.

Proof: apply the variable-cutoff finite averaging theorem to
`largeRestrictedDivisors L y q`. Positivity of `k` gives `d < d*k+1`; the
factor bound then excludes every prime divisor of `L` from the output prime.

Role: this separates the paper's analytic estimate from the final finite
filters needed by `AGPProgressionPrimeSupply`.
-/
theorem exists_prime_set_from_large_restricted_coprime_progression_lower_bound (L y q C : ℕ)
    (hL : L ≠ 0) (hqL : ∀ r, r ∣ L → Nat.Prime r → r ≤ q) (hC : C ≤ q) (x : ℕ → ℕ)
    (xmax Kmax m a T : ℕ) (c : ℝ) (hcut : ∀ d ∈ largeRestrictedDivisors L y q, x d ≤ d * Kmax + 1)
    (hcommon : ∀ d ∈ largeRestrictedDivisors L y q, x d ≤ xmax)
    (hlower :
      ((positiveCoprimeParameters L Kmax).card * T : ℕ) <
        c * ((largeRestrictedDivisors L y q).card : ℝ))
    (hanalytic :
      c * ((largeRestrictedDivisors L y q).card : ℝ) ≤
        (↑(∑ d ∈ largeRestrictedDivisors L y q,
              primeCountInProgressionWithCoprimeQuotient (x d) d m a L) :
          ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L Kmax,
      ∃ P : Finset ℕ,
        T < P.card ∧
          ∀ p ∈ P,
            Nat.Prime p ∧
              p ≤ xmax ∧
              p % m = a % m ∧
              C < p ∧ Nat.Coprime p L ∧ ∃ d, d ∣ L ∧ d ≤ y ∧ q < d ∧ p = d * k + 1 := by
  have hpos : ∀ d ∈ largeRestrictedDivisors L y q, 0 < d := by
    intro d hd
    exact Nat.pos_of_dvd_of_pos ((mem_largeRestrictedDivisors hL).mp hd).1 (Nat.pos_of_ne_zero hL)
  obtain ⟨k, hk, P, hPcard, hP⟩ :=
    exists_prime_set_from_variable_coprime_progression_lower_bound (largeRestrictedDivisors L y q) x
      xmax Kmax m a L T c hpos hcut hcommon hlower hanalytic
  have hkpos : 0 < k := by
    exact Nat.zero_lt_of_lt (Nat.succ_le_iff.mp (mem_positiveCoprimeParameters.mp hk).1)
  have hkone : 1 ≤ k := Nat.succ_le_iff.mpr hkpos
  refine ⟨k, hk, P, hPcard, ?_⟩
  intro p hp
  rcases hP p hp with ⟨hpPrime, hpx, hpm, d, hd, hpeq⟩
  have hd' := (mem_largeRestrictedDivisors hL).mp hd
  have hdk : d ≤ d * k := by
    calc
      d = d * 1 := by simp only [Nat.mul_one]
      _ ≤ d * k := Nat.mul_le_mul_left d hkone
  have hdp : d < p := by
    rw [hpeq]
    exact Nat.lt_succ_of_le hdk
  have hqp : q < p := lt_trans hd'.2.2 hdp
  have hnot : ¬p ∣ L := by
    intro hpL
    exact (Nat.not_le_of_gt hqp) (hqL p hpL hpPrime)
  have hpC : C < p := lt_of_le_of_lt hC hqp
  have hcop : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hpPrime).2 hnot
  exact ⟨hpPrime, hpx, hpm, hpC, hcop, d, hd'.1, hd'.2.1, hd'.2.2, hpeq⟩

/--
Inputs: nonzero `L`, a cutoff `y`, a positive parameter `k`, a prime bound,
a residue class, and a lower bound for the good restricted-divisor count.

Claim: there is a finite set of more than `T` distinct primes in the residue
class, each at most `x` and represented by `d*k+1` for some `d ∣ L` with
`d ≤ y`.

Content: this is the pointwise form of the divisor-to-prime conversion. It
matches an analytic result that already supplies one suitable `k`, as in the
conclusion of paper95, Theorem 3.1.

Proof: map the good divisors to prime values; positivity of `k` makes the map
injective, and `mem_restrictedDivisors` recovers the divisor conditions.

Role: this connects a pointwise analytic divisor count directly to the finite
prime-set input used by the AGP construction.
-/
theorem exists_prime_set_of_many_restricted_divisors_in_progression (L y k x m a T : ℕ) (hL : L ≠ 0)
    (hk : 0 < k)
    (h :
      T <
        ((restrictedDivisors L y).filter
            (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card) :
    ∃ P : Finset ℕ,
      T < P.card ∧
        ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d, d ∣ L ∧ d ≤ y ∧ p = d * k + 1 := by
  refine ⟨primesFromDivisorsInProgression (restrictedDivisors L y) k x m a, ?_, ?_⟩
  · rw [primesFromDivisorsInProgression_card _ _ _ _ _ hk]
    exact h
  · intro p hp
    obtain ⟨hpPrime, hpx, hpm, d, hd, hpeq⟩ := mem_primesFromDivisorsInProgression _ _ _ _ _ _ hp
    have hd' := (mem_restrictedDivisors hL).mp hd
    exact ⟨hpPrime, hpx, hpm, d, hd'.1, hd'.2, hpeq⟩

/--
Inputs: the data of the pointwise restricted-divisor count, a real coefficient
`c`, a lower bound for `c` times the number of small divisors, and an analytic
lower bound for the good-divisor count.

Claim: there is a finite set of more than `T` distinct primes in the specified
progression, each represented by a small divisor of `L`.

Content: this converts a real-valued analytic estimate into the natural-valued
cardinality threshold needed by the AGP construction.

Proof: combine the two real inequalities, cast the strict inequality back to
`ℕ`, and apply the pointwise divisor-to-prime result.

Role: this is the interface for inserting the real lower bound from paper95,
Theorem 3.1, once its analytic estimate is formalized.
-/
theorem exists_prime_set_of_real_restricted_divisor_lower_bound (L y k x m a T : ℕ) (hL : L ≠ 0)
    (hk : 0 < k) (c : ℝ) (hlower : (T : ℝ) < c * ((restrictedDivisors L y).card : ℝ))
    (hanalytic :
      c * ((restrictedDivisors L y).card : ℝ) ≤
        ((((restrictedDivisors L y).filter
                (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :
            ℕ) :
          ℝ)) :
    ∃ P : Finset ℕ,
      T < P.card ∧
        ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d, d ∣ L ∧ d ≤ y ∧ p = d * k + 1 := by
  have hcount :
    T <
      ((restrictedDivisors L y).filter
          (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :=
    Nat.cast_lt.mp (lt_of_lt_of_le hlower hanalytic)
  exact exists_prime_set_of_many_restricted_divisors_in_progression L y k x m a T hL hk hcount

/--
Inputs: a finite divisor set, a positive parameter, a prime bound, a
progression, a threshold, and a real lower bound for the good-divisor count.

Claim: there is a finite set of more than `T` distinct primes in the requested
progression, each at most `x` and represented as `d*k+1` for some `d ∈ D`.

Proof: convert the real inequality to a natural cardinality bound and map the
good divisors injectively to prime values.

Role: this generalizes the pointwise restricted-divisor conversion so that
additional divisor filters can express the analytic hypotheses directly.
-/
theorem exists_prime_set_from_real_divisor_count_lower_bound (D : Finset ℕ) (k x m a T : ℕ) (c : ℝ)
    (hk : 0 < k) (hlower : (T : ℝ) < c * (D.card : ℝ))
    (hanalytic :
      c * (D.card : ℝ) ≤
        ((((D.filter
                (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :
            ℕ) :
          ℝ))) :
    ∃ P : Finset ℕ,
      T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  have hcount :
    T <
      (D.filter (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :=
    Nat.cast_lt.mp (lt_of_lt_of_le hlower hanalytic)
  refine ⟨primesFromDivisorsInProgression D k x m a, ?_, ?_⟩
  · rw [primesFromDivisorsInProgression_card D k x m a hk]
    exact hcount
  · intro p hp
    exact mem_primesFromDivisorsInProgression D k x m a p hp

/--
Inputs: a finite set of divisor labels, a positive parameter, a prime bound,
a residue class, a cutoff `q`, and a strict lower bound for the number of
good divisors whose prime value exceeds `q`.

Claim: there are more than `T` distinct primes in the requested progression,
all greater than `q`, each represented as `d*k+1` for a label in `D`.

Proof: map the retained good divisors to their prime values. Positivity of
`k` makes this map injective.

Role: this removes small prime values after applying the full divisor-count
estimate, without requiring a separate density estimate for small divisors.
-/
theorem exists_prime_set_from_real_divisor_count_lower_bound_above (D : Finset ℕ) (k x m a q T : ℕ)
    (hk : 0 < k)
    (hcount :
      T <
        (D.filter
            (fun d =>
              q < d * k + 1 ∧
                Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card) :
    ∃ P : Finset ℕ,
      T < P.card ∧
        ∀ p ∈ P, Nat.Prime p ∧ p ≤ x ∧ p % m = a % m ∧ q < p ∧ ∃ d ∈ D, p = d * k + 1 := by
  let Dgood :=
    D.filter
      (fun d => q < d * k + 1 ∧ Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)
  let P := Dgood.image (fun d => d * k + 1)
  have hcard : P.card = Dgood.card := by
    dsimp only [P, Dgood]
    apply Finset.card_image_of_injOn
    intro d hd e he hde
    exact Nat.mul_right_cancel hk (Nat.add_right_cancel hde)
  refine ⟨P, ?_, ?_⟩
  · rw [hcard]
    exact hcount
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
    have hd' := Finset.mem_filter.mp hd
    rcases hd'.2 with ⟨hqd, hprime, hbound, hresidue⟩
    exact ⟨hprime, hbound, hresidue, hqd, ⟨d, hd'.1, rfl⟩⟩

/--
Inputs: a finite set, a retained predicate, a counted predicate, a real
coefficient, a lower bound for the full count, and an upper bound for the
count lost outside the retained set.

Claim: the retained part still has count at least the coefficient times the
size of the retained set.

Proof: split the good finite count into retained and discarded parts, then use
the strict margin and the assumed discarded-count bound.

Role: this transfers the full small-divisor estimate in reliable,
Proposition 1.5 to the divisors above the prime-factor cutoff.
-/
theorem real_card_filter_lower_bound_of_discarded_count_bound (D : Finset ℕ) {keep good : ℕ → Prop}
    [DecidablePred keep] [DecidablePred good] (c : ℝ) (T R : ℕ)
    (hfull : ((T + R : ℕ) : ℝ) < c * (D.card : ℝ))
    (hgood : c * (D.card : ℝ) ≤ (((D.filter good).card : ℕ) : ℝ))
    (hdiscarded : (((D.filter (fun d => ¬keep d ∧ good d)).card : ℕ) : ℝ) ≤ R) :
    (T : ℝ) < (((D.filter (fun d => keep d ∧ good d)).card : ℕ) : ℝ) := by
  classical
  have hkeepEq : (D.filter good).filter keep = D.filter (fun d => keep d ∧ good d) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hd, hgood⟩, hkeep⟩
      exact ⟨hd, hkeep, hgood⟩
    · rintro ⟨hd, hkeep, hgood⟩
      exact ⟨⟨hd, hgood⟩, hkeep⟩
  have hdiscardedEq :
    (D.filter good).filter (fun d => ¬keep d) = D.filter (fun d => ¬keep d ∧ good d) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hd, hgood⟩, hnotKeep⟩
      exact ⟨hd, hnotKeep, hgood⟩
    · rintro ⟨hd, hnotKeep, hgood⟩
      exact ⟨⟨hd, hgood⟩, hnotKeep⟩
  have hgoodSplitNat := Finset.card_filter_add_card_filter_not (s := D.filter good) (p := keep)
  have hgoodSplit :
    (((D.filter (fun d => keep d ∧ good d)).card : ℕ) : ℝ) +
        (((D.filter (fun d => ¬keep d ∧ good d)).card : ℕ) : ℝ) =
      (((D.filter good).card : ℕ) : ℝ) := by
    rw [← hkeepEq, ← hdiscardedEq]
    calc
      _ =
          (((((D.filter good).filter keep).card + ((D.filter good).filter fun d => ¬keep d).card :
              ℕ) :
            ℝ)) :=
        by rw [Nat.cast_add]
      _ = (((D.filter good).card : ℕ) : ℝ) := congrArg (fun n : ℕ => (n : ℝ)) hgoodSplitNat
  have htotal : ((T + R : ℕ) : ℝ) < (((D.filter good).card : ℕ) : ℝ) := lt_of_lt_of_le hfull hgood
  rw [← hgoodSplit] at htotal
  rw [Nat.cast_add] at htotal
  linarith only [htotal, hdiscarded]

/--
Inputs: a finite set `D`, a positive parameter `k`, and a cutoff `q`.

Claim: at most `q` elements of `D` can satisfy `d*k+1 ≤ q`.

Proof: positivity of `k` gives `d ≤ d*k`, so every such `d` lies in
`Finset.range q`.

Role: this bounds the small-prime terms discarded when the progression count
is restricted to primes larger than every prime factor of the auxiliary `L`.
-/
theorem card_small_parameters_le (D : Finset ℕ) (k q : ℕ) (hk : 0 < k) :
    (((D.filter (fun d => d * k + 1 ≤ q)).card : ℕ) : ℝ) ≤ q := by
  classical
  have hsubset : D.filter (fun d => d * k + 1 ≤ q) ⊆ Finset.range q := by
    intro d hd
    rw [Finset.mem_range]
    have hsmall := (Finset.mem_filter.mp hd).2
    have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk)
    have hdk : d ≤ d * k := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hkone
    have hsucc : d + 1 ≤ q := le_trans (Nat.add_le_add_right hdk 1) hsmall
    exact Nat.lt_of_succ_le hsucc
  have hcard : (D.filter (fun d => d * k + 1 ≤ q)).card ≤ q := by
    calc
      _ ≤ (Finset.range q).card := Finset.card_le_card hsubset
      _ = q := Finset.card_range q
  exact Nat.cast_le.mpr hcard

/--
Inputs: a nonzero modulus `L`, a divisor interval, a cutoff `q` above all
prime factors of `L`, a positive parameter, and a real lower bound for the
good-divisor count over `largeRestrictedDivisors L y q`.

Claim: there is a finite set of more than `T` primes at most `x` in the
requested progression. Every prime exceeds `C`, is coprime to `L`, and equals
`d*k+1` for a divisor `d ∣ L` with `q < d ≤ y`.

Proof: apply the generic finite divisor-count conversion. Positivity of `k`
gives `d < d*k+1`; the factor bound then proves the prime is coprime to `L`.

Role: this is the pointwise analytic-count interface for reliable,
Proposition 1.5 with the exclusions needed by the AGP construction.
-/
theorem exists_prime_set_from_large_restricted_divisor_real_lower_bound (L y q C k x m a T : ℕ)
    (hL : L ≠ 0) (hqL : ∀ r, r ∣ L → Nat.Prime r → r ≤ q) (hC : C ≤ q) (hk : 0 < k) (c : ℝ)
    (hlower : (T : ℝ) < c * ((largeRestrictedDivisors L y q).card : ℝ))
    (hanalytic :
      c * ((largeRestrictedDivisors L y q).card : ℝ) ≤
        ((((largeRestrictedDivisors L y q).filter
                (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :
            ℕ) :
          ℝ)) :
    ∃ P : Finset ℕ,
      T < P.card ∧
        ∀ p ∈ P,
          Nat.Prime p ∧
            p ≤ x ∧
            p % m = a % m ∧
            C < p ∧ Nat.Coprime p L ∧ ∃ d, d ∣ L ∧ d ≤ y ∧ q < d ∧ p = d * k + 1 := by
  obtain ⟨P, hPcard, hP⟩ :=
    exists_prime_set_from_real_divisor_count_lower_bound (largeRestrictedDivisors L y q) k x m a T c
      hk hlower hanalytic
  have hkone : 1 ≤ k := Nat.succ_le_iff.mpr hk
  refine ⟨P, hPcard, ?_⟩
  intro p hp
  rcases hP p hp with ⟨hpPrime, hpx, hpm, d, hd, hpeq⟩
  have hd' := (mem_largeRestrictedDivisors hL).mp hd
  have hdk : d ≤ d * k := by
    calc
      d = d * 1 := by simp only [Nat.mul_one]
      _ ≤ d * k := Nat.mul_le_mul_left d hkone
  have hdp : d < p := by
    rw [hpeq]
    exact Nat.lt_succ_of_le hdk
  have hqp : q < p := lt_trans hd'.2.2 hdp
  have hnot : ¬p ∣ L := by
    intro hpL
    exact (Nat.not_le_of_gt hqp) (hqL p hpL hpPrime)
  have hcop : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hpPrime).2 hnot
  have hpC : C < p := lt_of_le_of_lt hC hqp
  exact ⟨hpPrime, hpx, hpm, hpC, hcop, d, hd'.1, hd'.2.1, hd'.2.2, hpeq⟩

end PseudoPrime.AnalyticNumberTheory.AGP
