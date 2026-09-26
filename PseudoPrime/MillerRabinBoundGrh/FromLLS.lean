/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.MillerRabinBoundGrh.Small
import PseudoPrime.LLS.Theorem11S2
import PseudoPrime.PrimeTest.MillerRabin.Composite
import PseudoPrime.PrimeTest.MillerRabin.Prime
import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Large-input and GRH assembly for the Miller–Rabin witness bound
-/

namespace PseudoPrime.MillerRabinBoundGrh

/--
Assuming the S2 interface, every odd composite at least `3000` has a prime witness below the
logarithmic-square cutoff. A small prime factor gives the witness directly; otherwise S2 supplies
a prime outside the proper subgroup containing every passing residue.
-/
theorem exists_prime_millerRabin_witness_le_log_sq_of_s2
    (hS2 : LLS.llsTheorem11S2)
    {n s d : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hnNotPrime : ¬ Nat.Prime n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d)
    (hlarge : 3000 ≤ n) :
    ∃ p : ℕ,
      Nat.Prime p ∧
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      (p : ZMod n) ^ d ≠ (1 : ZMod n) ∧
      ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ (-1 : ZMod n) := by
  have hNeZero : NeZero n := ⟨Nat.ne_of_gt (by omega)⟩
  by_cases hsmallFactor :
      ∃ p : ℕ, Nat.Prime p ∧ (p : ℝ) < (Real.log (n : ℝ)) ^ 2 ∧ p ∣ n
  · obtain ⟨p, hp, hpBound, hpDiv⟩ := hsmallFactor
    refine ⟨p, hp, hpBound.le, ?_⟩
    exact PrimeTest.not_strongMillerRabinPass_iff.mp
      (PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hdecomp hp hpDiv)
  · have hnoSmallFactor : ∀ p : ℕ, Nat.Prime p →
        (p : ℝ) < (Real.log (n : ℝ)) ^ 2 → ¬ p ∣ n := by
      intro p hp hpBound hpDiv
      exact hsmallFactor ⟨p, hp, hpBound, hpDiv⟩
    obtain ⟨H, hHproper, hpassImage⟩ :=
      PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass
        hn hnOdd hnNotPrime hdecomp hdOdd
    obtain ⟨p, hp, hpBound, hpOutside⟩ := hS2 n hlarge hnoSmallFactor H hHproper
    refine ⟨p, hp, hpBound, ?_⟩
    apply PrimeTest.not_strongMillerRabinPass_iff.mp
    intro hpass
    obtain ⟨u, hu, huval⟩ := hpassImage (p : ZMod n) hpass
    exact hpOutside ⟨u, hu, huval⟩

/--
Under GRH, the S2 theorem handles `n ≥ 3000`, while the unconditional finite certificate handles
the remaining interval. This is the pointwise witness theorem specified by
`PrimeMillerRabinWitnessBound`.
-/
theorem exists_prime_millerRabin_witness_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n s d : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hnNotPrime : ¬ Nat.Prime n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d) :
    ∃ p : ℕ,
      Nat.Prime p ∧
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      (p : ZMod n) ^ d ≠ (1 : ZMod n) ∧
      ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ (-1 : ZMod n) := by
  have hS2 : LLS.llsTheorem11S2 := LLS.llsTheorem11S2_of_grh hGRH
  by_cases hsmall : n < 3000
  · exact exists_prime_millerRabin_witness_le_log_sq_of_lt_3000
      (n := n) (s := s) (d := d) hn hnOdd hnNotPrime hdecomp hdOdd hsmall
  · have hlarge : 3000 ≤ n := by omega
    exact exists_prime_millerRabin_witness_le_log_sq_of_s2
      hS2 (n := n) (s := s) (d := d) hn hnOdd hnNotPrime hdecomp hdOdd hlarge

/-- The logarithmic-square cutoff is strictly below every odd prime modulus. -/
private theorem log_sq_lt_of_odd_prime {n : ℕ} (hnPrime : Nat.Prime n) (hnOdd : Odd n) :
    (Real.log (n : ℝ)) ^ 2 < (n : ℝ) := by
  have hn3 : 3 ≤ n := by
    rcases hnPrime.two_le.eq_or_lt with h | h
    · subst n
      norm_num at hnOdd
    · omega
  by_cases hn9 : n < 9
  · interval_cases n
    · have hlog : Real.log (3 : ℝ) < 11 / 10 :=
        Real.log_three_lt_d9.trans (by norm_num)
      have hsq := mul_self_lt_mul_self
        ((Real.log_nonneg_iff (by norm_num : (0 : ℝ) < 3)).2 (by norm_num)) hlog
      change (Real.log (3 : ℝ)) ^ 2 < 3
      nlinarith
    · norm_num at hnPrime
    · have hlog : Real.log (5 : ℝ) < 161 / 100 :=
        Real.log_five_lt_d9.trans (by norm_num)
      have hsq := mul_self_lt_mul_self
        ((Real.log_nonneg_iff (by norm_num : (0 : ℝ) < 5)).2 (by norm_num)) hlog
      change (Real.log (5 : ℝ)) ^ 2 < 5
      nlinarith
    · norm_num at hnPrime
    · have hlog7 : Real.log 7 < 21 / 10 := by
        calc
          Real.log 7 < Real.log 8 := Real.log_lt_log (by norm_num) (by norm_num)
          _ = 3 * Real.log 2 := by
            rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
            norm_num
          _ < 21 / 10 := by nlinarith [Real.log_two_lt_d9]
      have hsq := mul_self_lt_mul_self
        ((Real.log_nonneg_iff (by norm_num : (0 : ℝ) < 7)).2 (by norm_num)) hlog7
      change (Real.log (7 : ℝ)) ^ 2 < 7
      nlinarith
    · norm_num at hnPrime
  · have hn9' : 9 ≤ n := by omega
    have he2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have hpos : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have hsq : Real.exp 1 * Real.exp 1 < 3 * 3 :=
        mul_self_lt_mul_self hpos Real.exp_one_lt_three
      nlinarith
    have hn9cast : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9'
    have hexp : Real.exp 2 ≤ (n : ℝ) := le_trans he2.le hn9cast
    have hratio := Real.log_div_sqrt_antitoneOn (le_rfl : Real.exp 2 ≤ Real.exp 2)
      hexp hexp
    have hsqrt : Real.sqrt (Real.exp 2) = Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      exact Real.sqrt_mul_self (Real.exp_nonneg 1)
    have hbase : Real.log (Real.exp 2) / Real.sqrt (Real.exp 2) < 1 := by
      rw [Real.log_exp, hsqrt]
      exact (div_lt_one (Real.exp_pos 1)).2 Real.exp_one_gt_two
    have hratio' : Real.log (n : ℝ) / Real.sqrt (n : ℝ) < 1 :=
      lt_of_le_of_lt hratio hbase
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hloglt : Real.log (n : ℝ) < Real.sqrt (n : ℝ) := by
      rwa [div_lt_iff₀ hsqrtpos, one_mul] at hratio'
    have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).le
    have hsquare := (sq_lt_sq₀ hlognonneg (Real.sqrt_nonneg (n : ℝ))).mpr hloglt
    rw [Real.sq_sqrt (by positivity)] at hsquare
    exact hsquare

/--
A prime modulus has no prime witness below `(log n)^2` that violates the strong-test conditions.
The logarithmic estimate places the base below `n`, making it coprime to the prime modulus; the
prime acceptance result is then applied to the supplied decomposition.
-/
theorem no_prime_millerRabin_witness_le_log_sq_of_prime
    {n s d : ℕ}
    (hnOdd : Odd n)
    (hnPrime : Nat.Prime n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d) :
    ¬ ∃ p : ℕ,
      Nat.Prime p ∧
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      (p : ZMod n) ^ d ≠ (1 : ZMod n) ∧
      ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ (-1 : ZMod n) := by
  rintro ⟨p, hp, hpBound, hreject⟩
  have hpLt : p < n := by
    have hcast : (p : ℝ) < (n : ℝ) :=
      lt_of_le_of_lt hpBound (log_sq_lt_of_odd_prime hnPrime hnOdd)
    exact_mod_cast hcast
  have hcop : Nat.Coprime p n := Nat.coprime_comm.mpr <| hnPrime.coprime_iff_not_dvd.mpr ?_
  · have hpass :=
      (PrimeTest.strongMillerRabinWithBase_eq_true_iff_pass_decomp
        hnPrime.one_lt hdecomp hdOdd).mp
        (PrimeTest.strongMillerRabinWithBase_of_prime hnPrime hcop)
    exact (PrimeTest.not_strongMillerRabinPass_iff.mpr hreject) hpass
  · intro hdiv
    have hle : n ≤ p := Nat.le_of_dvd hp.pos hdiv
    omega

/--
Assuming GRH and a fixed odd decomposition, a rejected prime base below `(log n)^2` exists exactly
when `n` is not prime. The composite direction uses the GRH witness theorem and the prime direction
uses `no_prime_millerRabin_witness_le_log_sq_of_prime`.
-/
theorem exists_prime_millerRabin_witness_le_log_sq_iff_not_prime
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n s d : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d) :
    (∃ p : ℕ,
      Nat.Prime p ∧
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      (p : ZMod n) ^ d ≠ (1 : ZMod n) ∧
      ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ (-1 : ZMod n)) ↔
      ¬ Nat.Prime n := by
  constructor
  · intro hwitness hnPrime
    exact no_prime_millerRabin_witness_le_log_sq_of_prime hnOdd hnPrime
      hdecomp hdOdd hwitness
  · intro hnNotPrime
    exact exists_prime_millerRabin_witness_le_log_sq hGRH
      (n := n) (s := s) (d := d) hn hnOdd hnNotPrime hdecomp hdOdd

/--
Under GRH and a fixed odd decomposition of `n - 1`, `n` is prime exactly when every prime base
below `(log n)^2` passes the strong Miller–Rabin congruence conditions. The forward direction
excludes a rejected witness using primality; the reverse direction contradicts the GRH witness
bound for a composite modulus.
-/
theorem prime_iff_millerRabin_for_all_primes_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n s d : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d) :
    (∀ p : ℕ,
      Nat.Prime p →
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 →
      (p : ZMod n) ^ d = (1 : ZMod n) ∨
        ∃ j : ℕ, j < s ∧
          (p : ZMod n) ^ (2 ^ j * d) = (-1 : ZMod n)) ↔
      Nat.Prime n := by
  classical
  constructor
  · intro hpass
    by_contra hnNotPrime
    obtain ⟨p, hp, hpBound, hpBase, hpSteps⟩ :=
      exists_prime_millerRabin_witness_le_log_sq hGRH hn hnOdd hnNotPrime
        hdecomp hdOdd
    rcases hpass p hp hpBound with hpow | ⟨j, hj, hminus⟩
    · exact hpBase hpow
    · exact hpSteps j hj hminus
  · intro hnPrime p hp hpBound
    by_cases hbase : (p : ZMod n) ^ d = (1 : ZMod n)
    · exact Or.inl hbase
    · by_cases hminus : ∃ j : ℕ, j < s ∧
          (p : ZMod n) ^ (2 ^ j * d) = (-1 : ZMod n)
      · exact Or.inr hminus
      · exfalso
        apply no_prime_millerRabin_witness_le_log_sq_of_prime hnOdd hnPrime
          hdecomp hdOdd
        exact ⟨p, hp, hpBound, hbase,
          fun j hj hpow => hminus ⟨j, hj, hpow⟩⟩

/-- The pointwise GRH theorem proves the target witness-bound property. -/
theorem primeMillerRabinWitnessBound_of_grh
    : PrimeMillerRabinWitnessBound := by
  intro hGRH n s d hn hnOdd hnNotPrime hdecomp hdOdd
  exact exists_prime_millerRabin_witness_le_log_sq
    hGRH (n := n) (s := s) (d := d) hn hnOdd hnNotPrime hdecomp hdOdd

/--
Under GRH, every odd composite has a prime base below `(log n)^2` rejected by the executable
Strong Miller–Rabin test with its computed two-adic decomposition.
-/
theorem exists_prime_strongMillerRabinWithBase_eq_false_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hnNotPrime : ¬ Nat.Prime n) :
    ∃ p : ℕ,
      Nat.Prime p ∧
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      PrimeTest.strongMillerRabinWithBase n p = false := by
  let s := PrimeTest.twoAdicExponent (n - 1)
  let d := PrimeTest.oddPart (n - 1)
  have hnsub : n - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hn
  have hdecomp : n - 1 = 2 ^ s * d := by
    dsimp only [s, d]
    exact (PrimeTest.twoAdicPart_mul_oddPart (n - 1)).symm
  have hdOdd : Odd d := by
    dsimp only [d]
    exact PrimeTest.oddPart_odd hnsub
  obtain ⟨p, hp, hpBound, hbase, hsteps⟩ :=
    exists_prime_millerRabin_witness_le_log_sq
      hGRH hn hnOdd hnNotPrime hdecomp hdOdd
  refine ⟨p, hp, hpBound, ?_⟩
  apply (PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass_decomp
    hn hdecomp hdOdd).2
  exact (PrimeTest.not_strongMillerRabinPass_iff).mpr ⟨hbase, hsteps⟩

end PseudoPrime.MillerRabinBoundGrh
