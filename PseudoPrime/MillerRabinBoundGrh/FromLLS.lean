/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.MillerRabinBoundGrh.Small
import PseudoPrime.LLS.Theorem11S2
import PseudoPrime.PrimeTest.MillerRabin.Composite

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
    dsimp [s, d]
    exact (PrimeTest.twoAdicPart_mul_oddPart (n - 1)).symm
  have hdOdd : Odd d := by
    dsimp [d]
    exact PrimeTest.oddPart_odd hnsub
  obtain ⟨p, hp, hpBound, hbase, hsteps⟩ :=
    exists_prime_millerRabin_witness_le_log_sq
      hGRH hn hnOdd hnNotPrime hdecomp hdOdd
  refine ⟨p, hp, hpBound, ?_⟩
  apply (PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass_decomp
    hn hdecomp hdOdd).2
  exact (PrimeTest.not_strongMillerRabinPass_iff).mpr ⟨hbase, hsteps⟩

end PseudoPrime.MillerRabinBoundGrh
