/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.AGP.FiniteBases
public import PseudoPrime.PrimeTest.MillerRabin.AGP.FiniteBasesIff
public import PseudoPrime.PrimeTest.MillerRabin.AGP.LegendreSignature
public import PseudoPrime.AnalyticNumberTheory.AGP.PrimeSupply
public import PseudoPrime.AnalyticNumberTheory.AGP.UnconditionalProgressionCountData

/-! # Initial-base unboundedness from the AGP prime-supply input

This module connects the analytic prime-supply proposition to the finite
Carmichael construction for Miller–Rabin tests.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.MillerRabin.AGP

/--
Assumption: the analytic progression-prime supply holds for every finite set
of positive bases and every requested lower bound.

Claim: Carmichael numbers passing all bases up to any bound exist above every
requested lower bound.

Content: the finite P2 theorem consumes the supplied progression primes. Since
each supplied prime exceeds `C` and the selected product has at least two
factors, the resulting Carmichael number exceeds `C`.

Proof: choose the bases in `[1, B]`, apply the supply proposition, then use the
finite signature-class construction and its product lower bound.

Role: this is the P3-to-`AGPInitialBasesUnbounded` interface; P3 itself remains
to be proved from the analytic estimates in the source papers.
-/
theorem agp_initial_bases_unbounded_of_prime_supply
    (hsupply : PseudoPrime.AnalyticNumberTheory.AGP.AGPProgressionPrimeSupply) :
    AGPInitialBasesUnbounded := by
  apply agpInitialBasesUnbounded_iff.mpr
  intro B C
  let W : Finset ℕ := Finset.Icc 1 B
  have hWpos : ∀ b ∈ W, 0 < b := by
    intro b hb
    have hmem : b ∈ Finset.Icc 1 B := by simpa only [W] using hb
    exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmem).1
  obtain ⟨L, k, P, hL, hlambda, hkL, hP, hsize⟩ := hsupply W C hWpos
  have hNeZeroL : NeZero L := ⟨Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_two hL)⟩
  have hNeZeroLambda : NeZero (ArithmeticFunction.carmichael L) :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hlambda)⟩
  obtain ⟨U, hUP, hUcard, hUcar, hpass⟩ :=
    @exists_carmichael_strongMillerRabin_pass_all_of_large_progression_primes L hNeZeroL hL hlambda
      hNeZeroLambda W P k hkL (fun p hp => (hP p hp).1) (fun p hp => (hP p hp).2.1)
      (fun p hp => (hP p hp).2.2.1) (fun p hp => (hP p hp).2.2.2.1) hWpos
      (fun p hp b hb => (hP p hp).2.2.2.2.2 b hb) hsize
  refine ⟨∏ p ∈ U, p, ?_, hUcar, ?_⟩
  · have hUpos : 0 < U.card := lt_of_lt_of_le (by decide : 0 < 2) hUcard
    obtain ⟨p, hpU⟩ := Finset.card_pos.mp hUpos
    have hpC : C < p := (hP p (hUP hpU)).2.2.2.2.1
    have hprodPos : 0 < ∏ q ∈ U.erase p, q := by
      apply Finset.prod_pos
      intro q hq
      exact Nat.Prime.pos ((hP q (hUP (Finset.mem_erase.mp hq).2)).1)
    calc
      C < p := hpC
      _ ≤ p * ∏ q ∈ U.erase p, q := Nat.le_mul_of_pos_right p hprodPos
      _ = (∏ q ∈ U.erase p, q) * p := Nat.mul_comm _ _
      _ = ∏ q ∈ U, q := Finset.prod_erase_mul U id hpU
  · intro b hb hbB
    have hbW : b ∈ W := by
      change b ∈ Finset.Icc 1 B
      exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hb, hbB⟩
    exact hpass b hbW

/--
Assumption: every finite positive base set and lower bound admits the
progression-count data from the source papers.

Claim: Carmichael numbers passing all bases up to any bound exist above every
requested lower bound.

Proof: convert the count data to prime supply and apply the P3-to-initial-bases
construction.

Role: this records the unbounded initial-base theorem with its remaining
analytic hypothesis isolated explicitly.
-/
theorem agp_initial_bases_unbounded_of_progression_count_data
    (hdata : PseudoPrime.AnalyticNumberTheory.AGP.AGPProgressionCountDataExists) :
    AGPInitialBasesUnbounded :=
  agp_initial_bases_unbounded_of_prime_supply
    (PseudoPrime.AnalyticNumberTheory.AGP.agp_prime_supply_of_progression_count_data hdata)

/--
Assumptions: none beyond the standard foundations; no GRH or analytic supply
hypothesis is required.

Claim: for every pair of natural bounds `B` and `C`, there exists a Carmichael
number greater than `C` that passes the strong Miller-Rabin test at every
positive base at most `B`.

Content: for each fixed initial segment of positive bases, such Carmichael
numbers are arbitrarily large.

Proof: apply the progression-count-data-to-initial-bases construction to the
unconditional progression-count theorem. The existing construction converts
these data to prime supply and then to a finite Carmichael product.

Role: expose `AGPInitialBasesUnbounded` unconditionally, so callers need not
provide progression-count data or a prime-supply hypothesis.
-/
theorem agp_initial_bases_unbounded :
    AGPInitialBasesUnbounded :=
  agp_initial_bases_unbounded_of_progression_count_data
    AnalyticNumberTheory.AGP.agp_progression_count_data_exists_unconditional

end PseudoPrime.PrimeTest.MillerRabin.AGP
