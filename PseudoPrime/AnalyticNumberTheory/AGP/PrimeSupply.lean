/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionCountData
public import PseudoPrime.AnalyticNumberTheory.AGP.ExceptionalModuli
public import PseudoPrime.AnalyticNumberTheory.AGP.UniformProgressionFixed
public import PseudoPrime.AnalyticNumberTheory.AGP.BrunTitchmarshSpecialization
public import PseudoPrime.AnalyticNumberTheory.AGP.BrunTitchmarshSieveReduction
public import PseudoPrime.AnalyticNumberTheory.AGP.CoarseProgressionSieve
public import PseudoPrime.AnalyticNumberTheory.AGP.TruncatedSelbergPrimorial
public import PseudoPrime.AnalyticNumberTheory.AGP.FixedThetaCountData
public import PseudoPrime.AnalyticNumberTheory.AGP.PrimorialSeedCount
public import PseudoPrime.AnalyticNumberTheory.AGP.PrimorialP2SeedBridge
public import PseudoPrime.AnalyticNumberTheory.AGP.PrimorialProgressionCountData

/-! # PrimeSupply

The finite prime-supply target and its extraction from progression-count data.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a finite set `W` of positive bases and a lower bound `C`.

Claim: there are parameters `L` and `k` and a finite set `P` of distinct primes
such that the primes lie in the required progression, have residue `3 mod 4`,
avoid every base in `W`, exceed `C`, and meet the P2 cardinality threshold.

Content: this records the uniform analytic prime-supply assertion required by
the AGP argument. It is a proposition, not an axiom or an assumed theorem.

Role: once proved, it supplies the input to the conditional reduction in the
Miller–Rabin AGP module.
-/
def AGPProgressionPrimeSupply : Prop :=
  ∀ (W : Finset ℕ) (C : ℕ),
    (∀ b ∈ W, 0 < b) →
      ∃ (L k : ℕ) (P : Finset ℕ),
        2 < L ∧
          3 ≤ ArithmeticFunction.carmichael L ∧
          Nat.Coprime k L ∧
          (∀ p ∈ P,
            Nat.Prime p ∧
              Nat.Coprime p L ∧
              (∃ d, d ∣ L ∧ p = d * k + 1) ∧ p % 4 = 3 ∧ C < p ∧ ∀ b ∈ W, ¬p ∣ b) ∧
          2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log L) < P.card

/--
Assumption: every positive finite base set and lower bound has
`AGPProgressionCountData` as above.

Claim: `AGPProgressionPrimeSupply` holds, including the residue modulo `4`,
the coprimality and lower-bound conditions for every selected prime, and the
P2 cardinality threshold.

Proof: subtract at most `q` divisors whose prime value is at most `q` from the
full Proposition 1.5 count. The remaining primes exceed every prime factor of
`L`, `C`, and every base in `W`.

Role: this isolates the remaining analytic work as the construction of the
count data, without weakening the unconditional target.
-/
theorem agp_prime_supply_of_progression_count_data (hdata : AGPProgressionCountDataExists) :
    AGPProgressionPrimeSupply := by
  classical
  obtain ⟨c₀, _, x₀, _, hdata⟩ := hdata
  intro W C hWpos
  obtain ⟨_, data, _, _⟩ := hdata W C hWpos
  have hL : data.L ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two data.hL)
  let D := restrictedDivisors data.L data.y
  let keep : ℕ → Prop := fun d => data.q < d * data.k + 1
  let good : ℕ → Prop := fun d =>
    Nat.Prime (d * data.k + 1) ∧ d * data.k + 1 ≤ data.x ∧ (d * data.k + 1) % 4 = 3
  have hdiscarded : (((D.filter (fun d => ¬keep d ∧ good d)).card : ℕ) : ℝ) ≤ data.q := by
    have hsubset :
      D.filter (fun d => ¬keep d ∧ good d) ⊆ D.filter (fun d => d * data.k + 1 ≤ data.q) := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hbad := hd'.2.1
      exact Finset.mem_filter.mpr ⟨hd'.1, Nat.not_lt.mp hbad⟩
    have hcard := Finset.card_le_card hsubset
    exact le_trans (Nat.cast_le.mpr hcard) (card_small_parameters_le D data.k data.q data.hk)
  have hretained :=
    real_card_filter_lower_bound_of_discarded_count_bound D (keep := keep) (good := good)
      (reliableProp15Coefficient c₀ 4 data.x)
      (2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael data.L : ℝ) * Real.log data.L)) data.q
      data.hlower data.hProp15 hdiscarded
  have hretainedCount :
    2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael data.L : ℝ) * Real.log data.L) <
      (D.filter (fun d => keep d ∧ good d)).card :=
    Nat.cast_lt.mp hretained
  obtain ⟨P, hPcard, hP⟩ :=
    exists_prime_set_from_real_divisor_count_lower_bound_above D data.k data.x 4 3 data.q
      (2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael data.L : ℝ) * Real.log data.L))
      data.hk hretainedCount
  have hsize :
    2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael data.L : ℝ) * Real.log data.L) <
      P.card :=
    hPcard
  refine ⟨data.L, data.k, P, data.hL, data.hlambda, data.hcoprime, ?_, hsize⟩
  intro p hp
  rcases hP p hp with ⟨hpPrime, hpx, hpm, hqp, d, hdD, hpeq⟩
  have hCq : C ≤ data.q := le_trans (Nat.le_max_left C (W.sup id)) data.hCq
  have hpC : C < p := lt_of_le_of_lt hCq hqp
  have hnot : ¬p ∣ data.L := by
    intro hpL
    exact Nat.not_le_of_gt hqp (data.hfactor p hpL hpPrime)
  have hpcop : Nat.Coprime p data.L := (Nat.Prime.coprime_iff_not_dvd hpPrime).2 hnot
  have hpAvoid : ∀ b ∈ W, ¬p ∣ b := by
    intro b hb hpdiv
    have hpb : p ≤ b := Nat.le_of_dvd (hWpos b hb) hpdiv
    have hbW : b ≤ W.sup id := Finset.le_sup (f := id) hb
    have hbq : b ≤ data.q := le_trans hbW (le_trans (Nat.le_max_right C (W.sup id)) data.hCq)
    exact Nat.not_le_of_gt hqp (le_trans hpb hbq)
  have hd' := (mem_restrictedDivisors hL).mp hdD
  exact ⟨hpPrime, hpcop, ⟨d, hd'.1, hpeq⟩, hpm, hpC, hpAvoid⟩

end PseudoPrime.AnalyticNumberTheory.AGP
