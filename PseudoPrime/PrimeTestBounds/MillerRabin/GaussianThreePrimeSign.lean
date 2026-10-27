/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.PairedQuadraticAnnihilator
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianConductorBranch

/-! # Gaussian three-prime common-sign subgroup witnesses

Construct the actual paired quadratic annihilator characters internally.
The remaining arithmetic premises concern the common sign exponent, index
and strong-pass containment, rather than supplied character classifications.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a three-prime modulus at the explicit Gaussian threshold, the actual
common-sign subgroup gives coefficient 282924/1000000 when its exponent is an odd
multiple of each local half exponent, its index is four and it contains all
strong passes. Construct the three annihilator characters and their conductors;
no character enumeration or conductor-saving hypothesis is supplied externally.
Canonical exponent arithmetic and branch classification remain explicit inputs. -/
theorem exists_prime_witness_le_gaussian_0283_of_three_prime_sign_subgroup {n p q r E kp kq kr : ℕ}
    [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hnOdd : Odd n) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpn : p ∣ n)
    (hqn : q ∣ n) (hrn : r ∣ n) (hkp : Odd kp) (hkq : Odd kq) (hkr : Odd kr)
    (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq) (hEr : E = (r / 2) * kr) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hi : (PrimeTest.signSubgroup n E).index = 4)
    (hpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n E ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 434782608696 ≤ n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨a, ha⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hqOdd hpn hqn hkp hkq hEp hEq hpq
  obtain ⟨b, hb⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hrOdd hpn hrn hkp hkr hEp hEr hpr
  obtain ⟨c, hc⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hqOdd hrOdd hqn hrn hkq hkr hEq hEr hqr
  exact
    exists_prime_witness_le_gaussian_0283_of_three_annihilator_members hnOdd
      (PrimeTest.signSubgroup n E) hi hpass hGRH a b c ha hb hc Fact.out Fact.out Fact.out hpq hpr
      hqr hn hN

/-- Under GRH at logarithmic scale `600`, a common-sign index-four subgroup
with three pairwise product conductors gives the classified Gaussian star
witness. The threshold only supplies the comparison's elementary size bound. -/
theorem exists_prime_witness_le_gaussian_star_of_three_prime_sign_subgroup {n p q r E kp kq kr : ℕ}
    [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (hpOdd : Odd p) (hqOdd : Odd q)
    (hrOdd : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n) (hkp : Odd kp) (hkq : Odd kq)
    (hkr : Odd kr) (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq) (hEr : E = (r / 2) * kr)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r)
    (hi : (PrimeTest.signSubgroup n E).index = 4)
    (hpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n E ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 600 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨a, ha⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hqOdd hpn hqn hkp hkq hEp hEq hpq
  obtain ⟨b, hb⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hrOdd hpn hrn hkp hkr hEp hEr hpr
  obtain ⟨c, hc⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hqOdd hrOdd hqn hrn hkq hkr hEq hEr hqr
  exact
    exists_prime_witness_le_gaussian_star_of_three_annihilator_prime_members hnlarge hnOdd
      (PrimeTest.signSubgroup n E) hpass hGRH hL hi a b c ha hb hc Fact.out Fact.out Fact.out hpq
      hpr hqr hn

/-- The common-sign subgroup and its three pairwise product conductors feed
the Gamma index-100 cutoff from logarithmic scale 330. -/
theorem exists_prime_witness_le_gammaIndex100_of_three_prime_sign_subgroup {n p q r E kp kq kr : ℕ}
    [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (hpOdd : Odd p) (hqOdd : Odd q)
    (hrOdd : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n) (hkp : Odd kp) (hkq : Odd kq)
    (hkr : Odd kr) (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq) (hEr : E = (r / 2) * kr)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r)
    (hi : (PrimeTest.signSubgroup n E).index = 4)
    (hpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n E ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨a, ha⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hqOdd hpn hqn hkp hkq hEp hEq hpq
  obtain ⟨b, hb⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hrOdd hpn hrn hkp hkr hEp hEr hpr
  obtain ⟨c, hc⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hqOdd hrOdd hqn hrn hkq hkr hEq hEr hqr
  exact
    exists_prime_witness_le_gammaIndex100_of_three_annihilator_prime_members hnlarge hnOdd
      (PrimeTest.signSubgroup n E) hpass hGRH hL hi a b c ha hb hc Fact.out Fact.out Fact.out hpq
      hpr hqr hn

/-- The same pairwise conductor construction feeds the 6/5 Gaussian witness
bound from logarithmic scale 500. -/
theorem exists_prime_witness_le_gaussian6fifths_of_three_prime_sign_subgroup
    {n p q r E kp kq kr : ℕ} [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (hpOdd : Odd p)
    (hqOdd : Odd q) (hrOdd : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n) (hkp : Odd kp)
    (hkq : Odd kq) (hkr : Odd kr) (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq)
    (hEr : E = (r / 2) * kr) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r)
    (hi : (PrimeTest.signSubgroup n E).index = 4)
    (hpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n E ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨a, ha⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hqOdd hpn hqn hkp hkq hEp hEq hpq
  obtain ⟨b, hb⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hrOdd hpn hrn hkp hkr hEp hEr hpr
  obtain ⟨c, hc⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hqOdd hrOdd hqn hrn hkq hkr hEq hEr hqr
  exact
    exists_prime_witness_le_gaussian6fifths_of_three_annihilator_prime_members hnlarge hnOdd
      (PrimeTest.signSubgroup n E) hpass hGRH hL hi a b c ha hb hc Fact.out Fact.out Fact.out hpq
      hpr hqr hn

end PseudoPrime.PrimeTestBounds.MillerRabin
