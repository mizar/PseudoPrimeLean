/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusResidual
public import PseudoPrime.LLS.GaussianPrefixSurplus

/-! # Gaussian surplus prefix witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an index-four subgroup yields an actual rejecting prime under the
35000-prefix clipped Gaussian cutoff. The rational residual certificate supplies
the strict inequality without an assumed profile entrance. -/
theorem jointSurplus_four35000 {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 130 30 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r := jointSurplusRadius 130 30 (Real.log n)
  have hr : (130 : ℝ) ≤ r := le_max_left _ _
  have hbudget :=
    jointSurplus_budget (rho := 130) (R := 30) (L := Real.log n) (by norm_num only)
      (by norm_num only) (Real.log_natCast_nonneg n)
  change
    (20115621 / 25000000 : ℝ) * Real.log n + 30 + (28794111 / 12500000 : ℝ) * Real.sqrt r ≤
      (10971611 / 5000000 : ℝ) * r at hbudget
  have hcert := jointSurplus_cert35000
  have hres :=
    jointSurplus_residual_lt (n := n) (P := 554117 / 100000) (R := 30) (rho := 130) (t := 11 / 20)
      (r := r) (by norm_num only) hr (by norm_num only) hcert.2.2 hbudget hcert.1 hcert.2.1
  have hprefix :
    (554117 / 100000 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 35000, Analysis.gaussianResolventMangoldtWeight j := by
    simpa only [Nat.floor_ofNat] using
      LLS.gaussian_prefix35000_surplus hGRH.riemann (le_refl (35000 : ℝ))
  have hcut : (35000 : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 := by nlinarith only [hr]
  exact jointSurplus_witness_four hnOdd hnlarge H hi hHpass hGRH hC hr hprefix hcut hbudget hres

/-- Under GRH, the 50000-prefix clipped Gaussian cutoff gives the corresponding
index-four rejecting prime. The stronger prefix pays for the smaller residual. -/
theorem jointSurplus_four50000 {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 155 29 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r := jointSurplusRadius 155 29 (Real.log n)
  have hr : (155 : ℝ) ≤ r := le_max_left _ _
  have hbudget :=
    jointSurplus_budget (rho := 155) (R := 29) (L := Real.log n) (by norm_num only)
      (by norm_num only) (Real.log_natCast_nonneg n)
  change
    (20115621 / 25000000 : ℝ) * Real.log n + 29 + (28794111 / 12500000 : ℝ) * Real.sqrt r ≤
      (10971611 / 5000000 : ℝ) * r at hbudget
  have hcert := jointSurplus_cert50000
  have hres :=
    jointSurplus_residual_lt (n := n) (P := 1129059 / 200000) (R := 29) (rho := 155) (t := 8 / 15)
      (r := r) (by norm_num only) hr (by norm_num only) hcert.2.2 hbudget hcert.1 hcert.2.1
  have hprefix :
    (1129059 / 200000 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 50000, Analysis.gaussianResolventMangoldtWeight j := by
    simpa only [Nat.floor_ofNat] using
      LLS.gaussian_prefix50000_surplus hGRH.riemann (le_refl (50000 : ℝ))
  have hcut : (50000 : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 := by nlinarith only [hr]
  exact
    jointSurplus_witness_four hnOdd hnlarge H hi hHpass hGRH hC (by linarith only [hr]) hprefix hcut
      hbudget hres

/-- Transfer any index-four witness cutoff to a squarefree uniform Korselt
three-factor input. The existing subgroup construction supplies the conductor bound. -/
theorem jointSurplus_transfer_three {n : ℕ} [NeZero n] (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    {X : ℝ}
    (hfour :
      ∀ H : Subgroup (ZMod n)ˣ,
        H.index = 4 →
          (∀ z : ZMod n,
            PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) →
          LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n →
          ∃ s : ℕ, s.Prime ∧ (s : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n)) :
    ∃ s : ℕ, s.Prime ∧ (s : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hc
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn)
  exact hfour H hi hpass hC.le

/-- Under GRH, the 35000-prefix cutoff yields a rejecting prime in the uniform
three-factor case. Apply the shared subgroup transfer to the index-four witness. -/
theorem jointSurplus_three35000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 130 30 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  apply jointSurplus_transfer_three ho hsf hc hK hU
  intro H hi hpass hC
  exact jointSurplus_four35000 ho hnlarge H hi hpass hGRH hC

/-- Under GRH, the 50000-prefix cutoff yields a rejecting prime in the uniform
three-factor case through the same subgroup transfer. -/
theorem jointSurplus_three50000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 155 29 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  apply jointSurplus_transfer_three ho hsf hc hK hU
  intro H hi hpass hC
  exact jointSurplus_four50000 ho hnlarge H hi hpass hGRH hC

end PseudoPrime.PrimeTestBounds.MillerRabin
