/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitPowerKernelProperness
public import Mathlib.NumberTheory.CarmichaelNumber
public import PseudoPrime.NumberTheory.PrimeFactorPairBounds
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatIndexSize
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatKernel
public import PseudoPrime.PrimeTest.MillerRabin.SquareFactorLocalBounds
public import PseudoPrime.PrimeTest.MillerRabin.UnequalTwoAdicSquares
public import PseudoPrime.PrimeTest.MillerRabin.PairedLocalSign
public import PseudoPrime.PrimeTest.MillerRabin.KorseltCanonicalSign
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup

/-! # Coefficient-independent finite-index classification -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An arithmetic finite-index dichotomy for a subgroup of the Fermat subgroup.
Either a proper local subgroup receives every ambient strong-MR pass at a
divisor modulus whose square is at most `J * n`, or `n` is a squarefree
uniform Korselt triple. This classification does not use GRH or a witness
coefficient. -/
theorem localSubgroup_or_uniformKorseltTriple {n J : ℕ} [NeZero n] (hn1 : 1 < n) (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hJ : 1 ≤ J)
    (hJ3 : J ^ 3 ≤ n) (hi : H.index ≤ J) :
    (∃ q : ℕ,
        2 ≤ q ∧
          q ∣ n ∧
          q ^ 2 ≤ J * n ∧
          ∃ K : Subgroup (ZMod q)ˣ,
            K ≠ ⊤ ∧
              ∀ a : ℕ,
                PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
                  ∃ u : (ZMod q)ˣ, u ∈ K ∧ (u : ZMod q) = (a : ZMod q)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  by_cases hNon : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ¬p - 1 ∣ n - 1
  · obtain ⟨p, hp, hpn, hdiv⟩ := hNon
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, rfl⟩ := hpn
    have hmpos : 0 < m := by
      by_contra hnot
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hnot
      subst m
      simp only [mul_zero, Nat.not_lt_zero] at hn1
    have hmne : m ≠ 1 := by
      intro hm
      exact hdiv (by simpa only [hm, mul_one] using (dvd_refl (p - 1)))
    have hm1 : 1 < m := lt_of_le_of_ne (Nat.succ_le_of_lt hmpos) (Ne.symm hmne)
    have hlocalSize := PrimeTest.primeFactor_sq_le_powerKernel_index (p := p) hm1
    have hlocalIndex := PrimeTest.local_powerKernel_index_le_of_le_fermat (dvd_mul_right p m) H hH
    have hsize : p ^ 2 ≤ J * (p * m) := by
      exact hlocalSize.trans (Nat.mul_le_mul_right (p * m) (hlocalIndex.trans hi))
    let K := (powMonoidHom (p * m - 1) : (ZMod p)ˣ →* (ZMod p)ˣ).ker
    have hproper : K ≠ ⊤ := NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hdiv
    have hcontain :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass (p * m) (a : ZMod (p * m)) →
          ∃ u : (ZMod p)ˣ, u ∈ K ∧ (u : ZMod p) = (a : ZMod p) := by
      intro a ha
      exact PrimeTest.strongMR_local_primeKernel hn1 hnOdd (dvd_mul_right p m) ha
    exact Or.inl ⟨p, hp.two_le, dvd_mul_right p m, hsize, ⟨K, hproper, hcontain⟩⟩
  have hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
    intro p hp hpn
    exact Classical.byContradiction (fun h ↦ hNon ⟨p, hp, hpn, h⟩)
  by_cases hSq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hsq⟩ := hSq
    let : Fact p.Prime := ⟨hp⟩
    have hpn : p ∣ n := dvd_trans ⟨p, by rw [pow_two]⟩ hsq
    have hpOdd := hnOdd.ne_two_of_dvd_nat hpn
    have hlow := PrimeTest.prime_le_local_square_powerKernel_index hn1 hp hpOdd hsq
    have hup := PrimeTest.local_divisor_powerKernel_index_le_of_le_fermat hsq H hH
    have hpJ : p ≤ J := hlow.trans (hup.trans hi)
    have hfourth : p ^ 4 ≤ J ^ 4 := Nat.pow_le_pow_left hpJ 4
    have hJfourth : J ^ 4 ≤ J * n := by
      calc
        J ^ 4 = J * J ^ 3 := by
          rw [pow_succ]; ring
        _ ≤ J * n := Nat.mul_le_mul_left J hJ3
    have hsize : (p ^ 2) ^ 2 ≤ J * n := by
      rw [← pow_mul]
      exact hfourth.trans hJfourth
    let K := (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
    have hproper : K ≠ ⊤ := by
      intro ht
      change p ≤ K.index at hlow
      rw [ht, Subgroup.index_top] at hlow
      exact (not_le_of_gt hp.one_lt) hlow
    have hcontain :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod (p ^ 2))ˣ, u ∈ K ∧ (u : ZMod (p ^ 2)) = (a : ZMod (p ^ 2)) := by
      intro a ha
      exact PrimeTest.strongMR_local_divisorKernel hn1 hnOdd hsq ha
    exact
      Or.inl
        ⟨p ^ 2, hp.two_le.trans (Nat.le_self_pow (by decide : 2 ≠ 0) p), hsq, hsize,
          ⟨K, hproper, hcontain⟩⟩
  have hsf : Squarefree n :=
    Nat.squarefree_iff_prime_squarefree.mpr (fun p hp hsq ↦ hSq ⟨p, hp, (pow_two p).symm ▸ hsq⟩)
  by_cases hBad :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ∣ n ∧ q ∣ n ∧ padicValNat 2 (q - 1) < padicValNat 2 (p - 1)
  · obtain ⟨p, q, hp, hq, hpn, hqn, hv⟩ := hBad
    let : Fact p.Prime := ⟨hp⟩
    let : Fact q.Prime := ⟨hq⟩
    have hpOdd := hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn)
    have hqOdd := hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn)
    have hsize' := PrimeTest.prime_factor_square_le_of_korselt hn1 hcomp hpn (hK p hp hpn)
    have hsize : p ^ 2 ≤ J * n := by
      exact hsize'.trans (Nat.le_mul_of_pos_left n (Nat.succ_le_iff.mp hJ))
    let K := (powMonoidHom (p / 2) : (ZMod p)ˣ →* (ZMod p)ˣ).ker
    have hproper := PrimeTest.local_half_powerKernel_ne_top hpOdd
    have hcontain :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod p)ˣ, u ∈ K ∧ (u : ZMod p) = (a : ZMod p) := by
      intro a ha
      exact
        PrimeTest.strongPass_mem_local_half_kernel_of_twoAdic_lt hn1 hnOdd hpOdd hqOdd hpn hqn hv ha
    exact Or.inl ⟨p, hp.two_le, hpn, hsize, ⟨K, hproper, hcontain⟩⟩
  have hU :
    ∀ p q : ℕ,
      p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
    intro p q hp hq hpn hqn
    exact
      le_antisymm (le_of_not_gt (fun h ↦ hBad ⟨p, q, hp, hq, hpn, hqn, h⟩))
        (le_of_not_gt (fun h ↦ hBad ⟨q, p, hq, hp, hqn, hpn, h⟩))
  by_cases hFour : 4 ≤ n.primeFactors.card
  · obtain ⟨p, q, hp, hq, hpq, hpqn, hsize'⟩ :=
      NumberTheory.exists_prime_pair_modulus_square_le (Nat.zero_lt_of_lt hn1) hFour
    let : Fact p.Prime := ⟨hp⟩
    let : Fact q.Prime := ⟨hq⟩
    let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
    have hpn : p ∣ n := (dvd_mul_right p q).trans hpqn
    have hqn : q ∣ n := (dvd_mul_left q p).trans hpqn
    have hpOdd := hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn)
    have hqOdd := hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn)
    let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (hnOdd.ne_two_of_dvd_nat hpn).symm⟩
    let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (hnOdd.ne_two_of_dvd_nat hqn).symm⟩
    let E := 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2
    obtain ⟨kp, hkp, hEp⟩ :=
      PrimeTest.canonical_sign_exponent_local_half hp.one_lt hpOdd hn1 hnOdd (hK p hp hpn)
    obtain ⟨kq, hkq, hEq⟩ :=
      PrimeTest.canonical_sign_exponent_local_half hq.one_lt hqOdd hn1 hnOdd (hK q hq hqn)
    rw [hU q p hq hp hqn hpn] at hEq
    have hproper :=
      PrimeTest.signSubgroup_pair_ne_top_of_local_half_odd hpOdd hqOdd hpq hkp hkq hEp hEq
    have hcontain :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ v : (ZMod (p * q))ˣ,
            v ∈ PrimeTest.signSubgroup (p * q) E ∧ (v : ZMod (p * q)) = (a : ZMod (p * q)) := by
      intro a ha
      obtain ⟨u, hu, hua⟩ :=
        PrimeTest.strongMillerRabinPass_mem_signSubgroup hn1 hnOdd ha hp hpOdd hpn
      refine ⟨ZMod.unitsMap hpqn u, PrimeTest.signSubgroup_unitsMap_mem hpqn u hu, ?_⟩
      rw [ZMod.unitsMap_val, hua, ZMod.cast_natCast hpqn]
    have hsize : (p * q) ^ 2 ≤ J * n := by
      exact hsize'.trans (Nat.le_mul_of_pos_left n (Nat.succ_le_iff.mp hJ))
    exact
      Or.inl
        ⟨p * q, hp.two_le.trans (Nat.le_mul_of_pos_right p hq.pos), hpqn, hsize,
          ⟨PrimeTest.signSubgroup (p * q) E, hproper, hcontain⟩⟩
  have hn2 : 2 < n := by
    by_contra hnot
    have hnle : n ≤ 2 := Nat.le_of_not_gt hnot
    have heq : n = 2 := le_antisymm hnle (Nat.succ_le_iff.mpr hn1)
    subst n
    exact (by decide : ¬Odd 2) hnOdd
  have hC := Nat.isCarmichael_iff_korselt.mpr ⟨hn2, hcomp, hsf, hK⟩
  have hc3 : n.primeFactors.card = 3 :=
    le_antisymm (Nat.le_of_lt_succ (lt_of_not_ge hFour)) hC.three_le_card_primeFactors
  exact Or.inr ⟨hsf, hc3, hK, hU⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
