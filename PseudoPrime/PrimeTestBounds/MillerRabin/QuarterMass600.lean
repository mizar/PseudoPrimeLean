/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterIdentity576
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCommonEuler576
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerRecovery94

/-! # Sharp sixth-pole zero mass through logarithmic cutoff 600 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For radii 292 through 300, the three pair characters of a passing uniform
Korselt triple retain the sharp Euler and Gamma recovery and the identity-prime saving. -/
theorem common_triple_mass_upper_600 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 292 ≤ R)
    (hU : R ≤ 300) (hL : Real.log n = 2 * R) (hP : R ^ 4 < p) (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb : ∀ b : ℕ, b.Prime → (b : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)
    quarterMass570 a + quarterMass570 b + quarterMass570 c <
      3 / 4 * R - 134154 / 10000 + 4 * positiveTail570 (R ^ 2) -
        (if R ≤ 299 then 0.02169 else 0.02179) := by
  intro a b c
  have hcut : Real.exp (5 / 2) ≤ R ^ 2 := by
    have hh := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by decide : 3 ≠ 0)
    rw [← Real.exp_natCast_mul] at hh
    norm_num only [Nat.cast_ofNat, mul_one] at hh
    exact
      (Real.exp_le_exp.mpr (by norm_num only : (5 / 2 : ℝ) ≤ 3)).trans
        (hh.le.trans
          (le_trans (b := (292 : ℝ) ^ 2) (by norm_num only)
            (pow_le_pow_left₀ (by norm_num only) hR 2)))
  have hsave :=
    identity_euler_saving_600 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hGRH.riemann hP hQ
      hT (fun l hl h => hb l hl (((Nat.le_floor_iff (Real.exp_pos _).le).mp h).trans hcut))
  have d₁ : p * q ∣ n := he ▸ dvd_mul_right _ _
  have d₂ : p * r ∣ n := by
    rw [he, mul_right_comm]; exact dvd_mul_right _ _
  have d₃ : q * r ∣ n := by
    rw [he, Nat.mul_assoc]; exact dvd_mul_left _ _
  have pa := pair_character_primitive hs d₁ (hp.mul hq)
  have pb := pair_character_primitive hs d₂ (hp.mul hr)
  have pc := pair_character_primitive hs d₃ (hq.mul hr)
  have bound (i j : ℕ) [Fact i.Prime] [Fact j.Prime] : 1 < i * j :=
    (Fact.out : i.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)
  have na := pair_character_ne_one hs d₁ (hp.mul hq) (bound p q)
  have nb := pair_character_ne_one hs d₂ (hp.mul hr) (bound p r)
  have nc := pair_character_ne_one hs d₃ (hq.mul hr) (bound q r)
  let s := Finset.Ioc 0 ⌊R ^ 2⌋₊
  have hS : ∀ k ∈ s, (k : ℝ) ≤ R ^ 2 := fun _ hk ↦
    (Nat.le_floor_iff (sq_nonneg R)).mp (Finset.mem_Ioc.mp hk).2
  have hx : 2701 ≤ R ^ 2 :=
    (by norm_num only : (2701 : ℝ) ≤ 292 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hR 2)
  have hy : R ^ 2 ≤ 1000000 :=
    (pow_le_pow_left₀ (by linarith only [hR]) hU 2).trans (by norm_num only)
  have htail := positive_tail_upper_570 hGRH.riemann hx hy
  have ea := pair_character_even_of_korselt hn ho hp hq hk hj hv
  have eb := pair_character_even_of_korselt hn ho hp hr hk hm hw
  have ec := pair_character_even_of_korselt hn ho hq hr hj hm (hw.trans hv.symm)
  have hmain :=
    mass_identity_series_of_recovery a b c (bound p q) (bound p r) (bound q r) (hGRH _ a pa)
      (hGRH _ b pb) (hGRH _ c pc) pa pb pc na nb nc (inv_ne_one.mpr na) (inv_ne_one.mpr nb)
      (inv_ne_one.mpr nc) s hS
      (fun l => by
        simpa only [a, b, c, Int.cast_natCast] using
          pair_character_sum_ge_neg_one (l : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr))
      (fun l hl h =>
        pair_character_nat_eq_one hn ho hp hq ((dvd_mul_right _ _).trans d₁)
          ((dvd_mul_left _ _).trans d₁) d₁ hk hj hv l (hb l hl h))
      (fun l hl h =>
        pair_character_nat_eq_one hn ho hp hr ((dvd_mul_right _ _).trans d₂)
          ((dvd_mul_left _ _).trans d₂) d₂ hk hm hw l (hb l hl h))
      (fun l hl h =>
        pair_character_nat_eq_one hn ho hq hr ((dvd_mul_right _ _).trans d₃)
          ((dvd_mul_left _ _).trans d₃) d₃ hj hm (hw.trans hv.symm) l (hb l hl h))
      (R := R)
      (by
        rw [pair_level_log_sum he, hL]; linarith only)
      (section99_euler_recovery ea eb ec) htail
  exact hmain.trans_lt (sub_lt_sub_left hsave _)

end PseudoPrime.PrimeTestBounds.MillerRabin
