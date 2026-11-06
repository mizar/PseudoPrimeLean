/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeFactorLocalEnvelope

/-! # Local correction certificates for the 0.30 target -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational radii, strict correction lower bounds and logarithm scales for
the eight local intervals from scale 15 to 39.4. These anchors are consumed
by the local witness theorem after their correction checks are verified. -/
def target030Anchors : List (ℚ × ℚ × ℕ) :=
  [(8, 324969 / 100000, 3), (12, 193673 / 50000, 4), (16, 85669 / 20000, 4),
    (19, 452097 / 100000, 5), (20, 5739 / 1250, 5), (21, 465779 / 100000, 5),
    (107 / 5, 9367 / 2000, 5), (43 / 2, 93797 / 20000, 5)]

set_option maxRecDepth 8192 in
/-- Each local correction exceeds its rational anchor. Kernel evaluation
checks an additional positive margin using the existing logarithm certificates. -/
theorem target030Anchors_checked :
    target030Anchors.all (fun x ↦ localCorrectionCheck x.1 (x.2.1 + 1 / 10000000) x.2.2) =
      true := by
  decide +kernel

/-- A listed correction is strictly below the even endpoint correction at its
radius. The checked positive margin converts the rational certificate to a
strict real inequality for the local witness theorem. -/
theorem target030Anchor_lt {b d : ℚ} {j : ℕ} (hm : (b, d, j) ∈ target030Anchors) :
    (d : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (b : ℝ) := by
  have hc := (List.all_eq_true.mp target030Anchors_checked) (b, d, j) hm
  have h := localCorrectionCheck_sound hc
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  linarith only [h]

/-- Under GRH, any listed anchor bounds a rejecting prime when all passing
residues belong to a proper subgroup at a divisor with logarithm at most `s`.
The finite certificate supplies the hypotheses of the local shift theorem. -/
theorem exists_prime_reject_target030_anchor {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b d : ℚ} {j : ℕ}
    (hm : (b, d, j) ∈ target030Anchors) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (max (b : ℝ) (s - d)) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hc := (List.all_eq_true.mp target030Anchors_checked) (b, d, j) hm
  have hbq : (8 : ℚ) ≤ b := (of_decide_eq_true hc).1
  have hb : (8 : ℝ) ≤ b := by exact_mod_cast hbq
  exact exists_prime_reject_of_local_shift hn ho hqn H hH hpass hGRH hb (target030Anchor_lt hm) hs

/-- Every scale from 15 through 39.4 admits a certified anchor whose radius
and correction fit the 0.30 local budget. The eight closed intervals cover
both endpoints and meet at their exact rational boundaries. -/
theorem target030_anchor_cover (L : ℝ) (hL : 15 ≤ L) (hU : L ≤ 197 / 5) :
    ∃ b d : ℚ,
      ∃ j : ℕ,
        (b, d, j) ∈ target030Anchors ∧
          (b : ℝ) ≤ (5477 / 10000 : ℝ) * L ∧ (2 / 3 - 5477 / 10000 : ℝ) * L ≤ d := by
  by_cases h0 : L ≤ (974907 / 35690 : ℝ)
  · refine ⟨8, 324969 / 100000, 3, by decide +kernel, ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h0]
  · by_cases h1 : L ≤ (581019 / 17845 : ℝ)
    · refine ⟨12, 193673 / 50000, 4, by decide +kernel, ?_, ?_⟩
      all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
      all_goals linarith only [hL, hU, h0, h1]
    · by_cases h2 : L ≤ (257007 / 7138 : ℝ)
      · refine ⟨16, 85669 / 20000, 4, by decide +kernel, ?_, ?_⟩
        all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
        all_goals linarith only [hL, hU, h0, h1, h2]
      · by_cases h3 : L ≤ (1356291 / 35690 : ℝ)
        · refine ⟨19, 452097 / 100000, 5, by decide +kernel, ?_, ?_⟩
          all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
          all_goals linarith only [hL, hU, h0, h1, h2, h3]
        · by_cases h4 : L ≤ (137736 / 3569 : ℝ)
          · refine ⟨20, 5739 / 1250, 5, by decide +kernel, ?_, ?_⟩
            all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
            all_goals linarith only [hL, hU, h0, h1, h2, h3, h4]
          · by_cases h5 : L ≤ (1397337 / 35690 : ℝ)
            · refine ⟨21, 465779 / 100000, 5, by decide +kernel, ?_, ?_⟩
              all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
              all_goals linarith only [hL, hU, h0, h1, h2, h3, h4, h5]
            · by_cases h6 : L ≤ (140505 / 3569 : ℝ)
              · refine ⟨107 / 5, 9367 / 2000, 5, by decide +kernel, ?_, ?_⟩
                all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
                all_goals linarith only [hL, hU, h0, h1, h2, h3, h4, h5, h6]
              · refine ⟨43 / 2, 93797 / 20000, 5, by decide +kernel, ?_, ?_⟩
                all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
                all_goals linarith only [hL, hU, h0, h1, h2, h3, h4, h5, h6]

/-- Under GRH, a proper local subgroup at a divisor with logarithm at most
`2 log(n) / 3` gives a 0.30 rejecting prime on scales 15 through 39.4. The
eight certified anchors cover the interval and bound the shifted cutoff. -/
theorem exists_prime_reject_03_local_cover {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (15 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 197 / 5) (hq : Real.log q ≤ (2 / 3 : ℝ) * Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨b, d, j, hm, hb, hd⟩ := target030_anchor_cover (Real.log n) hL hU
  obtain ⟨p, hp, hpbound, hfail⟩ :=
    exists_prime_reject_target030_anchor hn ho hqn H hH hpass hGRH hm hq
  have hmax : max (b : ℝ) ((2 / 3 : ℝ) * Real.log n - d) ≤ (5477 / 10000 : ℝ) * Real.log n := by
    apply max_le hb
    linarith only [hd]
  have hc := (List.all_eq_true.mp target030Anchors_checked) (b, d, j) hm
  have hbq : (8 : ℚ) ≤ b := (of_decide_eq_true hc).1
  have hbR : (8 : ℝ) ≤ b := by exact_mod_cast hbq
  have hnonneg : 0 ≤ max (b : ℝ) ((2 / 3 : ℝ) * Real.log n - d) :=
    le_trans (by linarith only [hbR]) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hnonneg hmax
  have hLsq := sq_nonneg (Real.log n)
  have hfinal :
    (max (b : ℝ) ((2 / 3 : ℝ) * Real.log n - d)) ^ 2 ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
    nlinarith only [hsquare, hLsq]
  exact ⟨p, hp, hpbound.trans hfinal, hfail⟩

/-- A two-prime divisor of an odd input either contains the prime three or
provides a proper local subgroup at a divisor no larger than the product.
Repeated, non-Korselt, and equal or unequal two-adic cases supply the subgroup. -/
theorem prime_pair_local_data {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hd : p * q ∣ n) :
    3 ∣ n ∨
      ∃ s : ℕ,
        0 < s ∧
          s ∣ n ∧
          s ≤ p * q ∧
          ∃ H : Subgroup (ZMod s)ˣ,
            H ≠ ⊤ ∧
              ∀ a : ℕ,
                PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
                  ∃ u : (ZMod s)ˣ, u ∈ H ∧ (u : ZMod s) = (a : ZMod s) := by
  have hpn : p ∣ n := (dvd_mul_right p q).trans hd
  have hqn : q ∣ n := (dvd_mul_left q p).trans hd
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqn
  have hpOdd := hp.odd_of_ne_two hp2
  have hqOdd := hq.odd_of_ne_two hq2
  by_cases hp3 : p = 3
  · exact Or.inl (hp3 ▸ hpn)
  by_cases hq3 : q = 3
  · exact Or.inl (hq3 ▸ hqn)
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le hp2.symm⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le hq2.symm⟩
  let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  by_cases heq : p = q
  · subst q
    have hdiv : p ^ 2 ∣ n := by simpa only [pow_two] using hd
    have hi := PrimeTest.prime_le_local_square_powerKernel_index hn hp hp2 hdiv
    have hproper : (powMonoidHom (n - 1) : (ZMod (p * p))ˣ →* (ZMod (p * p))ˣ).ker ≠ ⊤ := by
      intro ht
      rw [pow_two, ht, Subgroup.index_top] at hi
      exact (not_le_of_gt hp.one_lt) hi
    exact
      Or.inr
        ⟨p * p, mul_pos hp.pos hp.pos, hd, le_rfl, _, hproper, fun a ha ↦
          PrimeTest.strongMR_local_divisorKernel hn ho hd ha⟩
  by_cases hpK : p - 1 ∣ n - 1
  · by_cases hqK : q - 1 ∣ n - 1
    · rcases lt_trichotomy (padicValNat 2 (p - 1)) (padicValNat 2 (q - 1)) with hv | hv | hv
      · exact
          Or.inr
            ⟨q, hq.pos, hqn, Nat.le_mul_of_pos_left q hp.pos, _,
              PrimeTest.local_half_powerKernel_ne_top hqOdd, fun a ha ↦
              PrimeTest.strongPass_mem_local_half_kernel_of_twoAdic_lt hn ho hqOdd hpOdd hqn hpn hv
                ha⟩
      · let E := 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2
        obtain ⟨kp, hkp, hEp⟩ :=
          PrimeTest.canonical_sign_exponent_local_half hp.one_lt hpOdd hn ho hpK
        obtain ⟨kq, hkq, hEq⟩ :=
          PrimeTest.canonical_sign_exponent_local_half hq.one_lt hqOdd hn ho hqK
        rw [← hv] at hEq
        have hproper :=
          PrimeTest.signSubgroup_pair_ne_top_of_local_half_odd hpOdd hqOdd heq hkp hkq hEp hEq
        refine Or.inr ⟨p * q, mul_pos hp.pos hq.pos, hd, le_rfl, _, hproper, ?_⟩
        intro a ha
        obtain ⟨u, hu, hua⟩ :=
          PrimeTest.strongMillerRabinPass_mem_signSubgroup hn ho ha hp hpOdd hpn
        refine ⟨ZMod.unitsMap hd u, PrimeTest.signSubgroup_unitsMap_mem hd u hu, ?_⟩
        rw [ZMod.unitsMap_val, hua, ZMod.cast_natCast hd]
      · exact
          Or.inr
            ⟨p, hp.pos, hpn, Nat.le_mul_of_pos_right p hq.pos, _,
              PrimeTest.local_half_powerKernel_ne_top hpOdd, fun a ha ↦
              PrimeTest.strongPass_mem_local_half_kernel_of_twoAdic_lt hn ho hpOdd hqOdd hpn hqn hv
                ha⟩
    · exact
        Or.inr
          ⟨q, hq.pos, hqn, Nat.le_mul_of_pos_left q hp.pos, _,
            NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hqK, fun a ha ↦
            PrimeTest.strongMR_local_primeKernel hn ho hqn ha⟩
  · exact
      Or.inr
        ⟨p, hp.pos, hpn, Nat.le_mul_of_pos_right p hq.pos, _,
          NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hpK, fun a ha ↦
          PrimeTest.strongMR_local_primeKernel hn ho hpn ha⟩

/-- Under GRH, every odd input with at least three prime factors counted with
multiplicity has a 0.30 rejecting prime for logarithmic scales 15 to 39.4.
The two least factors give the local modulus via their logarithmic mean. -/
theorem exists_prime_reject_03_three_factors {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hL : (15 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 197 / 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hk2 : 2 ≤ n.primeFactorsList.length := by
    change 2 ≤ ArithmeticFunction.cardFactors n
    exact le_trans (by norm_num only) hk
  obtain ⟨p, q, hp, hq, hd, hm⟩ :=
    NumberTheory.exists_prime_pair_log_mean (Nat.zero_lt_of_lt hn) hk2
  have hkR : (3 : ℝ) ≤ ArithmeticFunction.cardFactors n := Nat.cast_le.mpr hk
  have hkpos : (0 : ℝ) < ArithmeticFunction.cardFactors n := by linarith only [hkR]
  have hlog :
    Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) := by
    apply (le_div_iff₀ hkpos).mpr
    simpa only [ArithmeticFunction.cardFactors_apply, mul_comm] using hm
  have hratio : 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) ≤ 2 * Real.log n / 3 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg n))
      (by norm_num only) hkR
  rcases prime_pair_local_data hn ho hp hq hd with hthree | ⟨s, hs, hsn, hsp, H, hproper, hpass⟩
  · have hbound : (3 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
    exact
      ⟨3, Nat.prime_three, hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · let : NeZero s := ⟨Nat.ne_zero_of_lt hs⟩
    have hslog : Real.log s ≤ (2 / 3 : ℝ) * Real.log n := by
      have h :=
        (Real.log_le_log (Nat.cast_pos.mpr hs) (Nat.cast_le.mpr hsp)).trans (hlog.trans hratio)
      linarith only [h]
    exact exists_prime_reject_03_local_cover hn ho hsn H hproper hpass hGRH hL hU hslog

end PseudoPrime.PrimeTestBounds.MillerRabin
