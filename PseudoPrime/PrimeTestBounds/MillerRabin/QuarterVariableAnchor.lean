/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformLow

/-! # Variable local anchors for quarter-square witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A certified even-character local anchor gives a quarter-square witness
when its correction covers the upper scale and prime rounding covers the
initial radius. The local modulus may be any divisor carrying a proper
subgroup containing every passing residue. -/
theorem quarter_variable_anchor {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b d P : ℝ} (hb : 8 ≤ b)
    (hd : d < LLS.PaperStatements.fullEndpointEvenGapCorrection b) (hdb : b / 3 ≤ d)
    (hU : Real.log n ≤ 6 * d) (hq : Real.log q ≤ (2 / 3 : ℝ) * Real.log n)
    (hP : P ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hround : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b ^ 2 → (p : ℝ) ≤ P) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hbound, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hH hpass hGRH hb hd hq
  have hnonneg : (0 : ℝ) ≤ max b ((2 / 3 : ℝ) * Real.log n - d) :=
    (by linarith only [hb] : 0 ≤ b).trans (le_max_left _ _)
  by_cases hsmall : Real.log n ≤ 2 * b
  · have hm : max b ((2 / 3 : ℝ) * Real.log n - d) ≤ b := by
      apply max_le le_rfl
      linarith only [hsmall, hdb]
    have hs := pow_le_pow_left₀ hnonneg hm 2
    exact ⟨p, hp, (hround p hp (hbound.trans hs)).trans hP, hf⟩
  · have hm : max b ((2 / 3 : ℝ) * Real.log n - d) ≤ Real.log n / 2 := by
      apply max_le
      · linarith only [hsmall]
      · linarith only [hU]
    have hs := pow_le_pow_left₀ hnonneg hm 2
    have hp : (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hbound, hs]
    exact ⟨p, ‹p.Prime›, hp, hf⟩

/-- For an odd input with at least three prime factors, a certified variable
anchor supplies a quarter-square witness. The two smallest factors give the
local modulus with logarithm at most two thirds of the input scale. -/
theorem quarter_three_variable {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hL : (8 : ℝ) ≤ Real.log n) {b d P : ℝ} (hb : 8 ≤ b)
    (hd : d < LLS.PaperStatements.fullEndpointEvenGapCorrection b) (hdb : b / 3 ≤ d)
    (hU : Real.log n ≤ 6 * d) (hP : P ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hround : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b ^ 2 → (p : ℝ) ≤ P) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hk2 : 2 ≤ n.primeFactorsList.length := by
    change 2 ≤ ArithmeticFunction.cardFactors n
    exact le_trans (by norm_num only) hk
  obtain ⟨p, q, hp, hq, hdivpair, hm⟩ :=
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
  rcases prime_pair_local_data hn ho hp hq hdivpair with hthree |
    ⟨s, hs, hsn, hsp, H, hproper, hpass⟩
  · have hbound : (3 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
    exact
      ⟨3, Nat.prime_three, hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · let : NeZero s := ⟨Nat.ne_zero_of_lt hs⟩
    have hslog : Real.log s ≤ (2 / 3 : ℝ) * Real.log n := by
      have h :=
        (Real.log_le_log (Nat.cast_pos.mpr hs) (Nat.cast_le.mpr hsp)).trans (hlog.trans hratio)
      linarith only [h]
    exact quarter_variable_anchor hn ho hsn H hproper hpass hGRH hb hd hdb hU hslog hP hround

/-- A uniform Korselt triple satisfies the factor-count premise for the
variable-anchor witness. The remaining assumptions are scalar and rounding
certificates for the selected anchor. -/
theorem quarter_uniform_variable {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    {b d P : ℝ} (hb : 8 ≤ b) (hd : d < LLS.PaperStatements.fullEndpointEvenGapCorrection b)
    (hdb : b / 3 ≤ d) (hU : Real.log n ≤ 6 * d) (hP : P ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hround : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b ^ 2 → (p : ℝ) ≤ P) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hlist : n.primeFactorsList.Nodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList (Nat.ne_zero_of_lt hn)).mp hu.1
  have heq : n.primeFactors.card = ArithmeticFunction.cardFactors n := by
    change n.primeFactorsList.toFinset.card = n.primeFactorsList.length
    exact List.toFinset_card_of_nodup hlist
  have hk : 3 ≤ ArithmeticFunction.cardFactors n := by rw [← heq, hu.2.1]
  exact quarter_three_variable hn ho hGRH hk hL hb hd hdb hU hP hround

end PseudoPrime.PrimeTestBounds.MillerRabin
