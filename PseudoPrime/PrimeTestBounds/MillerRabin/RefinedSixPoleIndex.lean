/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEndpoints
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularThresholdBounds

/-! # Finite-index reduction for the refined paper cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Positive natural numbers with `q² ≤ 10^16 n` satisfy the corresponding
logarithmic bound. Monotonicity and the logarithm product rule translate the
arithmetic modulus constraint into the local-witness scale. -/
theorem refined_log_local16 {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 16 * n) :
    Real.log q ≤ (Real.log n + 16 * Real.log 10) / 2 := by
  have h :=
    Real.log_le_log (sq_pos_of_pos (Nat.cast_pos.mpr hq : (0 : ℝ) < q))
      (by exact_mod_cast hsize : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 16 * n)
  rw [Real.log_pow,
    Real.log_mul (pow_ne_zero 16 (by norm_num only : (10 : ℝ) ≠ 0)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

/-- Under GRH, a proper local subgroup with `q² ≤ 10^16 n` gives a witness
within the paper cutoff for `log n ≥ 1000`. The radius-48 anchor and the
logarithmic modulus comparison are bounded by the paper's root lower bound. -/
theorem refined_local16_witness {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hq : 0 < q)
    (hqn : q ∣ n) (hsize : q ^ 2 ≤ 10 ^ 16 * n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hm : ((48 : ℚ), (579107 / 100000 : ℚ), 6) ∈ localEvenAnchors := by decide +kernel
  have hs := refined_log_local16 (Nat.zero_lt_of_lt hn) hq hsize
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_of_local_anchor hn ho hqn H hH hpass hGRH hm hs
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  have h10 := log_ten_lt_seven_thirds
  have hmax :
    max (48 : ℝ) ((Real.log n + 16 * Real.log 10) / 2 - 579107 / 100000) ≤
      (261 / 500 : ℝ) * Real.log n := by
    apply max_le
    · linarith only [hL]
    · linarith only [hL, h10]
  have hnonneg : 0 ≤ max (48 : ℝ) ((Real.log n + 16 * Real.log 10) / 2 - 579107 / 100000) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hnonneg hmax
  have hfinal :
    (max (48 : ℝ) ((Real.log n + 16 * Real.log 10) / 2 - 579107 / 100000)) ^ 2 ≤
      ((261 / 500 : ℝ) * Real.log n) ^ 2 := by
    nlinarith only [hsquare]
  exact ⟨p, hp, (hb.trans hfinal).trans (refined_piecewise_radius_lower hL), hf⟩

/-- Under GRH, every odd composite with `log n ≥ 1000` and Fermat subgroup
index at most `10^16` has a rejecting prime within the paper cutoff. The
finite-index classification yields either a local modulus covered above or a
uniform Korselt triple covered by the certified three-prime witness. -/
theorem refined_index16_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 16)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hJ : (1 : ℕ) ≤ 10 ^ 16 := by norm_num only
  have h48 : 10 ^ 48 ≤ n :=
    decimal_le_of_log_upper (A := 48) (Nat.zero_lt_of_lt hn)
      (by
        norm_num only; linarith only [hL])
  have hJ3 : (10 ^ 16 : ℕ) ^ 3 ≤ n := by simpa only [← pow_mul, Nat.reduceMul] using h48
  rcases
    localSubgroup_or_uniformKorseltTriple hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hJ hJ3
      hi with
    hlocal | htriple
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    exact
      refined_local16_witness hn ho (lt_of_lt_of_le (by decide : 0 < 2) hq) hqn hsize K hproper
        hpass hGRH hL
  · exact refined_uniform_certified_witness hn ho htriple hGRH hL

/-- Under GRH, the piecewise bound holds when `log n ≥ 8` and either the low
branch applies or the Fermat subgroup index is at most `10^16`. Combine the
existing low-range theorem with the finite-index reduction above. -/
theorem refined_piecewise_index16 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hcover : Real.log n < 1000 ∨ (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 16) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hsmall : Real.log n < 1000
  · exact refined_piecewise_low_witness hn ho hc hGRH hL hsmall
  · exact refined_index16_witness hn ho hc (hcover.resolve_left hsmall) hGRH (le_of_not_gt hsmall)

end PseudoPrime.PrimeTestBounds.MillerRabin
