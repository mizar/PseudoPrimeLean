/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgePrincipal663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeConductor663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeGamma663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflect663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgePowers663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeReflect663

/-! # First quarter-square bridge comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The three bridge cells contradict common prime passage under GRH. -/
theorem quarter_bridge_all_false {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) : False := by
  have hwide : r ∈ Set.Icc 328 332 := ⟨hr.1, hr.2.trans (by norm_num only)⟩
  have hfull := hr
  have h1 : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have h0 := zero_lt_one.trans_le h1
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ h1
  have hGm := quarter_gamma_bridge_663 hwide
  let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hd (n : ℕ) : 0 ≤ d n ∧ d n ≤ 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hB : (103684 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (103684 : ℝ) ≤ (328 : ℝ) ^ 2).trans
      (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hprefix (n : ℕ) (hn : n ∈ Finset.Ioc 0 103684) (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) :
    d n = 0 := by
    have hn' : (n : ℝ) ≤ 103684 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hnX := hn'.trans hB
    simp only [d,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero a hpa hnX hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero b hpb hnX hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero c hpc hnX hΛ,
      Complex.one_re]
    norm_num only
  have hlog : 7 ≤ 2 * Real.log r := by
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 4) (hi := 6)
          (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat] at hl
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hwide' : r ∈ Set.Icc 328 (1329 / 4) := ⟨hwide.1, hwide.2.trans (by norm_num only)⟩
  have haux :=
    (quarter_reflect_lower_box_663 hwide' hlog).trans
      (quarter_reflection_tail_663 hG.riemann (by norm_num only) (by norm_num only) d hd hprefix h0
        hlog)
  have hshift := quarter_shift_mix_663 ha hb hc hG.riemann hr.1 hL
  have hz := (abs_le.mp (quarter_shift_xi_cap_663 hG.riemann hr.1)).1
  have hm :=
    (quarter_main_reflect_cap_656 a b c hG.riemann ((by norm_num only : (322 : ℝ) ≤ 328).trans hr.1)
          (B := 103684) (by norm_num only) (by norm_num only) (by exact_mod_cast hB) ht hpa hpb
          hpc).trans
      (quarter_main_reflect_box_663 hwide')
  have hE := quarter_bridge_reflect_credit hfull
  have hW := quarter_bridge_weight_one_lower hfull
  have hw : 0 ≤ quarterWeight656 (r ^ 2) 1 := by
    have hlog₀ := Real.log_nonneg hx
    unfold quarterWeight656
    simp only [Real.sqrt_one, one_div, inv_one, one_mul, Real.log_inv, sub_neg_eq_add]
    positivity
  have hlogπ :=
    mul_le_mul_of_nonneg_right
      (show 3 * Real.log (2 * Real.pi) ≤ 5.517 by linarith only [Analysis.log_two_mul_pi_lt]) hw
  dsimp only [d] at haux
  ring_nf at hGm hshift hz haux hm hlogπ
  have hC := quarter_bridge_conductor_lower hfull
  have compare (K : Finset ℕ) (hcut : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) {B D P : ℝ}
    (hB : B ≤ 4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2))
    (hD : D ≤ (if r ≤ 329 then -14.645555 else if r ≤ 330 then -14.670133 else -14.711643))
    (hP : P ≤ ∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n))
    (hnum :
      0 <
        B + D + P + 14.55079583 - 0.001384 - 0.003335 + 0.07137 + 0.009446 - 0.000242 +
          0.163 * 0.001228) :
    False := by
    have hu :=
      quarter_scaled_comparison_upper ha hb hc hp hq hk hG
        ⟨hwide.1, hwide.2.trans (by norm_num only)⟩ hL ht hpa hpb hpc K hcut hU hpow
    dsimp only at hu
    rw [ite_eq_left hfull.2] at hu
    have hl := quarter_bridge_principal_lower hG.riemann hfull hB
    have hC' := hD.trans hC
    dsimp only at hl
    ring_nf at hu hl hC' hP hnum hE hW
    linarith only [hu, hl, hC', hGm, hP, hshift, hz, haux, hm, hE, hW, hlogπ, hnum]
  have hsupport (n : ℕ) (hn : n ∈ fixedPowers663) :=
    fixed_power_support_663 ⟨by linarith only [hr.1], hfull.2⟩ hn
  by_cases h₁ : r ≤ 329
  · exact
      compare fixedPowers663 (fun n hn ↦ (hsupport n hn).1) (fun n hn ↦ (hsupport n hn).2.le)
        (fun _ hn ↦ fixed_power_base_663 hn) (quarter_bridge_boundary_658 ⟨hr.1, h₁⟩)
        (by rw [ite_eq_left h₁]) (fixed_power_gain_663 hfull) (by norm_num only)
  by_cases h₂ : r ≤ 330
  · have hrow : r ∈ Set.Icc 329 330 := ⟨le_of_not_ge h₁, h₂⟩
    exact
      compare (fixedPowers656 true) (fun _ hn ↦ (quarter_bridge_power_support_660 hrow hn).1)
        (fun _ hn ↦ (quarter_bridge_power_support_660 hrow hn).2)
        (fun _ hn ↦ by
          obtain ⟨p, k, hp, _, hk, he⟩ := fixed_power_prime_base_656 true hn
          exact ⟨p, k, hp, hk, he⟩)
        (quarter_bridge_boundary_660 hrow) (by rw [ite_eq_right h₁, ite_eq_left h₂])
        (quarter_bridge_power_gain_660 hrow) (by norm_num only)
  · have hrow : r ∈ Set.Icc 330 (663 / 2) := ⟨le_of_not_ge h₂, hr.2⟩
    exact
      compare fixedPowers663 (fun n hn ↦ (hsupport n hn).1) (fun n hn ↦ (hsupport n hn).2.le)
        (fun _ hn ↦ fixed_power_base_663 hn) (quarter_bridge_boundary_663 hrow)
        (by rw [ite_eq_right h₁, ite_eq_right h₂]) (quarter_bridge_power_gain_663 hrow)
        (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
