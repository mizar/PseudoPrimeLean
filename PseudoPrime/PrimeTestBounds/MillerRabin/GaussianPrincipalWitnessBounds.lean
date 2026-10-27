/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRPrincipalNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessBounds

/-! # Gaussian MR witnesses from constant principal upper error -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive log n and Gaussian scale (32/105)log(n)², an index-at-least-four
subgroup cannot satisfy the actual fixed-cutoff comparison when its normalized
error is at most log(n)/800. Retain the conductor sum until bounding it by
(index-1)log(n), and use the certified actual denominator and strict rational margin. -/
private theorem gaussian_constant_principal_inequality_contradiction {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index) (hL : 0 < Real.log n) :
    let x := Analysis.gaussianMRScale (Real.log n)
    let R := (56 / 3 : ℝ) * x ^ (1 / 4 : ℝ) + 13 / 3 + LLS.PaperStatements.gaussianAmbientError n x
    R ≤ Real.log n / 800 →
      ¬(((H.index : ℝ) *
                (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                  (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
              Real.exp (1 / 16 : ℝ)) *
            Real.sqrt x ≤
          (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
            14 * (H.index : ℝ) * x ^ (1 / 4 : ℝ) +
            13 +
            ((H.index - 1 : ℕ) : ℝ) * (LLS.PaperStatements.gaussianAmbientError n x)) := by
  intro x R hR hcmp
  have hiR : (4 : ℝ) ≤ H.index := Nat.cast_le.mpr hi
  have hm : (0 : ℝ) < (H.index : ℝ) - 1 := by linarith only [hiR]
  have hcast : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    rw [Nat.cast_sub (le_trans (by decide : 1 ≤ 4) hi), Nat.cast_one]
  rw [hcast] at hcmp
  have hC := LLS.PaperStatements.subgroupConductorLogSum_le H
  have hCM := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hs := Real.sqrt_nonneg x
  have hr : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Analysis.gaussianMRScale_nonneg (Real.log n)) _
  have hd := LLS.gaussian_kernel_normalized_denominator_le_of_four_le_index hiR
  have he :
    (LLS.PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re = Real.exp (1 / 16 : ℝ) :=
    Analysis.gaussianGammaFunction_endpoint
  rw [he] at hd
  have hden := (le_div_iff₀ hm).mp hd
  have hleft :
    ((H.index : ℝ) - 1) * (21943 / 30000 : ℝ) * Real.sqrt x ≤
      ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x := by
    simpa only [mul_comm (21943 / 30000 : ℝ) ((H.index : ℝ) - 1)] using
      mul_le_mul_of_nonneg_right hden hs
  have hright :
    (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        14 * (H.index : ℝ) * x ^ (1 / 4 : ℝ) +
        13 +
        ((H.index : ℝ) - 1) * (LLS.PaperStatements.gaussianAmbientError n x) ≤
      ((H.index : ℝ) - 1) * ((161 / 400 : ℝ) * Real.log n + R) := by
    have hd :=
      mul_nonneg hr
        (show 0 ≤ (56 / 3 : ℝ) * ((H.index : ℝ) - 1) - 14 * (H.index : ℝ) by linarith only [hiR])
    dsimp only [R]
    have hc : 0 ≤ (13 / 3 : ℝ) * ((H.index : ℝ) - 1) - 13 := by linarith only [hiR]
    nlinarith only [hCM, hd, hc]
  have hstrict := mul_lt_mul_of_pos_left (Analysis.gaussianMR_main_term_lt hL hR) hm
  rw [← mul_assoc] at hstrict
  exact (not_lt_of_ge (hleft.trans (hcmp.trans hright))) hstrict

/-- Under GRH for odd n with log n≥130000000, a subgroup of index at least four
containing every strong pass gives a prime failing base at most (16/25)log(n)².
The logarithmic cutoff certifies the actual Gaussian scale and all
error budgets. Universal prime-base passage would contradict the actual comparison. -/
theorem exists_prime_witness_le_gaussian_principal_of_index_ge_four {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 130000000 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  have hpos : 0 < Real.log n := (by norm_num only : (0 : ℝ) < 130000000).trans_le hL
  have hlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (NeZero.pos n) : (0 : ℝ) < n)
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, hlog]
  by_contra hnone
  let x := Analysis.gaussianMRScale (Real.log n)
  have hx : 4 ≤ x :=
    (by norm_num only : (4 : ℝ) ≤ 3 ^ 16).trans
      (Analysis.gaussianMRScale_ge_three_pow_sixteen_principal hL)
  have hcut : (21 / 10 : ℝ) * x = (16 / 25 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [x, Analysis.gaussianMRScale]
    ring
  have hpass :
    ∀ r : ℕ,
      r.Prime → (r : ℝ) ≤ (21 / 10 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    intro r hr hb
    rw [hcut] at hb
    by_contra hfail
    exact hnone ⟨r, hr, hb, hfail⟩
  have hcmp :=
    gaussian_inequality_of_prime_passes_constant_principal hnlarge hnOdd H hHpass hGRH hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hpass
  have hR := Analysis.gaussianMR_error_budget_principal hL (le_refl (Real.log n))
  exact gaussian_constant_principal_inequality_contradiction H hi hpos hR hcmp

/-- Under GRH, every odd composite log n≥130000000 has a prime strong
Miller--Rabin witness at most (16/25)log(n)². The arithmetic pass-containing
subgroup has index at least four; the threshold excludes the exceptional modulus 9.
Apply the actual Gaussian comparison and explicit numerical budget. No additional
subgroup, integral, zero-mass, or error hypothesis remains. -/
theorem exists_prime_witness_le_gaussian_principal {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 130000000 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, hlog]
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hn9 : n ≠ 9 := by
    intro h
    rw [h] at hnlarge
    exact (by decide : ¬20000 ≤ 9) hnlarge
  obtain ⟨H, hi, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_strongMillerRabinPass hn1 hnOdd hnComposite
      hn9
  exact exists_prime_witness_le_gaussian_principal_of_index_ge_four hnOdd H hi hHpass hGRH hL

/-- Under GRH for odd n with log n≥130000000, passage of the canonical strong test
for every prime base at most (16/25)log(n)² is equivalent to primality.
The composite direction uses the explicit Gaussian prime witness; the prime
direction restricts the existing log-squared criterion to the smaller cutoff.
The same logarithmic threshold applies to both directions. -/
theorem prime_iff_millerRabin_for_all_primes_le_gaussian_principal {n : ℕ} (hnOdd : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 130000000 ≤ Real.log n) :
    (∀ r : ℕ,
        r.Prime →
          (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (r : ZMod n)) ↔
      n.Prime := by
  constructor
  · intro hpass
    by_contra hComposite
    obtain ⟨r, hr, hb, hfail⟩ := exists_prime_witness_le_gaussian_principal hnOdd hComposite hGRH hL
    exact hfail (hpass r hr hb)
  · intro hp r hr hb
    have hn1 : 1 < n := hp.one_lt
    have hcap : (16 / 25 : ℝ) * (Real.log n) ^ 2 ≤ (Real.log n) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (by norm_num only)
    exact
      (prime_iff_millerRabin_for_all_primes_le_log_sq hGRH hn1 hnOdd).mpr hp r hr (hb.trans hcap)

end PseudoPrime.PrimeTestBounds.MillerRabin
