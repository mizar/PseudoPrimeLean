/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRNumerics
public import PseudoPrime.LLS.GaussianKernelCoefficientBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaWitnessBounds

/-! # Gaussian coefficient 0.64 strong Miller--Rabin witnesses

The actual Gaussian subgroup comparison and kernel-certified error budget give
prime witnesses below (16/25)log(n)² for every odd composite n≥10^97826087 under GRH.
Arithmetic index-four containment removes the subgroup premise from the final theorem.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive log n and Gaussian scale (32/105)log(n)², an index-at-least-four
subgroup cannot satisfy the actual fixed-cutoff comparison when its normalized
error is at most log(n)/800. Retain the conductor sum until bounding it by
(index-1)log(n), and use the certified actual denominator and strict rational margin. -/
private theorem gaussian_inequality_contradiction_of_index_ge_four {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index) (hL : 0 < Real.log n) :
    let x := Analysis.gaussianMRScale (Real.log n)
    let R := (70 / 3 : ℝ) * x ^ (1 / 4 : ℝ) + LLS.PaperStatements.gaussianAmbientError n x
    R ≤ Real.log n / 800 →
      ¬(((H.index : ℝ) *
                (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                  (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
              Real.exp (1 / 16 : ℝ)) *
            Real.sqrt x ≤
          (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
            14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
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
        14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index : ℝ) - 1) * (LLS.PaperStatements.gaussianAmbientError n x) ≤
      ((H.index : ℝ) - 1) * ((161 / 400 : ℝ) * Real.log n + R) := by
    have hd :=
      mul_nonneg hr
        (show 0 ≤ (70 / 3 : ℝ) * ((H.index : ℝ) - 1) - 14 * ((H.index : ℝ) + 1) by
          linarith only [hiR])
    dsimp only [R]
    nlinarith only [hCM, hd]
  have hstrict := mul_lt_mul_of_pos_left (Analysis.gaussianMR_main_term_lt hL hR) hm
  rw [← mul_assoc] at hstrict
  exact (not_lt_of_ge (hleft.trans (hcmp.trans hright))) hstrict

/-- Under GRH for odd n≥10^97826087, a subgroup of index at least four
containing every strong pass gives a prime failing base at most (16/25)log(n)².
The decimal cutoff certifies log(n)≥225000000, the actual Gaussian scale and all
error budgets. Universal prime-base passage would contradict the actual comparison. -/
theorem exists_prime_witness_le_gaussian_of_index_ge_four {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 97826087 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  have hL := Analysis.gaussianMR_log_cutoff hn
  have hpos : 0 < Real.log n := (by norm_num only : (0 : ℝ) < 225000000).trans_le hL
  have hlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (NeZero.pos n) : (0 : ℝ) < n)
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, hlog]
  by_contra hnone
  let x := Analysis.gaussianMRScale (Real.log n)
  have hx : 4 ≤ x :=
    (by norm_num only : (4 : ℝ) ≤ 3 ^ 16).trans (Analysis.gaussianMRScale_ge_three_pow_sixteen hL)
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
    gaussian_inequality_of_prime_passes_in_subgroup hnlarge hnOdd H hHpass hGRH hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hpass
  have hR := Analysis.gaussianMR_error_budget hL (le_refl (Real.log n))
  exact gaussian_inequality_contradiction_of_index_ge_four H hi hpos hR hcmp

/-- A decimal exponent at least five gives a modulus cutoff at least 20000.
Keep the exponent variable when comparing powers to avoid evaluating huge integers. -/
private theorem decimal_cutoff_ge_twenty_thousand (d : ℕ) (hd : 5 ≤ d) : 20000 ≤ 10 ^ d := by
  exact (by decide : 20000 ≤ 10 ^ 5).trans (Nat.pow_le_pow_right (by decide : 0 < 10) hd)

/-- Under GRH, every odd composite n≥10^97826087 has a prime strong
Miller--Rabin witness at most (16/25)log(n)². The arithmetic pass-containing
subgroup has index at least four; the threshold excludes the exceptional modulus 9.
Apply the actual Gaussian comparison and explicit numerical budget. No additional
subgroup, integral, zero-mass, or error hypothesis remains. -/
theorem exists_prime_witness_le_gaussian {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 97826087 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hnlarge : 20000 ≤ n :=
    (decimal_cutoff_ge_twenty_thousand 97826087 (by decide : 5 ≤ 97826087)).trans hn
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hn9 : n ≠ 9 := by
    intro h
    rw [h] at hnlarge
    exact (by decide : ¬20000 ≤ 9) hnlarge
  obtain ⟨H, hi, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_strongMillerRabinPass hn1 hnOdd hnComposite
      hn9
  exact exists_prime_witness_le_gaussian_of_index_ge_four hnOdd H hi hHpass hGRH hn

/-- Under GRH for odd n≥10^97826087, passage of the canonical strong test
for every prime base at most (16/25)log(n)² is equivalent to primality.
The composite direction uses the explicit Gaussian prime witness; the prime
direction restricts the existing log-squared criterion to the smaller cutoff.
This is the public coefficient 0.64 criterion at the same decimal threshold. -/
theorem prime_iff_millerRabin_for_all_primes_le_gaussian_log_sq {n : ℕ} (hnOdd : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 97826087 ≤ n) :
    (∀ r : ℕ,
        r.Prime →
          (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (r : ZMod n)) ↔
      n.Prime := by
  constructor
  · intro hpass
    by_contra hComposite
    obtain ⟨r, hr, hb, hfail⟩ := exists_prime_witness_le_gaussian hnOdd hComposite hGRH hn
    exact hfail (hpass r hr hb)
  · intro hp r hr hb
    have hnlarge : 20000 ≤ n :=
      (decimal_cutoff_ge_twenty_thousand 97826087 (by decide : 5 ≤ 97826087)).trans hn
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    have hcap : (16 / 25 : ℝ) * (Real.log n) ^ 2 ≤ (Real.log n) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (by norm_num only)
    exact
      (prime_iff_millerRabin_for_all_primes_le_log_sq hGRH hn1 hnOdd).mpr hp r hr (hb.trans hcap)

end PseudoPrime.PrimeTestBounds.MillerRabin
