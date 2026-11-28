/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedBound570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel570
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterAmbientTriviality

/-! # Reflected kernel series for the section 31 character triple -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Below one the section 31 profile has its full logarithmic fifth-power expression. -/
theorem quarter_profile_below_one {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) u =
      ((51 / 50 : ℝ) ^ 5 / 120) * Real.exp (-(51 / 50) * (14 / 5)) * u ^ (51 / 50 : ℝ) *
        (14 / 5 - Real.log u) ^ 5 := by
  have hl := Real.log_nonpos hu.le hu1
  unfold Analysis.rationalPoleProfile
  rw [ite_eq_left ⟨hu, by linarith only [hl]⟩]
  norm_num only [show 2 * 3 - 1 = 5 by decide, Nat.factorial]
  have he :
    -(((14 / 5 : ℝ) - Real.log u) / (50 / 51)) = -(357 / 125 : ℝ) + (51 / 50) * Real.log u := by
    ring
  rw [he, Real.exp_add, Real.rpow_def_of_pos hu]
  rw [mul_comm (Real.log u) (51 / 50 : ℝ)]
  ring

/-- At every natural index, factor the reflected kernel term at a square cutoff into
the section 31 scalar and the shifted Mangoldt weight. The zero index vanishes. -/
theorem reflected_kernel_term_570 {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (quarterKernel570.transform (((n : ℝ) * r ^ 2)⁻¹)).re =
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ))) *
        reflectedWeight570 (14 / 5 + 2 * Real.log r) n := by
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, zero_div, zero_mul, reflectedWeight570, mul_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnx := one_le_mul_of_one_le_of_one_le hn1 (one_le_pow₀ hr (n := 2))
  have hp := zero_lt_one.trans_le hnx
  have hn0 := zero_lt_one.trans_le hn1
  have hr0 := zero_lt_one.trans_le hr
  rw [quarterKernel570, LLS.PaperStatements.rationalPole_transform _ _ _ _ (inv_pos.mpr hp),
    Complex.ofReal_re, quarter_profile_below_one (inv_pos.mpr hp) ((inv_le_one₀ hp).mpr hnx),
    Real.log_inv, Real.log_mul hn0.ne' (sq_pos_of_pos hr0).ne', Real.log_pow, Nat.cast_ofNat,
    Real.inv_rpow hp.le, ← Real.rpow_neg hp.le, Real.mul_rpow hn0.le (sq_nonneg _), ←
    Real.rpow_natCast_mul hr0.le]
  unfold reflectedWeight570
  have he : (n : ℝ) ^ (-(51 / 50 : ℝ)) / Real.sqrt n = (n : ℝ) ^ (-(38 / 25 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn0]
    norm_num only
  rw [← he]
  norm_num only [Nat.cast_ofNat]
  ring

/-- Under RH, if three characters are one at primes through the squared radius and their
real sum is at least minus one, their signed reflected kernel series is below minus 0.0273
for radii from 278 through 285. Prime-power support supplies the finite prefix sign. -/
theorem reflected_triple_kernel_570 (hRH : RiemannHypothesis) {p q s : ℕ} {r : ℝ} (hl : 278 ≤ r)
    (hu : r ≤ 285) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              (quarterKernel570.transform (((n : ℝ) * r ^ 2)⁻¹)).re)) <
      -(273 / 10000) := by
  let τ := fun n : ℕ ↦ (a n).re + (b n).re + (c n).re
  have hsign (n : ℕ) : -1 ≤ τ n ∧ τ n ≤ 3 := by
    refine ⟨ht n, ?_⟩
    dsimp only [τ]
    linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n),
      (Complex.re_le_norm _).trans (b.norm_le_one n),
      (Complex.re_le_norm _).trans (c.norm_le_one n)]
  have hone {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → χ l = 1)
    {n : ℕ} (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 := by
    have hn' : (n : ℝ) ≤ 2701 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 278) hl 2
    exact
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) (by linarith only [hx, hn']) (Nat.coprime_one_right n) hv
  have hprefix (n : ℕ) (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) :
    τ n = 3 := by
    dsimp only [τ]
    rw [hone a hA hn hv, hone b hB hn hv, hone c hC hn hv, Complex.one_re]
    norm_num only
  have h := reflected_kernel_bound_570 hRH hl hu τ hsign hprefix
  let C := ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ)))
  change -(∑' n : ℕ, τ n * _) < _
  simp_rw [reflected_kernel_term_570 (show 1 ≤ r by linarith only [hl])]
  change -(∑' n : ℕ, τ n * (C * reflectedWeight570 _ n)) < _
  simp_rw [mul_left_comm (τ _) C, tsum_mul_left, ← mul_neg]
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
