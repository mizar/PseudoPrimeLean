/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-! # Prime mass at the origin for the wide triangle -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational lower bound for a centered triangle term follows from logarithm
and square-root enclosures at its base and prime-power index. -/
private theorem centerTermLower {m p : ℕ} {l u d c : ℝ} (hm : 0 < m)
    (hΛ : ArithmeticFunction.vonMangoldt m = Real.log p) (hl : l ≤ Real.log p) (hu : Real.log m ≤ u)
    (hd : (m : ℝ) ≤ d ^ 2) (hc0 : 0 ≤ c) (hd0 : 0 < d) (hl0 : 0 ≤ l) (hu0 : u ≤ 5 / 2)
    (hc : c * d ≤ l * (1 - u / (5 / 2))) :
    c ≤ ArithmeticFunction.vonMangoldt m / Real.sqrt m * (1 - Real.log m / (5 / 2)) := by
  have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have hs' := (Real.sqrt_le_iff.mpr ⟨hd0.le, hd⟩)
  have ha :=
    mul_le_mul hl (show 1 - u / (5 / 2) ≤ 1 - Real.log m / (5 / 2) by linarith only [hu])
      (show 0 ≤ 1 - u / (5 / 2) by linarith only [hu0]) (hl0.trans hl)
  rw [hΛ, div_mul_eq_mul_div, le_div_iff₀ hs]
  exact (mul_le_mul_of_nonneg_left hs' hc0).trans (hc.trans ha)

/-- Turn a rational logarithm certificate and a rounded square root into
a lower bound for the individual Mangoldt term at a positive prime power. -/
private theorem centerPrimePower (p k j l u d c : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hlog : Analysis.rationalLogIntervalCheck p j 40 (l / 1000) (u / 1000) = true)
    (hd : (p ^ k : ℝ) ≤ (d / 1000) ^ 2) (hd0 : 0 < (d : ℝ) / 1000)
    (hu : (k : ℝ) * (u / 1000) ≤ 5 / 2)
    (hc : (c : ℝ) / 1000 * (d / 1000) ≤ l / 1000 * (1 - k * (u / 1000) / (5 / 2))) :
    (c : ℝ) / 1000 ≤
      ArithmeticFunction.vonMangoldt (p ^ k) / Real.sqrt (p ^ k : ℕ) *
        (1 - Real.log (p ^ k : ℕ) / (5 / 2)) := by
  have hz := Analysis.rationalLogIntervalCheck_sound hlog
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at hz
  apply
    centerTermLower (pow_pos hp.pos _)
      ((ArithmeticFunction.vonMangoldt_apply_pow hk.ne').trans
        (ArithmeticFunction.vonMangoldt_apply_prime hp))
      hz.1 (u := (k : ℝ) * (u / 1000)) (d := d / 1000)
  · rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left hz.2 (Nat.cast_nonneg _)
  · simpa only [Nat.cast_pow] using hd
  · positivity
  · exact hd0
  · positivity
  · exact hu
  · exact hc

/-- The eight supported prime powers at the origin contribute at least 1.393
to the centered triangle sum for half-width 5/2. -/
theorem triangle_center_prime_mass :
    1393 / 1000 ≤
      ∑ m ∈ ({2, 3, 4, 5, 7, 8, 9, 11} : Finset ℕ),
        ArithmeticFunction.vonMangoldt m / Real.sqrt m * (1 - Real.log m / (5 / 2)) := by
  have h2 :=
    centerPrimePower 2 1 1 693 694 1415 353 (by decide) (by decide) (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have h3 :=
    centerPrimePower 3 1 2 1098 1099 1733 355 (by decide) (by decide) (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have h4 :=
    centerPrimePower 2 2 1 693 694 2000 154 (by decide) (by decide) (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have h5 :=
    centerPrimePower 5 1 2 1609 1610 2237 256 (by decide) (by decide) (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have h7 :=
    centerPrimePower 7 1 3 1945 1946 2646 162 (by decide) (by decide) (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have h8 :=
    centerPrimePower 2 3 1 693 694 2829 40 (by decide) (by decide) (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have h9 :=
    centerPrimePower 3 2 2 1098 1099 3000 44 (by decide) (by decide) (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have h11 :=
    centerPrimePower 11 1 3 2397 2398 3317 29 (by decide) (by decide) (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  norm_num only [Nat.reducePow, Nat.cast_ofNat] at *
  linarith only [h2, h3, h4, h5, h7, h8, h9, h11]

/-- Summing all positive indices up to the exponential cutoff gives the
section 76 origin prime mass; the eight certified terms suffice for its lower bound. -/
theorem triangle_center_mass_lower :
    1393 / 1000 ≤
      ∑ m ∈ Finset.Ioc 0 ⌊Real.exp (5 / 2)⌋₊,
        ArithmeticFunction.vonMangoldt m / Real.sqrt m * (1 - Real.log m / (5 / 2)) := by
  have h11 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 11) (j := 3) (n := 40) (lo := 2) (hi := 5 / 2)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h11
  have he := (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 11)).mp h11
  have hb : 11 ≤ ⌊Real.exp (5 / 2)⌋₊ := Nat.le_floor he
  apply triangle_center_prime_mass.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    have hsub : ({2, 3, 4, 5, 7, 8, 9, 11} : Finset ℕ) ⊆ Finset.Ioc 0 11 := by decide
    have ht := Finset.mem_Ioc.mp (hsub hm)
    exact Finset.mem_Ioc.mpr ⟨ht.1, ht.2.trans hb⟩
  · intro m hm _
    have ht := Finset.mem_Ioc.mp hm
    have hlog :=
      (Real.log_le_iff_le_exp (Nat.cast_pos.mpr ht.1)).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp ht.2)
    exact
      mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (by linarith only [hlog])

end PseudoPrime.PrimeTestBounds.MillerRabin
