/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
import PseudoPrime.AnalyticNumberTheory.General.MellinWeights

/-! General finite-sum identities for Mellin-weighted von Mangoldt sums. -/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/--
The von Mangoldt tsum against the logarithmic Mellin weight collapses to the classical finite
Riemann-weighted sum, since the weight vanishes past `x` and the von Mangoldt function vanishes
at `0`.
-/
theorem mellinWeightTwo_vonMangoldt_tsum_eq_ofReal {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * General.mellinWeightTwo ((n : ℝ) / x) =
      (logWeightedMangoldtSum x : ℂ) := by
  have hvanish :
    ∀ n ∉ Finset.Ioc 0 ⌊x⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * General.mellinWeightTwo ((n : ℝ) / x) = 0 := by
    intro n hn
    simp only [Finset.mem_Ioc, not_and, not_le] at hn
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp only [hn0, ArithmeticFunction.map_zero, Complex.ofReal_zero, CharP.cast_eq_zero,
        zero_div, zero_mul]
    · have hnxlt : x < n := (Nat.floor_lt hx.le).mp (hn hn0)
      have ht : (0 : ℝ) < (n : ℝ) / x := div_pos (by exact_mod_cast hn0) hx
      have hdivge : (1 : ℝ) ≤ (n : ℝ) / x := (one_le_div hx).mpr hnxlt.le
      rw [General.mellinWeightTwo_eq_ofReal_neg_log_min ht, min_eq_right hdivge, Real.log_one]
      simp only [neg_zero, Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hvanish, logWeightedMangoldtSum]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnxle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have hnxdiv : (n : ℝ) / x ≤ 1 := (div_le_one hx).mpr hnxle
  have ht : (0 : ℝ) < (n : ℝ) / x := div_pos hnpos hx
  have hlog : Real.log ((n : ℝ) / x) = -Real.log (x / (n : ℝ)) := by
    rw [← inv_div x (n : ℝ), Real.log_inv]
  rw [General.mellinWeightTwo_eq_ofReal_neg_log_min ht, min_eq_left hnxdiv, logWeightedMangoldtTerm,
    hlog]
  push_cast
  ring

/--
The von Mangoldt tsum against the reciprocal Mellin weight collapses to the classical finite
reciprocal Riemann-weighted sum, for the same reason as
`PseudoPrime.AnalyticNumberTheory.Arithmetic.mellinWeightTwo_vonMangoldt_tsum_eq_ofReal`.
-/
theorem mellinWeightOne_vonMangoldt_div_tsum_eq_ofReal {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * General.mellinWeightOne ((n : ℝ) / x) =
      (reciprocalWeightedMangoldtSum x : ℂ) := by
  have hvanish :
    ∀ n ∉ Finset.Ioc 0 ⌊x⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * General.mellinWeightOne ((n : ℝ) / x) =
        0 := by
    intro n hn
    simp only [Finset.mem_Ioc, not_and, not_le] at hn
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp only [hn0, ArithmeticFunction.map_zero, Complex.ofReal_zero, CharP.cast_eq_zero,
        div_zero, zero_div, zero_mul]
    · have hnxlt : x < n := (Nat.floor_lt hx.le).mp (hn hn0)
      have ht : (0 : ℝ) < (n : ℝ) / x := div_pos (by exact_mod_cast hn0) hx
      have hdivgt : (1 : ℝ) < (n : ℝ) / x := (one_lt_div hx).mpr hnxlt
      rw [General.mellinWeightOne_eq_ofReal_max ht, max_eq_right (by linarith)]
      simp only [Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hvanish, reciprocalWeightedMangoldtSum]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnxle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have hnxdiv : (n : ℝ) / x ≤ 1 := (div_le_one hx).mpr hnxle
  have ht : (0 : ℝ) < (n : ℝ) / x := div_pos hnpos hx
  rw [General.mellinWeightOne_eq_ofReal_max ht, max_eq_left (by linarith),
    reciprocalWeightedMangoldtTerm]
  push_cast
  ring

/--
Input/assumptions: `N ≥ 1`, `χ` a character mod `N`, `x > 0`.
Conclusion: `∑' n, Λ(n)/n · χ(n) · w₁(n/x) = Arithmetic.characterReciprocalWeightedSum x χ`.
Content: the Mellin weight `w₁` vanishes for `n > x` (`General.mellinWeightOne_eq_ofReal_max`), and
for
`0 < n ≤ x` it equals `1 - n/x`, matching `Arithmetic.reciprocalWeightedMangoldtTerm` exactly; only
finitely
many terms survive, collapsing the `tsum` to the defining finite sum.
Role: identifies the Mellin-weighted series with the finite reciprocal character sum;
`mellinWeightOne_vonMangoldt_div_tsum_eq_ofReal` is the character-free identity in this file.
-/
theorem characterReciprocalWeightedTerm_tsum_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * χ (n : ZMod N) *
          General.mellinWeightOne ((n : ℝ) / x) =
      characterReciprocalWeightedSum x χ := by
  have hvanish :
    ∀ n ∉ Finset.Ioc 0 ⌊x⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * χ (n : ZMod N) *
          General.mellinWeightOne ((n : ℝ) / x) =
        0 := by
    intro n hn
    simp only [Finset.mem_Ioc, not_and, not_le] at hn
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp only [hn0, ArithmeticFunction.map_zero, Complex.ofReal_zero, CharP.cast_eq_zero,
        div_zero, Nat.cast_zero, zero_mul, zero_div]
    · have hnxlt : x < n := (Nat.floor_lt hx.le).mp (hn hn0)
      have ht : (0 : ℝ) < (n : ℝ) / x := div_pos (by exact_mod_cast hn0) hx
      have hdivgt : (1 : ℝ) < (n : ℝ) / x := (one_lt_div hx).mpr hnxlt
      rw [General.mellinWeightOne_eq_ofReal_max ht, max_eq_right (by linarith)]
      simp only [Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hvanish, characterReciprocalWeightedSum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnxle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have hnxdiv : (n : ℝ) / x ≤ 1 := (div_le_one hx).mpr hnxle
  have ht : (0 : ℝ) < (n : ℝ) / x := div_pos hnpos hx
  rw [General.mellinWeightOne_eq_ofReal_max ht, max_eq_left (by linarith),
    characterReciprocalWeightedTerm, reciprocalWeightedMangoldtTerm]
  push_cast
  ring

/--
Input/assumptions: `N ≥ 1`, `χ` a character mod `N`, `x > 0`.
Conclusion: `∑' n, Λ(n) · χ(n) · w₂(n/x) = Arithmetic.characterLogWeightedSum x χ`.
Content: the Mellin weight `w₂` vanishes for `n > x`
(`General.mellinWeightTwo_eq_ofReal_neg_log_min`),
and for `0 < n ≤ x` it equals `-log(n/x) = log(x/n)`, matching `Arithmetic.logWeightedMangoldtTerm`
exactly; only finitely many terms survive, collapsing the `tsum` to the defining finite sum.
Role: the finite-sum side of the Mellin-inversion identity, mirroring
`PseudoPrime.AnalyticNumberTheory.Arithmetic.mellinWeightTwo_vonMangoldt_tsum_eq_ofReal`,
the character-free identity in this file.
-/
theorem characterLogWeightedTerm_tsum_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 0 < x) :
    ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) *
          General.mellinWeightTwo ((n : ℝ) / x) =
      characterLogWeightedSum x χ := by
  have hvanish :
    ∀ n ∉ Finset.Ioc 0 ⌊x⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) *
          General.mellinWeightTwo ((n : ℝ) / x) =
        0 := by
    intro n hn
    simp only [Finset.mem_Ioc, not_and, not_le] at hn
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp only [hn0, ArithmeticFunction.map_zero, Complex.ofReal_zero, Nat.cast_zero, zero_mul,
        CharP.cast_eq_zero, zero_div]
    · have hnxlt : x < n := (Nat.floor_lt hx.le).mp (hn hn0)
      have ht : (0 : ℝ) < (n : ℝ) / x := div_pos (by exact_mod_cast hn0) hx
      have hdivge : (1 : ℝ) ≤ (n : ℝ) / x := (one_le_div hx).mpr hnxlt.le
      rw [General.mellinWeightTwo_eq_ofReal_neg_log_min ht, min_eq_right hdivge, Real.log_one]
      simp only [neg_zero, Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hvanish, characterLogWeightedSum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnxle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have hnxdiv : (n : ℝ) / x ≤ 1 := (div_le_one hx).mpr hnxle
  have ht : (0 : ℝ) < (n : ℝ) / x := div_pos hnpos hx
  have hlog : Real.log ((n : ℝ) / x) = -Real.log (x / (n : ℝ)) := by
    rw [← inv_div x (n : ℝ), Real.log_inv]
  rw [General.mellinWeightTwo_eq_ofReal_neg_log_min ht, min_eq_left hnxdiv,
    characterLogWeightedTerm, logWeightedMangoldtTerm, hlog]
  push_cast
  ring

end PseudoPrime.AnalyticNumberTheory.Arithmetic
