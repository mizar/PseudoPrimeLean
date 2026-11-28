/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleCentralGamma
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleOrigin
public import PseudoPrime.LLS.PaperStatements.TriangularDualScaleGeneral

/-! # Absolute zero mass for the section 76 triangle -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The scale-one explicit formula for a primitive even self-inverse character
expresses its normalized absolute zero mass using the signed arithmetic sum. -/
theorem triangle_origin_zero_mass {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (hev : χ.Even) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    (2 / 5) * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) =
      Real.log q + triangleOriginGamma - (4 / 5) * (∑' n : ℕ, K.summand χ 1 n).re := by
  intro K
  let F (t : ℝ) := logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * K.function (Complex.I * t)
  have hF : MeasureTheory.Integrable F := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := 1)
        (by norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) zero_lt_one
    simpa only [Complex.ofReal_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, mul_one] using
      h
  have he :=
    LLS.PaperStatements.triangular_dual_signed_central (by norm_num only : (0 : ℝ) < 5 / 4) hq hGRH
      hp hne (inv_ne_one.mpr hne) (x := 1) le_rfl
  dsimp only at he
  rw [LLS.PaperStatements.triangular_zeroSum_one_eq_absoluteMass _ hne, hi, inv_one] at he
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at he
  have ht : LLS.PaperStatements.triangularKernelProfile (5 / 4) 1 = 5 / 2 := by
    norm_num only [LLS.PaperStatements.triangularKernelProfile, Real.log_one, abs_zero, sub_zero,
      max_eq_right (by norm_num only : (0 : ℝ) ≤ 5 / 2)]
  rw [ht, ← Complex.natCast_log, ← Complex.ofReal_mul] at he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  have hG := triangle_even_gamma_integral hev
  change (4 / 5) * ((∫ t : ℝ, (F t).re) / (2 * Real.pi)) = _ at hG
  rw [show (∫ t : ℝ, (F t).re) = (∫ t, F t).re from integral_re hF] at hG
  change
    (∑' n : ℕ, K.summand χ 1 n).re + (∑' n : ℕ, K.summand χ 1 n).re +
        (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) =
      _ + (1 / (2 * Real.pi)) * (∫ t, F t).re + (1 / (2 * Real.pi)) * (∫ t, F t).re at hre
  rw [one_div_mul_eq_div] at hre
  linarith only [hre, hG]

/-- At a positive index inside the origin cutoff where the character equals one,
the normalized summand is the linear Mangoldt weight. -/
theorem triangle_origin_term {q n : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hn : 0 < n)
    (hb : (n : ℝ) ≤ Real.exp (5 / 2)) (hc : χ (n : ZMod q) = 1) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    (2 / 5) * (K.summand χ 1 n).re =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * (1 - Real.log n / (5 / 2)) := by
  intro K
  have hp := Nat.cast_pos (α := ℝ).mpr hn
  have hl := (Real.log_le_iff_le_exp hp).mpr hb
  have hpos := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn.ne', hc, mul_one,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, div_one]
  rw [LLS.PaperStatements.triangular_transform_of_function K (by norm_num only : (0 : ℝ) < 5 / 4)
      rfl hp]
  unfold LLS.PaperStatements.triangularKernelProfile
  rw [abs_of_nonneg hpos, max_eq_right (by linarith only [hl])]
  ring

/-- Agreement on the positive cutoff gives the certified lower bound for the
normalized finite arithmetic sum by the term identity. -/
theorem triangle_origin_sum_lower {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hc : ∀ n ∈ Finset.Ioc 0 ⌊Real.exp (5 / 2)⌋₊, χ (n : ZMod q) = 1) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    1393 / 1000 ≤ (2 / 5) * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (5 / 2)⌋₊, (K.summand χ 1 n).re := by
  intro K
  rw [Finset.mul_sum]
  apply triangle_center_mass_lower.trans_eq
  apply Finset.sum_congr rfl
  intro n hn
  have hm := Finset.mem_Ioc.mp hn
  exact (triangle_origin_term hm.1 ((Nat.le_floor_iff (Real.exp_pos _).le).mp hm.2) (hc n hn)).symm

/-- At scale one the inverse transform vanishes above the positive cutoff,
so the full character series has exactly the same real part as its finite sum. -/
theorem triangle_origin_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    (∑' n : ℕ, K.summand χ 1 n).re =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (5 / 2)⌋₊, (K.summand χ 1 n).re := by
  intro K
  change Complex.reCLM _ = _
  rw [Complex.reCLM.map_tsum (K.summable_summand χ zero_lt_one)]
  apply tsum_eq_sum
  intro n hout
  change (K.summand χ 1 n).re = 0
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re]
  have hp := Nat.pos_of_ne_zero hn
  have hb :=
    (Nat.floor_lt (Real.exp_pos (5 / 2)).le).mp
      (lt_of_not_ge (fun h ↦ hout (Finset.mem_Ioc.mpr ⟨hp, h⟩)))
  have hl := Real.log_lt_log (Real.exp_pos _) hb
  rw [Real.log_exp] at hl
  have ht :=
    LLS.PaperStatements.triangular_transform_of_function K (by norm_num only : (0 : ℝ) < 5 / 4) rfl
      (Nat.cast_pos.mpr hp)
  have hz : K.transform n = 0 := by
    apply Complex.ext
    · rw [ht, LLS.PaperStatements.triangularKernelProfile,
        abs_of_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hp)),
        max_eq_left (by linarith only [hl])]
      rfl
    · exact K.mellin_real _ (Nat.cast_pos.mpr hp)
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, div_one, hz, mul_zero,
    Complex.zero_re]

/-- For primitive nontrivial even self-inverse characters agreeing with one on
the origin cutoff, the explicit formula saves more than 28/5 from the log conductor. -/
theorem triangle_zero_mass_upper {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (hev : χ.Even)
    (hc : ∀ n ∈ Finset.Ioc 0 ⌊Real.exp (5 / 2)⌋₊, χ (n : ZMod q) = 1) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    (2 / 5) * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) < Real.log q - 28 / 5 := by
  intro K
  rw [triangle_origin_zero_mass hq hGRH hp hne hi hev, triangle_origin_tsum χ]
  have ha := triangle_origin_sum_lower hc
  dsimp only at ha
  linarith only [ha, triangle_origin_gamma_upper]

/-- Multiplicativity extends agreement with one on primes through a cutoff
to every positive integer in the same interval. -/
theorem character_one_on_initial_interval {q B : ℕ} {χ : DirichletCharacter ℂ q}
    (hc : ∀ p : ℕ, p.Prime → p ≤ B → χ (p : ZMod q) = 1) (n : ℕ) :
    0 < n → n ≤ B → χ (n : ZMod q) = 1 := by
  induction n using Nat.recOnMul with
  | zero => exact fun hn _ => (Nat.lt_irrefl 0 hn).elim
  | one => exact fun _ _ => by rw [Nat.cast_one, map_one]
  | prime p hp => exact fun _ hb => hc p hp hb
  | mul a b ha hb =>
    intro hn hB
    have hap := Nat.pos_of_mul_pos_right hn
    have hbp := Nat.pos_of_mul_pos_left hn
    rw [Nat.cast_mul, map_mul, ha hap ((Nat.le_mul_of_pos_right a hbp).trans hB),
      hb hbp ((Nat.le_mul_of_pos_left b hap).trans hB), mul_one]

/-- Under the hypotheses of the origin formula, agreement on small primes
suffices for the conductor saving, by multiplicativity. -/
theorem triangle_zero_mass_of_prime_pass {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (hev : χ.Even)
    (hc : ∀ p : ℕ, p.Prime → p ≤ ⌊Real.exp (5 / 2)⌋₊ → χ (p : ZMod q) = 1) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    (2 / 5) * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) < Real.log q - 28 / 5 := by
  apply triangle_zero_mass_upper hq hGRH hp hne hi hev
  intro n hn
  exact character_one_on_initial_interval hc n (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2

end PseudoPrime.PrimeTestBounds.MillerRabin
