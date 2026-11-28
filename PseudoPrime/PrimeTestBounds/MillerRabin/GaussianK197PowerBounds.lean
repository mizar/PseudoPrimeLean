/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Comparison
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Euler
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Power340
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion

/-! # Transfer of K197 retained prime-power credits -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem forward_weight_mono {l r n : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hn : r ^ 2 ≤ n) :
    (if Real.log (n / l ^ 2) ≤ 21 / 8 then quarterWeight656 (l ^ 2) n else 0) ≤
      (if Real.log (n / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) := by
  have hr := hl.trans_le hlr
  have hn₀ := (sq_pos_of_pos hr).trans_le hn
  have hlog :=
    Real.log_le_log (div_pos hn₀ (sq_pos_of_pos hr))
      (div_le_div_of_nonneg_left hn₀.le (sq_pos_of_pos hl) (pow_le_pow_left₀ hl.le hlr 2))
  split
  · rename_i hs
    rw [ite_eq_left (hlog.trans hs)]
    exact weight_radius_mono hl hlr hn hs
  · split
    · rename_i hs
      unfold quarterWeight656
      dsimp only
      exact
        mul_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg _))
          (div_nonneg (mul_nonneg (pow_nonneg (by linarith only [hs]) 5) (Real.exp_pos _).le)
            (by norm_num only))
    · exact le_rfl

/-- Transfer a certified lower bound at the left endpoint to any radius
for which the retained atoms are still above the squared cutoff. The signed
density is independent of the radius, even outside the forward support. -/
theorem gaussian_power_gain_transfer_197 {K : Finset ℕ} {l r C : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (hK : ∀ n ∈ K, r ^ 2 ≤ (n : ℝ))
    (hC :
      C ≤
        ∑ n ∈ K,
          4 *
            (ArithmeticFunction.vonMangoldt n *
              ((if Real.log ((n : ℝ) / l ^ 2) ≤ 21 / 8 then quarterWeight656 (l ^ 2) n else 0) +
                gaussianDensity197 n))) :
    C ≤
      ∑ n ∈ K,
        4 *
          (ArithmeticFunction.vonMangoldt n *
            ((if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) +
              gaussianDensity197 n)) := by
  refine hC.trans (Finset.sum_le_sum fun n hn ↦ ?_)
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (add_le_add_left (forward_weight_mono hl hlr (hK n hn)) _)
        ArithmeticFunction.vonMangoldt_nonneg)
      (by norm_num only)

/-- Insert a certified left-endpoint prime-power bound into the K197
comparison at any later radius below all the retained powers. -/
theorem gaussian_power_cell_comparison_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ} (hr : 332.15 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hpow : ∀ n ∈ K, ∃ l j : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ n = l ^ j) (l C : ℝ) (hl : 0 < l)
    (hlr : l ≤ r)
    (hC :
      C ≤
        ∑ n ∈ K,
          4 *
            (ArithmeticFunction.vonMangoldt n *
              ((if Real.log ((n : ℝ) / l ^ 2) ≤ 21 / 8 then quarterWeight656 (l ^ 2) n else 0) +
                gaussianDensity197 n))) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) + C +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0475739 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  have h := gaussian_prime_power_signed_197 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hpow
  have hgain := gaussian_power_gain_transfer_197 hl hlr (fun n hn ↦ (hK n hn).le) hC
  dsimp only at h ⊢
  linarith only [h, hgain]

/-- Enclose the signed reflected density using logarithm and power intervals.
The lower power endpoint applies to positive profile bounds and the upper
endpoint to negative bounds. This gives a rational check for each retained atom. -/
theorem gaussian_density_box_197 {n l u a b : ℝ} (hn : 0 ≤ n) (hl : 23 / 2 ≤ l)
    (hlog : Real.log n ∈ Set.Icc l u) (hp : n ^ (-(8 / 5) : ℝ) ∈ Set.Icc a b) :
    let q := 4.028662 - 7.025620 * (u - 23 / 2) + 2.061370 * (l - 23 / 2) ^ 2
    min (a * q) (b * q) ≤ gaussianDensity197 n := by
  intro q
  have h₁ := sub_le_sub_right hlog.1 (23 / 2)
  have h₂ := pow_le_pow_left₀ (sub_nonneg.mpr hl) h₁ 2
  have h₃ := profile_lower (hl.trans hlog.1)
  have hq : q ≤ gaussianProfile197 (Real.log n) := by
    dsimp only [q, lowerPoly] at h₃ ⊢
    linarith only [h₂, h₃, hlog.2]
  rw [gaussianDensity197]
  apply le_trans _ (mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hn _))
  by_cases h : 0 ≤ q
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hp.1 h)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hp.2 (le_of_not_ge h))

/-- Certify the negative eight-fifths power by comparing fifth powers.
Both comparisons use only integer exponents and allow rational endpoints. -/
theorem gaussian_power_box_197 {n a b : ℝ} (hn : 0 < n) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlo : a ^ 5 * n ^ 8 ≤ 1) (hhi : 1 ≤ b ^ 5 * n ^ 8) : n ^ (-(8 / 5) : ℝ) ∈ Set.Icc a b := by
  have hp : (n ^ (-(8 / 5) : ℝ)) ^ 5 = (n ^ 8)⁻¹ := by
    rw [← Real.rpow_mul_natCast hn.le, Nat.cast_ofNat,
      show (-(8 / 5) : ℝ) * 5 = -8 by norm_num only, Real.rpow_neg hn.le, ←
      Nat.cast_ofNat (R := ℝ) (n := 8), Real.rpow_natCast]
  have hn₈ := pow_pos hn 8
  refine ⟨?_, ?_⟩
  · apply (pow_le_pow_iff_left₀ ha (Real.rpow_nonneg hn.le _) (by decide : 5 ≠ 0)).mp
    rw [hp, ← one_div]
    exact (le_div_iff₀ hn₈).mpr hlo
  · apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hn.le _) hb (by decide : 5 ≠ 0)).mp
    rw [hp, ← one_div]
    exact (div_le_iff₀ hn₈).mpr hhi

/-- A retained density bound from rational log and fifth-power checks. -/
theorem gaussian_density_rat_197 {n j : ℕ} {l u a b : ℚ} (hn : 0 < n) (hl : 23 / 2 ≤ l)
    (hlog : Analysis.rationalLogIntervalCheck n j 12 l u = true) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlo : a ^ 5 * (n : ℚ) ^ 8 ≤ 1) (hhi : 1 ≤ b ^ 5 * (n : ℚ) ^ 8) :
    let q : ℚ := 4.028662 - 7.025620 * (u - 23 / 2) + 2.061370 * (l - 23 / 2) ^ 2
    ((min (a * q) (b * q) : ℚ) : ℝ) ≤ gaussianDensity197 n := by
  intro q
  have h := Analysis.rationalLogIntervalCheck_sound hlog
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Rat.cast_natCast] at h
  have hp :=
    gaussian_power_box_197 hn' (a := (a : ℝ)) (b := (b : ℝ)) (by exact_mod_cast ha)
      (by exact_mod_cast hb) (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  have hx : (23 / 2 : ℝ) ≤ (l : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hl
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hh
  have hbox := gaussian_density_box_197 hn'.le hx h hp
  dsimp only [q] at hbox ⊢
  simpa only [Rat.cast_min, Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofScientific] using hbox

/-- For a prime-power row, enclose the Mangoldt-weighted signed density.
All endpoints are rational and the product handles either sign of the density. -/
theorem gaussian_power_density_row_197 {p k jp jn : ℕ} {pl pu l u a b D : ℚ} (hp : p.Prime)
    (hk : k ≠ 0) (hprime : Analysis.rationalLogIntervalCheck p jp 12 pl pu = true) (hl : 23 / 2 ≤ l)
    (hlog : Analysis.rationalLogIntervalCheck (p ^ k : ℕ) jn 12 l u = true) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hlo : a ^ 5 * ((p ^ k : ℕ) : ℚ) ^ 8 ≤ 1) (hhi : 1 ≤ b ^ 5 * ((p ^ k : ℕ) : ℚ) ^ 8)
    (hD :
      let q : ℚ := 4.028662 - 7.025620 * (u - 23 / 2) + 2.061370 * (l - 23 / 2) ^ 2
      D ≤ 4 * min (pl * min (a * q) (b * q)) (pu * min (a * q) (b * q))) :
    (D : ℝ) ≤ 4 * (ArithmeticFunction.vonMangoldt (p ^ k) * gaussianDensity197 (p ^ k)) := by
  let q : ℚ := 4.028662 - 7.025620 * (u - 23 / 2) + 2.061370 * (l - 23 / 2) ^ 2
  let v : ℚ := min (a * q) (b * q)
  have hd : (v : ℝ) ≤ gaussianDensity197 (p ^ k) := by
    rw [← Nat.cast_pow]
    exact gaussian_density_rat_197 (pow_pos hp.pos _) hl hlog ha hb hlo hhi
  have h := Analysis.rationalLogIntervalCheck_sound hprime
  rw [Rat.cast_natCast] at h
  have he : min ((pl : ℝ) * v) ((pu : ℝ) * v) ≤ Real.log p * v := by
    by_cases hv : (0 : ℝ) ≤ v
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right h.1 hv)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right h.2 (le_of_not_ge hv))
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hc := (Rat.cast_le (K := ℝ)).mpr hD
  change (D : ℝ) ≤ ((4 * min (pl * v) (pu * v) : ℚ) : ℝ) at hc
  simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_min] at hc
  exact
    hc.trans
      (mul_le_mul_of_nonneg_left
        (he.trans (mul_le_mul_of_nonneg_left hd (Real.log_natCast_nonneg p))) (by norm_num only))

/-- The retained atom 3^13 contributes positive signed density even when
its forward weight vanishes. -/
theorem gaussian_density_three_pow13_197 :
    (22 / 10 ^ 11 : ℝ) ≤
      4 * (ArithmeticFunction.vonMangoldt (3 ^ 13) * gaussianDensity197 ((3 ^ 13 : ℕ) : ℝ)) := by
  rw [Nat.cast_pow]
  have he : ((22 / 10 ^ 11 : ℚ) : ℝ) = (22 / 10 ^ 11 : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  rw [← he]
  apply
    gaussian_power_density_row_197 (p := 3) (k := 13) (jp := 2) (jn := 21) (pl := 1.098612) (pu :=
      1.098613) (l := 14.281959) (u := 14.281961) (a := 119 / 10 ^ 12) (b := 120 / 10 ^ 12)
  all_goals decide +kernel

private theorem fixed_weight_transfer {r : ℝ} {n : ℕ} (hr : 332.15 ≤ r) (hn : r ^ 2 < (n : ℝ))
    (hs : Real.log ((n : ℝ) / (330 : ℝ) ^ 2) ≤ 21 / 8) :
    4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) ((330 : ℝ) ^ 2) n).re ≤
      4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  rw [quarter_summand_656 (by norm_num only) (Nat.cast_pos.mp ((sq_nonneg r).trans_lt hn)) hs,
    mul_comm (quarterWeight656 _ _)]
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (weight_radius_mono (by norm_num only) (by linarith only [hr]) hn.le hs)
        ArithmeticFunction.vonMangoldt_nonneg)
      (by norm_num only)

/-- Reuse the certified radius-330 forward sum in the early K197 range.
All retained powers stay above the cutoff through radius 336.9, and the
comparison includes the cost of their reflected density. -/
theorem gaussian_fixed_power_comparison_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ}
    (hr : r ∈ Set.Icc 332.15 336.9) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) + 0.143227796 +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  have hwide : r ∈ Set.Ico 325 337 :=
    ⟨(by norm_num only : (325 : ℝ) ≤ 332.15).trans hr.1, hr.2.trans_lt (by norm_num only)⟩
  have hs (n : ℕ) (hn : n ∈ fixedPowers663) := fixed_power_support_lt_337 hwide hn
  have h :=
    gaussian_power_comparison_197 ha hb hc hp hq hk hG ⟨hr.1, hr.2.trans (by norm_num only)⟩ hL ht
      hpa hpb hpc fixedPowers663 (fun n hn ↦ (hs n hn).1) (fun n hn ↦ (hs n hn).2.le)
      (fun _ hn ↦ fixed_power_base_663 hn)
  have hg :=
    quarter_power_gain_330.trans
      (Finset.sum_le_sum fun n hn ↦
        fixed_weight_transfer hr.1 (hs n hn).1
          (fixed_power_support_lt_337 (r := 330) ⟨by norm_num only, by norm_num only⟩ hn).2.le)
  dsimp only at h ⊢
  linarith only [h, hg]

private theorem main_power_early {x : ℝ} (hx : 0 < x) (hl : 11.611 ≤ Real.log x) :
    x ^ (-(3 / 5) : ℝ) ≤ 0.000944 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 125000 / 118) (j := 11) (n := 32) (lo := 6)
        (hi := 6.9666) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h
  rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
  have he : -(3 / 5 : ℝ) * Real.log x ≤ -Real.log (125000 / 118) := by linarith only [h, hl]
  refine (Real.exp_le_exp.mpr he).trans ?_
  rw [Real.exp_neg, Real.exp_log (by norm_num only)]
  norm_num only

/-- The signed main integral costs at most 0.006 on the early K197 radii.
This bounds the combined quadratic before multiplying by the positive power. -/
theorem gaussian_profile_main_early_197 {r : ℝ} (hr : r ∈ Set.Icc 332.15 336.9) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 332.15).trans hr.1)
  have hlog := radius_log_lower hr.1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 336.9) (j := 9) (n := 27) (lo := 5) (hi := 5.82)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hu
  have hl : 11.611 ≤ Real.log (r ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog]
  have hh : Real.log (r ^ 2) ≤ 11.64 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hu, Real.log_le_log hr₀ hr.2]
  let v := Real.log (r ^ 2) - 23 / 2
  have hv₀ : 0 ≤ v := by
    dsimp only [v]; linarith only [hl]
  have hvlo : 0.111 ≤ v := by
    dsimp only [v]; linarith only [hl]
  have hv₁ : v ≤ 0.14 := by
    dsimp only [v]; linarith only [hh]
  have hv₂ := pow_le_pow_left₀ hv₀ hv₁ 2
  have hpoly :
    (4.028663 - 7.025619 * (v + 5 / 3) + 2.061371 * (v ^ 2 + (10 / 3) * v + 50 / 9)) / (3 / 5) ≤
      (6.34 : ℝ) := by
    linarith only [hvlo, hv₂]
  refine (gaussian_profile_main_upper_197 hx (by linarith only [hl])).trans ?_
  refine (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (sq_nonneg r) _)).trans ?_
  exact
    (mul_le_mul_of_nonneg_right (main_power_early (sq_pos_of_pos hr₀) hl)
          (by norm_num only : (0 : ℝ) ≤ 6.34)).trans
      (by norm_num only)

private theorem profile_boundary_abs {v : ℝ} (hv : v ∈ Set.Icc 11.5 11.694) :
    |gaussianProfile197 v| ≤ 5 := by
  rw [profile_expand_197, abs_le]
  have hz : 0 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hU : v - 23 / 2 ≤ 0.194 := by linarith only [hv.2]
  have hsq := pow_le_pow_left₀ hz hU 2
  have h := profile_coeff_bounds_197
  have h₀ := mul_le_mul_of_nonneg_right h.2.1.1 hz
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.2 hz
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.1 (sq_nonneg (v - 23 / 2))
  have h₃ := mul_le_mul_of_nonneg_right h.2.2.2 (sq_nonneg (v - 23 / 2))
  exact
    ⟨by linarith only [h.1.1, h₀, h₂, hz, hU, sq_nonneg (v - 23 / 2)], by
      linarith only [h.1.2, h₁, h₃, hz, hsq]⟩

private theorem boundary_power_bound {x : ℝ} (hx : 110000 ≤ x) :
    x ^ (-(8 / 5) : ℝ) ≤ 0.000000009 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 110000) (p := 8) (d :=
        5) (lo := 0) (hi := 0.000000009) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at h
  exact
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 110000) hx (by norm_num only)).trans
      (by
        norm_num only; exact h)

/-- On the squared cutoffs from radius 336.8 to 346.1 the finite Chebyshev envelope
and the signed profile box bound the remaining Abel boundary term. -/
theorem gaussian_abel_boundary_early_197 {x : ℝ} (hx : 110000 ≤ x) (hU : x ≤ 346.1 ^ 2)
    (hl : Real.log x ∈ Set.Icc 11.5 11.694) :
    -(Chebyshev.psi x - x) * gaussianDensity197 x ≤ 0.000013 := by
  have hxp : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 110000).trans hx
  have hψ :=
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
      ((by norm_num only : (1423 : ℝ) ≤ 110000).trans hx) (hU.trans (by norm_num only))
  have hs : Real.sqrt x ≤ 346.1 := (Real.sqrt_le_iff).mpr ⟨by norm_num only, hU⟩
  have he : |Chebyshev.psi x - x| ≤ (276.88 : ℝ) := by linarith only [hψ, hs]
  have hd : |gaussianDensity197 x| ≤ (0.000000045 : ℝ) := by
    rw [gaussianDensity197, abs_mul, abs_of_nonneg (Real.rpow_nonneg hxp _)]
    have h :=
      mul_le_mul (boundary_power_bound hx) (profile_boundary_abs hl) (abs_nonneg _)
        (by norm_num only)
    linarith only [h]
  have h := mul_le_mul he hd (abs_nonneg _) (by norm_num only)
  have hh := le_abs_self (-(Chebyshev.psi x - x) * gaussianDensity197 x)
  rw [abs_mul, abs_neg] at hh
  linarith only [h, hh]

/-- Combine the signed density integral, boundary, and Abel error into
one upper bound for substitution in the early K197 comparison. -/
theorem gaussian_abel_tail_early_197 {r : ℝ} (hr : r ∈ Set.Icc 332.15 336.9) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.006305 := by
  intro x
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1
  have hL : (110000 : ℝ) ≤ x :=
    (by norm_num only : (110000 : ℝ) ≤ 332.15 ^ 2).trans
      (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hU : x ≤ 336.9 ^ 2 := pow_le_pow_left₀ hp.le hr.2 2
  have hlog : Real.log x ∈ Set.Icc 11.5 11.64 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 336.9) (j := 9) (n := 27) (lo := 5) (hi :=
          5.82) (by decide +kernel)).2
    simp only [Rat.cast_ofScientific] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    exact ⟨by linarith only [radius_log_lower hr.1], by linarith only [h, Real.log_le_log hp hr.2]⟩
  have hmain := gaussian_profile_main_early_197 hr
  have hb :=
    gaussian_abel_boundary_early_197 hL (hU.trans (by norm_num only))
      ⟨hlog.1, hlog.2.trans (by norm_num only)⟩
  have he := gaussian_abel_error_early_197 hL (hU.trans (by norm_num only))
  dsimp only [x] at hb he ⊢
  linarith only [hmain, hb, he]

private theorem erased_atom_log : Real.log ((337 : ℝ) ^ 2 / (330 : ℝ) ^ 2) ∈ Set.Icc 0 0.06 := by
  have h₁ :=
    Analysis.rationalLogIntervalCheck_sound (N := 337) (j := 9) (n := 27) (lo := 5.82) (hi := 5.821)
      (by decide +kernel)
  have h₂ :=
    Analysis.rationalLogIntervalCheck_sound (N := 330) (j := 9) (n := 27) (lo := 5.799) (hi := 5.8)
      (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h₁ h₂
  rw [Real.log_div (by norm_num only) (by norm_num only), Real.log_pow, Real.log_pow,
    Nat.cast_ofNat]
  exact ⟨by linarith only [h₁.1, h₂.2], by linarith only [h₁.2, h₂.1]⟩

private theorem erased_atom_weight :
    quarterWeight656 ((330 : ℝ) ^ 2) ((337 : ℝ) ^ 2) ≤
      (1 / 337) * ((2.8875 : ℝ) ^ 5 * 0.06 / 120) := by
  let v := (11 / 10 : ℝ) * (21 / 8 - Real.log ((337 : ℝ) ^ 2 / (330 : ℝ) ^ 2))
  have hv₀ : 0 ≤ v := by
    dsimp only [v]; linarith only [erased_atom_log.2]
  have hvU : v ≤ 2.8875 := by
    dsimp only [v]; linarith only [erased_atom_log.1]
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 50 / 3) (j := 5) (n := 27) (lo := 2) (hi :=
        2.815) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlog
  have hvL : 2.815 ≤ v := by
    dsimp only [v]; linarith only [erased_atom_log.2]
  have hx := Real.exp_le_exp.mpr (show -v ≤ -Real.log (50 / 3) by linarith only [hvL, hlog])
  simp only [Real.exp_neg, Real.exp_log (by norm_num only : (0 : ℝ) < 50 / 3)] at hx
  have he : Real.exp (-v) ≤ (0.06 : ℝ) := by
    rw [Real.exp_neg]; linarith only [hx]
  have hh := mul_le_mul (pow_le_pow_left₀ hv₀ hvU 5) he (Real.exp_pos _).le (by norm_num only)
  unfold quarterWeight656
  rw [Real.sqrt_sq (by norm_num only : (0 : ℝ) ≤ 337)]
  exact
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hh (by norm_num only)) (by norm_num only)

private theorem erased_atom_upper :
    4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) ((330 : ℝ) ^ 2) (337 ^ 2 : ℕ)).re ≤
      0.007 := by
  have hp : Nat.Prime 337 := by decide +kernel
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 337) (j := 9) (n := 27) (lo := 5.82) (hi :=
        5.821) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlog
  rw [quarter_summand_656 (by norm_num only) (by norm_num only)
      (show Real.log (((337 ^ 2 : ℕ) : ℝ) / (330 : ℝ) ^ 2) ≤ 21 / 8
        by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact erased_atom_log.2.trans (by norm_num only)),
    ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Nat.cast_ofNat]
  have he := mul_le_mul erased_atom_weight hlog (Real.log_natCast_nonneg 337) (by norm_num only)
  linarith only [he]

/-- Removing the square of 337 from the radius-330 certificate costs at
most 0.007. This keeps the remaining credit when the radius passes 337. -/
private theorem erased_power_gain :
    (0.136227796 : ℝ) ≤
      ∑ n ∈ fixedPowers663.erase (337 ^ 2),
        4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) ((330 : ℝ) ^ 2) n).re := by
  have hm : 337 ^ 2 ∈ fixedPowers663 := by decide +kernel
  have hsum :=
    Finset.sum_erase_add fixedPowers663
      (fun n ↦ 4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) ((330 : ℝ) ^ 2) n).re) hm
  have h := quarter_power_gain_330
  rw [← hsum] at h
  linarith only [h, erased_atom_upper]

private theorem retained_log_support {r : ℝ} (hr : 332.15 ≤ r) {n : ℕ}
    (hn : n ∈ fixedPowers663.erase (337 ^ 2)) : Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 := by
  have hbase :=
    fixed_power_support_lt_337 (r := 330) ⟨by norm_num only, by norm_num only⟩
      (Finset.mem_of_mem_erase hn)
  have hn₀ := (sq_nonneg (330 : ℝ)).trans_lt hbase.1
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 332.15).trans_le hr
  have h₃₃₀ : (330 : ℝ) ≤ r := (by norm_num only : (330 : ℝ) ≤ 332.15).trans hr
  refine (Real.log_le_log (div_pos hn₀ (sq_pos_of_pos hr₀)) ?_).trans hbase.2.le
  exact
    div_le_div_of_nonneg_left hn₀.le (by norm_num only) (pow_le_pow_left₀ (by norm_num only) h₃₃₀ 2)

private theorem erased_support {r : ℝ} (hr : r ∈ Set.Icc 332.15 342.9) {n : ℕ}
    (hn : n ∈ fixedPowers663.erase (337 ^ 2)) :
    r ^ 2 < (n : ℝ) ∧ Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 := by
  have hN : ∀ n ∈ fixedPowers663.erase (337 ^ 2), 343 ^ 2 ≤ n := by decide +kernel
  have hlo : (343 : ℝ) ^ 2 ≤ n := by exact_mod_cast hN n hn
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1
  have hcut :=
    (pow_lt_pow_left₀ (hr.2.trans_lt (by norm_num only : (342.9 : ℝ) < 343)) hr₀.le
          (by decide : (2 : ℕ) ≠ 0)).trans_le
      hlo
  have h₃₃₀ : (330 : ℝ) ≤ r := (by norm_num only : (330 : ℝ) ≤ 332.15).trans hr.1
  have hn₀ := (sq_nonneg r).trans_lt hcut
  have h :=
    Real.log_le_log (div_pos hn₀ (sq_pos_of_pos hr₀))
      (div_le_div_of_nonneg_left hn₀.le (by norm_num only)
        (pow_le_pow_left₀ (by norm_num only) h₃₃₀ 2))
  exact
    ⟨hcut,
      h.trans
        (fixed_power_support_lt_337 (r := 330) ⟨by norm_num only, by norm_num only⟩
            (Finset.mem_of_mem_erase hn)).2.le⟩

/-- The retained forward contribution after removing the square of 337
has a fixed lower bound up to radius 342.9. -/
private theorem erased_power_at_radius {r : ℝ} (hr : r ∈ Set.Icc 332.15 342.9) :
    (0.136227796 : ℝ) ≤
      ∑ n ∈ fixedPowers663.erase (337 ^ 2),
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  refine erased_power_gain.trans (Finset.sum_le_sum fun n hn ↦ ?_)
  exact
    fixed_weight_transfer hr.1 (erased_support hr hn).1
      (fixed_power_support_lt_337 (r := 330) ⟨by norm_num only, by norm_num only⟩
          (Finset.mem_of_mem_erase hn)).2.le

private theorem retained_comparison_of_gain {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t C : ℝ} (hr : 336.8 ≤ r)
    (K : Finset ℕ) (hsub : K ⊆ fixedPowers663.erase (337 ^ 2)) (hcut : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1)
    (hcredit : C ≤ ∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) + C +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  have hrad : (332.15 : ℝ) ≤ r := (by norm_num only : (332.15 : ℝ) ≤ 336.8).trans hr
  have h₀ : (336.8 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num only) hr 2
  have hs (n : ℕ) (hn : n ∈ K) :=
    fixed_power_support_lt_337 (r := 336.8) ⟨by norm_num only, by norm_num only⟩
      (Finset.mem_of_mem_erase (hsub hn))
  obtain ⟨hpass, hcost⟩ :=
    quarter_retained_window_663 a b c (r := 336.8) ⟨by norm_num only, by norm_num only⟩
      (fun n hn hl ↦ hpa n hn (hl.trans h₀)) (fun n hn hl ↦ hpb n hn (hl.trans h₀))
      (fun n hn hl ↦ hpc n hn (hl.trans h₀)) K (fun n hn ↦ (hs n hn).1) (fun n hn ↦ (hs n hn).2.le)
      (fun _ hn ↦ fixed_power_base_663 (Finset.mem_of_mem_erase (hsub hn)))
  have h :=
    gaussian_comparison_upper_197 ha hb hc hp hq hk hG hrad hL ht hpa hpb hpc K hcut
      (fun n hn ↦ retained_log_support hrad (hsub hn)) hpass
  have hcost' :
    (∑ n ∈ K, 8 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤ 0.000297 := by
    rw [← Finset.mul_sum] at hcost ⊢
    linarith only [hcost]
  change C ≤ ∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) at hcredit
  dsimp only at h ⊢
  linarith only [h, hcredit, hcost']

private theorem erased_comparison_of_gain {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t C : ℝ}
    (hr : r ∈ Set.Icc 336.8 342.9) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1)
    (hcredit :
      C ≤
        ∑ n ∈ fixedPowers663.erase (337 ^ 2),
          4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) + C +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  have hrad : r ∈ Set.Icc 332.15 342.9 :=
    ⟨(by norm_num only : (332.15 : ℝ) ≤ 336.8).trans hr.1, hr.2⟩
  exact
    retained_comparison_of_gain ha hb hc hp hq hk hG hr.1 _ (fun _ hn ↦ hn)
      (fun _ hn ↦ (erased_support hrad hn).1) hL ht hpa hpb hpc hcredit

/-- For radii from 336.8 through 342.9, reuse the radius-330 certificate
after discarding the square of 337. Bound the reflection cost using the
same finite set at radius 336.8, where the existing correction applies. -/
theorem gaussian_erased_comparison_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ}
    (hr : r ∈ Set.Icc 336.8 342.9) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) + 0.136227796 +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  exact
    erased_comparison_of_gain ha hb hc hp hq hk hG hr hL ht hpa hpb hpc
      (erased_power_at_radius ⟨(by norm_num only : (332.15 : ℝ) ≤ 336.8).trans hr.1, hr.2⟩)

private theorem mid_main_power {r : ℝ} (hr : 336.8 ≤ r) : (r ^ 2) ^ (-(3 / 5) : ℝ) ≤ 0.000928 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (336.8 : ℚ) ^ 2) (p :=
        3) (d := 5) (lo := 0) (hi := 0.000928) (by decide +kernel)).2
  simp only [Rat.cast_pow, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hb : (336.8 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num only) hr 2
  exact
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 336.8 ^ 2) hb
          (by norm_num only)).trans
      (by
        norm_num only at hp ⊢; exact hp)

/-- The signed main integral costs at most 0.006 on the K197 radii from 336.8 to 346.1.
This bounds the combined quadratic before multiplying by the positive power. -/
theorem gaussian_profile_main_mid_197 {r : ℝ} (hr : r ∈ Set.Icc 336.8 346.1) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 336.8).trans_le hr.1
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 336.8).trans hr.1)
  have hlog := radius_log_lower ((by norm_num only : (332.15 : ℝ) ≤ 336.8).trans hr.1)
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 346.1) (j := 9) (n := 27) (lo := 5) (hi := 5.847)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hu
  have hl : 11.611 ≤ Real.log (r ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog]
  have hh : Real.log (r ^ 2) ≤ 11.694 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hu, Real.log_le_log hr₀ hr.2]
  let v := Real.log (r ^ 2) - 23 / 2
  have hv₀ : 0 ≤ v := by
    dsimp only [v]; linarith only [hl]
  have hvlo : 0.111 ≤ v := by
    dsimp only [v]; linarith only [hl]
  have hv₁ : v ≤ 0.194 := by
    dsimp only [v]; linarith only [hh]
  have hv₂ := pow_le_pow_left₀ hv₀ hv₁ 2
  have hpoly :
    (4.028663 - 7.025619 * (v + 5 / 3) + 2.061371 * (v ^ 2 + (10 / 3) * v + 50 / 9)) / (3 / 5) ≤
      (6.4 : ℝ) := by
    linarith only [hvlo, hv₂]
  refine (gaussian_profile_main_upper_197 hx (by linarith only [hl])).trans ?_
  refine (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (sq_nonneg r) _)).trans ?_
  exact
    (mul_le_mul_of_nonneg_right (mid_main_power hr.1) (by norm_num only : (0 : ℝ) ≤ 6.4)).trans
      (by norm_num only)

/-- Combine the signed density integral, boundary, and Abel error into
one upper bound for substitution in the K197 comparison through radius 346.1. -/
theorem gaussian_abel_tail_mid_197 {r : ℝ} (hr : r ∈ Set.Icc 336.8 346.1) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.006305 := by
  intro x
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 336.8).trans_le hr.1
  have hL : (110000 : ℝ) ≤ x :=
    (by norm_num only : (110000 : ℝ) ≤ 336.8 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hU : x ≤ 346.1 ^ 2 := pow_le_pow_left₀ hp.le hr.2 2
  have hlog : Real.log x ∈ Set.Icc 11.5 11.694 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 346.1) (j := 9) (n := 27) (lo := 5) (hi :=
          5.847) (by decide +kernel)).2
    simp only [Rat.cast_ofScientific] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    have hleft := radius_log_lower ((by norm_num only : (332.15 : ℝ) ≤ 336.8).trans hr.1)
    exact ⟨by linarith only [hleft], by linarith only [h, Real.log_le_log hp hr.2]⟩
  have hmain := gaussian_profile_main_mid_197 hr
  have hb := gaussian_abel_boundary_early_197 hL hU hlog
  have he := gaussian_abel_error_early_197 hL (hU.trans (by norm_num only))
  dsimp only [x] at hb he ⊢
  linarith only [hmain, hb, he]

private theorem forward_growth_deriv (v : ℝ) :
    HasDerivAt (fun z : ℝ ↦ z ^ 5 * Real.exp (-(1.73 : ℝ) * z))
      ((5 - 1.73 * v) * v ^ 4 * Real.exp (-(1.73 : ℝ) * v)) v := by
  have h := ((hasDerivAt_id v).pow 5).mul (((hasDerivAt_id v).const_mul (-(1.73 : ℝ))).exp)
  convert h using 1
  · rfl
  · dsimp only [id, Pi.pow_apply]
    ring

private theorem forward_growth_mono :
    MonotoneOn (fun z : ℝ ↦ z ^ 5 * Real.exp (-(1.73 : ℝ) * z)) (Set.Icc 0 2.8875) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun v _ ↦ (forward_growth_deriv v).continuousAt.continuousWithinAt
  · exact fun v _ ↦ (forward_growth_deriv v).differentiableAt.differentiableWithinAt
  · intro v hv
    have h : v ∈ Set.Icc (0 : ℝ) 2.8875 := interior_subset hv
    rw [(forward_growth_deriv v).deriv]
    exact mul_nonneg (mul_nonneg (by linarith only [h.2]) (pow_nonneg h.1 _)) (Real.exp_pos _).le

private theorem forward_growth {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ 2.8875) :
    (1 + 0.73 * (w - v)) * (v ^ 5 * Real.exp (-v)) ≤ w ^ 5 * Real.exp (-w) := by
  have hm := forward_growth_mono ⟨hv, hvw.trans hw⟩ ⟨hv.trans hvw, hw⟩ hvw
  have ho := mul_le_mul_of_nonneg_right hm (Real.exp_pos (0.73 * w)).le
  have hd :=
    mul_le_mul_of_nonneg_right (Real.add_one_le_exp (0.73 * (w - v)))
      (mul_nonneg (pow_nonneg hv 5) (Real.exp_pos (-v)).le)
  calc
    _ ≤ Real.exp (0.73 * (w - v)) * (v ^ 5 * Real.exp (-v)) := by linarith only [hd]
    _ = v ^ 5 * (Real.exp (-v) * Real.exp (0.73 * (w - v))) := by ring
    _ = v ^ 5 * Real.exp (-(1.73 : ℝ) * v) * Real.exp (0.73 * w) := by
      rw [← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      refine ho.trans_eq ?_
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

private theorem log_radius_gain {r : ℝ} (hr : 338 ≤ r) : 0.0238 ≤ Real.log r - Real.log 330 := by
  have ha :=
    (Analysis.rationalLogIntervalCheck_sound (N := 338) (j := 9) (n := 27) (lo := 5.82304) (hi := 6)
        (by decide +kernel)).1
  have hb :=
    (Analysis.rationalLogIntervalCheck_sound (N := 330) (j := 9) (n := 27) (lo := 5) (hi := 5.79910)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at ha hb
  linarith only [ha, hb, Real.log_le_log (by norm_num only : (0 : ℝ) < 338) hr]

private theorem log_radius_gain_late {r : ℝ} (hr : 339916 / 1000 ≤ r) :
    0.02959 ≤ Real.log r - Real.log 330 := by
  have ha :=
    (Analysis.rationalLogIntervalCheck_sound (N := 339916 / 1000) (j := 9) (n := 27) (lo :=
        5.828698) (hi := 6) (by decide +kernel)).1
  have hb :=
    (Analysis.rationalLogIntervalCheck_sound (N := 330) (j := 9) (n := 27) (lo := 5) (hi := 5.79910)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ha hb
  linarith only [ha, hb, Real.log_le_log (by norm_num only : (0 : ℝ) < 339916 / 1000) hr]

/-- Within the retained support, increasing the radius from 330 to at
least 338 multiplies the forward weight by at least 1.038. -/
private theorem gaussian_weight_growth_197 {r n g : ℝ} (hr : 338 ≤ r)
    (hg : 0 ≤ Real.log r - Real.log 330)
    (hm : g ≤ 1 + 0.73 * (11 / 5) * (Real.log r - Real.log 330)) (hn : r ^ 2 ≤ n)
    (hs : Real.log (n / (330 : ℝ) ^ 2) ≤ 21 / 8) :
    g * quarterWeight656 ((330 : ℝ) ^ 2) n ≤ quarterWeight656 (r ^ 2) n := by
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 338).trans_le hr
  have hn₀ := (sq_pos_of_pos hr₀).trans_le hn
  let v := (11 / 10 : ℝ) * (21 / 8 - Real.log (n / (330 : ℝ) ^ 2))
  let w := (11 / 10 : ℝ) * (21 / 8 - Real.log (n / r ^ 2))
  have hv : 0 ≤ v := by
    dsimp only [v]; linarith only [hs]
  have hln : 0 ≤ Real.log (n / r ^ 2) := Real.log_nonneg ((one_le_div (sq_pos_of_pos hr₀)).mpr hn)
  have hw : w ≤ 2.8875 := by
    dsimp only [w]; linarith only [hln]
  have he : w - v = (11 / 5) * (Real.log r - Real.log 330) := by
    dsimp only [v, w]
    rw [Real.log_div hn₀.ne' (sq_pos_of_pos hr₀).ne', Real.log_div hn₀.ne' (by norm_num only),
      Real.log_pow, Real.log_pow, Nat.cast_ofNat]
    ring
  have hf := forward_growth hv (by linarith only [he, hg] : v ≤ w) hw
  have hm' : g ≤ 1 + 0.73 * (w - v) := by linarith only [he, hm]
  have ht :=
    (mul_le_mul_of_nonneg_right hm' (mul_nonneg (pow_nonneg hv 5) (Real.exp_pos (-v)).le)).trans hf
  unfold quarterWeight656
  calc
    _ = (1 / Real.sqrt n) * ((g * (v ^ 5 * Real.exp (-v))) / 120) := by
      dsimp only [v]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ht (by norm_num only))
        (one_div_nonneg.mpr (Real.sqrt_nonneg _))

private theorem erased_growth_at_radius {r g P : ℝ} (hr : r ∈ Set.Icc 338 342.9) (hg : 0 ≤ g)
    (hlog : 0 ≤ Real.log r - Real.log 330)
    (hm : g ≤ 1 + 0.73 * (11 / 5) * (Real.log r - Real.log 330)) (hP : P ≤ g * 0.136227796) :
    P ≤
      ∑ n ∈ fixedPowers663.erase (337 ^ 2),
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  have hrw : r ∈ Set.Icc 332.15 342.9 := ⟨(by norm_num only : (332.15 : ℝ) ≤ 338).trans hr.1, hr.2⟩
  refine hP.trans ?_
  refine (mul_le_mul_of_nonneg_left erased_power_gain hg).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have ht := (erased_support hrw hn).1
  have hs :=
    (fixed_power_support_lt_337 (r := 330) ⟨by norm_num only, by norm_num only⟩
        (Finset.mem_of_mem_erase hn)).2.le
  rw [quarter_summand_656 (by norm_num only) (Nat.cast_pos.mp ((sq_nonneg r).trans_lt ht)) hs]
  have h := gaussian_weight_growth_197 hr.1 hlog hm ht.le hs
  have h' := mul_le_mul_of_nonneg_left h (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  linarith only [h']

/-- From radius 338, the forward growth of the retained atoms gives a lower bound P
in the erased comparison when the logarithmic gain certifies g. -/
theorem gaussian_grown_comparison_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t g P : ℝ}
    (hr : r ∈ Set.Icc 338 342.9) (hg : 0 ≤ g)
    (hm : g ≤ 1 + 0.73 * (11 / 5) * (Real.log r - Real.log 330)) (hP : P ≤ g * 0.136227796)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) + P +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  exact
    erased_comparison_of_gain ha hb hc hp hq hk hG
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 338).trans hr.1, hr.2⟩ hL ht hpa hpb hpc
      (erased_growth_at_radius hr hg (by linarith only [log_radius_gain hr.1]) hm hP)

/-- Radius 338 gives a uniform growth multiplier of 1.038 for the retained powers. -/
theorem gaussian_growth_from338 {r : ℝ} (hr : 338 ≤ r) :
    (1.038 : ℝ) ≤ 1 + 0.73 * (11 / 5) * (Real.log r - Real.log 330) := by
  linarith only [log_radius_gain hr]

/-- Radius 339.916 gives a growth multiplier of 1.0475 for the retained powers. -/
theorem gaussian_growth_from339916 {r : ℝ} (hr : 339916 / 1000 ≤ r) :
    (1.0475 : ℝ) ≤ 1 + 0.73 * (11 / 5) * (Real.log r - Real.log 330) := by
  linarith only [log_radius_gain_late hr]

private theorem retained_gain_from340 {r : ℝ} (hr : r ∈ Set.Icc 340 342.9) :
    (0.14908 : ℝ) ≤
      ∑ n ∈ fixedPowers663.erase (337 ^ 2),
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  refine gaussian_power_gain_340.trans (Finset.sum_le_sum fun n hn ↦ ?_)
  have hcut := (erased_support ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr.1, hr.2⟩ hn).1
  have hlog := (erased_support (r := 340) ⟨by norm_num only, by norm_num only⟩ hn).2
  have hp := Nat.cast_pos.mp ((sq_nonneg r).trans_lt hcut)
  rw [quarter_summand_656 (by norm_num only) hp hlog, mul_comm (quarterWeight656 _ _)]
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (weight_radius_mono (by norm_num only) hr.1 hcut.le hlog)
        ArithmeticFunction.vonMangoldt_nonneg)
      (by norm_num only)

private theorem retained_without343_cut {r : ℝ} (hr : r ∈ Set.Icc 340 346.1) {n : ℕ}
    (hn : n ∈ (fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6)) : r ^ 2 < (n : ℝ) := by
  have hN : ∀ n ∈ (fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6), 347 ^ 2 ≤ n := by decide +kernel
  have hlo : (347 : ℝ) ^ 2 ≤ n := by exact_mod_cast hN n hn
  have hr₀ : 0 ≤ r := (by norm_num only : (0 : ℝ) ≤ 340).trans hr.1
  exact
    (pow_lt_pow_left₀ (hr.2.trans_lt (by norm_num only : (346.1 : ℝ) < 347)) hr₀
          (by decide : (2 : ℕ) ≠ 0)).trans_le
      hlo

private theorem retained_gain_without343 {r : ℝ} (hr : r ∈ Set.Icc 340 346.1) :
    (0.147 : ℝ) ≤
      ∑ n ∈ (fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6),
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  refine gaussian_power_gain_340_without343.trans (Finset.sum_le_sum fun n hn ↦ ?_)
  have hcut := retained_without343_cut hr hn
  have hlog := retained_log_support (r := 340) (by norm_num only) (Finset.mem_of_mem_erase hn)
  have hp := Nat.cast_pos.mp ((sq_nonneg r).trans_lt hcut)
  rw [quarter_summand_656 (by norm_num only) hp hlog, mul_comm (quarterWeight656 _ _)]
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (weight_radius_mono (by norm_num only) hr.1 hcut.le hlog)
        ArithmeticFunction.vonMangoldt_nonneg)
      (by norm_num only)

/-- Between radii 340 and 346.1, the retained K197 powers strictly above
the tested cutoff contribute 0.147 to the comparison. -/
theorem gaussian_comparison_without343 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ}
    (hr : r ∈ Set.Icc 340 346.1) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) + 0.147 +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  exact
    retained_comparison_of_gain ha hb hc hp hq hk hG
      ((by norm_num only : (336.8 : ℝ) ≤ 340).trans hr.1)
      ((fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6)) (fun _ hn ↦ Finset.mem_of_mem_erase hn)
      (fun _ hn ↦ retained_without343_cut hr hn) hL ht hpa hpb hpc (retained_gain_without343 hr)

end PseudoPrime.PrimeTestBounds.MillerRabin
