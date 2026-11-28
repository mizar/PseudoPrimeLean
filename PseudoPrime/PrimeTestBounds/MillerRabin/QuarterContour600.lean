/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaSigned570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInterval600
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaPole570
import Mathlib.Tactic.Ring
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

/-! # Signed Gamma contour estimate for section 99 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the section 99 radius interval, an even character's contour term
is bounded by its conductor contribution minus the first Gamma recovery,
with the density contribution retained separately. -/
theorem section99_even_contour_upper {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hi : χ⁻¹ ≠ 1)
    (he : χ.Even) {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    contourNonEuler570 χ (r ^ 2) ≤
      Real.log q * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (r ^ 2)⁻¹ -
        (if r ≤ 299 then 0.03434 else 0.0364) -
        (4 / 3 : ℝ) * gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have hp : 0 < r := by linarith only [hl]
  have hx := sq_pos_of_pos hp
  have hx1 := one_le_pow₀ (show 1 ≤ r by linarith only [hl]) (n := 2)
  have hz : 13 ≤ Real.log (r ^ 2) + 14 / 5 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 20) (lo := 227 / 40) (hi :=
          6) (by decide +kernel)).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h, Real.log_le_log (by norm_num only) hl]
  have hc :
    (if r ≤ 299 then 0.03434 else 0.0364) <
      ∫ v in Set.Ioi (0 : ℝ),
        gammaDensity570 v * Real.exp (-(1 / 2) * |v - (Real.log (r ^ 2) + 14 / 5)|) := by
    split_ifs with h
    · exact section99_first_gamma hl hu
    · exact section99_first_gamma_upper (le_of_not_ge h) hu
  have hn := central_gamma_convolution_upper χ he hx hz
  rw [← central_gamma_pair_eq_570 χ he hx, ← right_gamma_eq_central_570 χ hx, ←
    reflected_arch_eq_central_570 _ hi hx1, Complex.add_re] at hn
  unfold contourNonEuler570
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
    ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith only [hn, hc]

/-- Beyond 5/(51/50), the fifth-power Gamma density decreases. -/
private theorem density_antitone : AntitoneOn gammaDensity570 (Set.Ici 5) := by
  let f := fun z : ℝ ↦ ((51 / 50 : ℝ) ^ 5 / 120) * z ^ 5 * Real.exp (-(51 / 50 : ℝ) * z)
  have hd (z : ℝ) :
    HasDerivAt f
      (((51 / 50 : ℝ) ^ 5 / 120) * (5 * z ^ 4) * Real.exp (-(51 / 50 : ℝ) * z) +
        ((51 / 50 : ℝ) ^ 5 / 120) * z ^ 5 * (Real.exp (-(51 / 50 : ℝ) * z) * -(51 / 50)))
      z := by
    have h₁ := ((hasDerivAt_id z).pow 5).const_mul ((51 / 50 : ℝ) ^ 5 / 120)
    have h₂ := ((hasDerivAt_id z).const_mul (-(51 / 50 : ℝ))).exp
    simpa only [f, Pi.mul_def, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] using
      h₁.mul h₂
  have hf : AntitoneOn f (Set.Ici 5) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun z _ ↦ (hd z).continuousAt.continuousWithinAt
    · exact fun z _ ↦ (hd z).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : (5 : ℝ) ≤ z := interior_subset hz
      rw [(hd z).deriv]
      have h :=
        mul_nonpos_of_nonneg_of_nonpos
          (show 0 ≤ ((51 / 50 : ℝ) ^ 5 / 120) * z ^ 4 * Real.exp (-(51 / 50 : ℝ) * z) by positivity)
          (show 5 - (51 / 50 : ℝ) * z ≤ 0 by linarith only [hz'])
      linarith only [h]
  intro x hx y hy hxy
  have hx' : (5 : ℝ) ≤ x := hx
  have hy' : (5 : ℝ) ≤ y := hy
  have hx₀ : 0 ≤ x := by linarith only [hx']
  have hy₀ : 0 ≤ y := by linarith only [hy']
  simp only [gammaDensity570, ite_eq_left hx₀, ite_eq_left hy₀]
  exact hf hx hy hxy

/-- Monotonicity of the shifted Gamma density transports a right-radius
certificate to the entire preceding interval. -/
private theorem section99_density_of_endpoint {r b z B d : ℝ} (hl : 292 ≤ r) (hu : r ≤ b)
    (hlog : 2 * Real.log b + 14 / 5 ≤ z) (hB : 0 < B) (hexp : 51 / 50 * z ≤ Real.log B)
    (hd : d ≤ ((51 / 50 : ℝ) ^ 5 / 120) * z ^ 5 / B) :
    d ≤ gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have hp : 0 < r := by linarith only [hl]
  have h₀ : 5 ≤ Real.log (r ^ 2) + 14 / 5 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 20) (lo := 227 / 40) (hi :=
          6) (by decide +kernel)).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h, Real.log_le_log (by norm_num only) hl]
  have h₁ : Real.log (r ^ 2) + 14 / 5 ≤ z := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog, Real.log_le_log hp hu]
  have hz : 0 ≤ z := by linarith only [h₀, h₁]
  refine hd.trans (le_trans ?_ (density_antitone h₀ (h₀.trans h₁) h₁))
  have he := (Real.le_log_iff_exp_le hB).1 hexp
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) he
  rw [one_div (Real.exp _), ← Real.exp_neg, ← neg_mul] at hi
  rw [gammaDensity570, ite_eq_left hz, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hi (mul_nonneg (by norm_num only) (pow_nonneg hz _))

/-- The section 99 density exceeds the required lower bound through radius 299. -/
theorem section99_density_299 {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 299) :
    0.002720 ≤ gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 299) (j := 8) (n := 20) (lo := 5) (hi :=
        570045 / 100000) (by decide +kernel)).2
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1953100) (j := 21) (n := 24) (lo :=
        51 / 50 * 14.2009) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_ofScientific] at h₁ h₂
  exact
    section99_density_of_endpoint hl hu (by linarith only [h₁]) (B := 1953100) (z := 14.2009)
      (by norm_num only) (by linarith only [h₂]) (by norm_num only)

/-- The section 99 density exceeds the required lower bound through radius 300. -/
theorem section99_density_300 {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    0.002708 ≤ gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 20) (lo := 5) (hi :=
        570379 / 100000) (by decide +kernel)).2
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1966450) (j := 21) (n := 24) (lo :=
        51 / 50 * 14.20758) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_ofScientific] at h₁ h₂
  exact
    section99_density_of_endpoint hl hu (by linarith only [h₁]) (B := 1966450) (z := 14.20758)
      (by norm_num only) (by linarith only [h₂]) (by norm_num only)

/-- At the squared radius the inverse Mellin conductor weight is the
shifted Gamma density. -/
theorem section99_profile_eq_density {r : ℝ} (hr : 1 ≤ r) :
    Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (r ^ 2)⁻¹ =
      gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have hp : 0 < r ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hr)
  have h := Real.log_nonneg (one_le_pow₀ hr (n := 2))
  have ht : 0 ≤ Real.log (r ^ 2) + 14 / 5 := by linarith only [h]
  rw [Analysis.rationalPoleProfile, Real.log_inv, gammaDensity570, ite_eq_left ht,
    ite_eq_left ⟨inv_pos.mpr hp, by linarith only [h]⟩]
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.factorial, Nat.cast_ofNat]
  have he :
    (14 / 5 - -Real.log (r ^ 2)) / (50 / 51 : ℝ) = (51 / 50) * (Real.log (r ^ 2) + 14 / 5) := by
    ring
  rw [he, neg_mul]
  ring

/-- The sum of the three conductor budgets equals the section 99 conductor
envelope when the total logarithmic conductor bound is 4r. -/
theorem section99_conductor_eq_density {r : ℝ} (hr : 1 ≤ r) :
    section99Conductor r = 4 * r * gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have hp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h := Real.log_nonneg hr
  rw [Real.log_pow, Nat.cast_ofNat, gammaDensity570,
    ite_eq_left (by linarith only [h] : 0 ≤ 2 * Real.log r + 14 / 5), section99Conductor]
  have he :
    -(51 / 50 : ℝ) * (2 * Real.log r + 14 / 5) =
      -(51 / 50) * (14 / 5) + Real.log r * (-(51 / 25 : ℝ)) := by
    ring
  rw [he, Real.exp_add, ← Real.rpow_def_of_pos hp]
  have hi : r * r ^ (-(51 / 25 : ℝ)) = r ^ (-(26 / 25 : ℝ)) := by
    calc
      _ = r ^ (1 : ℝ) * r ^ (-(51 / 25 : ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hp, show 1 + -(51 / 25 : ℝ) = -(26 / 25 : ℝ) by norm_num only]
  rw [← hi]
  ring

/-- The smooth principal weight at one is the conductor boundary density. -/
theorem section99_weight_eq_density {r : ℝ} (hr : 1 ≤ r) :
    quarterWeight570 (r ^ 2) 1 = gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have h₀ := Real.log_nonneg (one_le_pow₀ hr (n := 2))
  unfold quarterWeight570 gammaDensity570
  rw [Real.sqrt_one, div_self one_ne_zero, one_mul, one_div, Real.log_inv,
    ite_eq_left (by linarith only [h₀] : 0 ≤ Real.log (r ^ 2) + 14 / 5)]
  have he :
    (2 * (7 / 5) - -Real.log (r ^ 2)) / (2 * (25 / 51)) =
      (51 / 50) * (Real.log (r ^ 2) + 14 / 5) := by
    ring
  rw [he, neg_mul]
  ring

/-- Starting at radius 292, the boundary density decreases with the radius. -/
private theorem section99_boundary_antitone {a r : ℝ} (ha : 292 ≤ a) (h : a ≤ r) :
    gammaDensity570 (Real.log (r ^ 2) + 14 / 5) ≤ gammaDensity570 (Real.log (a ^ 2) + 14 / 5) := by
  have h₀ : 0 < a := by linarith only [ha]
  have h₁ := Real.log_le_log (sq_pos_of_pos h₀) (pow_le_pow_left₀ h₀.le h 2)
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 20) (lo := 5) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h₂
  have h₃ : 5 ≤ Real.log (a ^ 2) + 14 / 5 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h₂, Real.log_le_log (by norm_num only) ha]
  have h₄ : Real.log (a ^ 2) + 14 / 5 ≤ Real.log (r ^ 2) + 14 / 5 := by linarith only [h₁]
  exact density_antitone h₃ (h₃.trans h₄) h₄

/-- The principal boundary weight is at most 0.00281 or 0.002721 on the
two section 99 rows. The conductor endpoint certificates give both caps. -/
theorem section99_boundary_caps {r : ℝ} (hr : 292 ≤ r) :
    quarterWeight570 (r ^ 2) 1 ≤ if r ≤ 299 then 0.00281 else 0.002721 := by
  rw [section99_weight_eq_density (by linarith only [hr])]
  split_ifs with h
  · apply (section99_boundary_antitone (le_refl 292) hr).trans
    have hc := section99_conductor_292
    rw [section99_conductor_eq_density (by norm_num only)] at hc
    linarith only [hc]
  · apply (section99_boundary_antitone (by norm_num only) (le_of_not_ge h)).trans
    have hc := section99_conductor_299
    rw [section99_conductor_eq_density (by norm_num only)] at hc
    linarith only [hc]

/-- The three even contour bounds give the section 99 conductor budget
minus the certified Gamma savings, with no dependence on earlier witnesses. -/
theorem section99_triple_contour_upper {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) (ea : a.Even) (eb : b.Even) (ec : c.Even) {r : ℝ}
    (hl : 292 ≤ r) (hu : r ≤ 300) (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) :
    contourNonEuler570 a (r ^ 2) + contourNonEuler570 b (r ^ 2) + contourNonEuler570 c (r ^ 2) ≤
      section99Conductor r - 3 * (if r ≤ 299 then 0.03434 else 0.0364) -
        4 * quarterWeight570 (r ^ 2) 1 := by
  have hr : 1 ≤ r := by linarith only [hl]
  have h₀ := section99_density_300 hl hu
  have hpos := le_trans (by norm_num only : (0 : ℝ) ≤ 0.002708) h₀
  have hm := mul_le_mul_of_nonneg_right hlog hpos
  have ha := section99_even_contour_upper a ia ea hl hu
  have hb := section99_even_contour_upper b ib eb hl hu
  have hc := section99_even_contour_upper c ic ec hl hu
  rw [section99_profile_eq_density hr] at ha hb hc
  rw [section99_conductor_eq_density hr, section99_weight_eq_density hr]
  linarith only [ha, hb, hc, hm]

/-- The real explicit formula retains the signed oscillating zero sum,
so a later phase recovery can use it directly. -/
theorem section99_prime_sum_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {X : ℝ} (hX : 1 ≤ X) :
    (∑' n : ℕ, quarterKernel570.summand χ X n).re =
      contourNonEuler570 χ X - reflectedIntegral570 χ X -
        (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ X ρ).re := by
  have hx := zero_lt_one.trans_le hX
  have h := congrArg Complex.re (contour_formula_570 hq hGRH hp hn hi hX)
  rw [contour_no_residue_570, left_euler_split_570 hp hn hi hx] at h
  simp only [Complex.add_re, Complex.sub_re, ordinary_re_570, reflected_inv_570 χ hx] at h
  unfold contourNonEuler570 rightGamma570
  linarith only [h]

/-- For the three section 99 characters, add a lower bound for the arithmetic
sum to the signed zero and reflected terms and compare it with the contour budget. -/
theorem section99_triple_signed_upper {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) {r A : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r)
    (hA :
      A ≤
        (∑' n : ℕ, quarterKernel570.summand a (r ^ 2) n).re +
          (∑' n : ℕ, quarterKernel570.summand b (r ^ 2) n).re +
          (∑' n : ℕ, quarterKernel570.summand c (r ^ 2) n).re) :
    A +
        (reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) +
        ((∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm a (r ^ 2) ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm b (r ^ 2) ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm c (r ^ 2) ρ).re) ≤
      section99Conductor r - 3 * (if r ≤ 299 then 0.03434 else 0.0364) -
        4 * quarterWeight570 (r ^ 2) 1 := by
  have hx := one_le_pow₀ (show 1 ≤ r by linarith only [hl]) (n := 2)
  rw [section99_prime_sum_eq hp hG pa na ia hx, section99_prime_sum_eq hq hG pb nb ib hx,
    section99_prime_sum_eq hs hG pc nc ic hx] at hA
  linarith only [hA, section99_triple_contour_upper a b c ia ib ic ea eb ec hl hu hlog]

end PseudoPrime.PrimeTestBounds.MillerRabin
