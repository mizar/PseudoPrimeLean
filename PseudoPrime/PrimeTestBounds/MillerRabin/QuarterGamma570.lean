/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaPrecise
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriple570

/-! # Even gamma estimate for the section 31 mass bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The digamma trapezoid estimate with forty-eight terms certifies the value at 19/25. -/
private theorem point570 : digammaReal (19 / 25) ≤ -(106066 / 100000 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck (1219 / 25) 5 32 0 (3886911 / 1000000) = true from
          by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have h :=
    (AnalyticNumberTheory.Gamma.real_digamma_finite_prefix_bounds (r := (19 / 25 : ℝ))
        (by norm_num only) 48).2
  norm_num only [digammaReal, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h ⊢
  linarith only [h, hl]

/-- For a positive shift, the reciprocal-square prefix dominates the telescoping
sum of successive reciprocal differences. -/
private theorem tail_square {x : ℝ} (hx : 0 < x) (N : ℕ) :
    x⁻¹ - (x + N)⁻¹ ≤ ∑ k ∈ Finset.range N, (x + k)⁻¹ ^ 2 := by
  induction N with
  | zero => simp only [Nat.cast_zero, add_zero, sub_self, Finset.sum_range_zero, le_refl]
  | succ n ih =>
    have hp : 0 < x + n := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)
    have hq : 0 < x + n + 1 := by linarith only [hp]
    have h : (x + n)⁻¹ - (x + n + 1)⁻¹ ≤ (x + n)⁻¹ ^ 2 := by
      field_simp [hp, hq]
      nlinarith only [hp]
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc]
    linarith only [ih, h]

/-- A finite reciprocal-square prefix plus its telescoping tail bounds the
digamma derivative. Only the 48-term prefix requires rational arithmetic. -/
private theorem first570 : (248936 / 100000 : ℝ) ≤ deriv digammaReal (19 / 25) := by
  let x : ℝ := 19 / 25
  let z : ℝ := x + 48
  let S : ℝ := ∑ k ∈ Finset.range 48, (x + k)⁻¹ ^ 2
  have hd := digammaReal_hasDeriv (by norm_num only : (1 / 2 : ℝ) < 19 / 25)
  have hz : 0 < z := by norm_num only [z, x]
  have hn : Filter.Tendsto (fun n : ℕ ↦ z + (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun _ ↦ le_add_of_nonneg_left hz.le) tendsto_natCast_atTop_atTop
  have hv := (tendsto_inv_atTop_zero.comp hn).const_sub (S + z⁻¹)
  have ht : S + z⁻¹ ≤ deriv digammaReal x := by
    apply le_of_tendsto (by simpa only [sub_zero] using hv)
    apply Filter.Eventually.of_forall
    intro n
    have h := digamma_deriv_ge_prefix (by norm_num only : 0 < x) hd (48 + n)
    rw [Finset.sum_range_add] at h
    simp only [Nat.cast_add, Nat.cast_ofNat, ← add_assoc] at h
    change S + (∑ k ∈ Finset.range n, (z + k)⁻¹ ^ 2) ≤ _ at h
    change S + z⁻¹ - (z + (n : ℝ))⁻¹ ≤ _
    rw [hd.deriv]
    linarith only [h, tail_square hz n]
  have hp : (2469104 / 1000000 : ℝ) ≤ S := by
    norm_num only [S, x, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one]
  norm_num only [z, x] at ht
  linarith only [ht, hp]

/-- The first 32 positive reciprocal cubes bound the second derivative from above
via the negative digamma derivative series. -/
private theorem second570 : deriv (deriv digammaReal) (19 / 25) < -(5109 / 1000 : ℝ) := by
  have hu : (1 / 2 : ℝ) < 19 / 25 := by norm_num only
  have hp : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num only : (1 : ℝ) < 2))
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_two] using h
  have hpos (n : ℕ) : 0 ≤ 2 * ((19 / 25 : ℝ) + n)⁻¹ ^ 3 := by positivity
  have hs : Summable (fun n : ℕ ↦ 2 * ((19 / 25 : ℝ) + n)⁻¹ ^ 3) := by
    apply (hp.mul_left 16).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos n), ← inv_pow]
    exact inv_shift_cub_bound hu n
  have hsum := hs.sum_le_tsum (Finset.range 32) (fun n _ ↦ hpos n)
  have hd := (digammaReal_second_series hu).deriv
  rw [show
      (fun n : ℕ ↦ -2 * ((19 / 25 : ℝ) + n)⁻¹ ^ 3) = (fun n : ℕ ↦ -(2 * ((19 / 25 : ℝ) + n)⁻¹ ^ 3))
      from funext (fun n ↦ by ring),
    tsum_neg] at hd
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one] at hsum
  linarith only [hsum, hd]

/-- For an even character the second gamma derivative equals one eighth of the
second digamma derivative at the half argument, by two applications of the chain rule. -/
private theorem even_second_eq {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) {u : ℝ}
    (hu : 1 / 2 < u) :
    deriv (deriv (fun t : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + t : ℝ) : ℂ)).re)) u =
      deriv (deriv digammaReal) ((1 / 2 + u) / 2) / 8 := by
  have hz : 1 / 2 < ((1 / 2 : ℝ) + u) / 2 := by linarith only [hu]
  have heq :
    deriv (fun t : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + t : ℝ) : ℂ)).re) =ᶠ[nhds u]
      (fun t : ℝ ↦ deriv digammaReal ((1 / 2 + t) / 2) / 4) := by
    filter_upwards [Ioi_mem_nhds hu] with t ht
    exact gamma_even_deriv_identity he ht
  have hd := digammaReal_second_series hz
  have hd' := (hd.comp u (((hasDerivAt_id u).const_add (1 / 2 : ℝ)).div_const 2)).div_const 4
  simp only [Function.comp_def, id_eq] at hd'
  rw [heq.deriv_eq, hd'.deriv, hd.deriv]
  ring

/-- For an even character the three section 31 gamma contributions together are at most
minus eight times 0.7346. The signs determine the required sides of the derivative bounds. -/
theorem quarter_gamma_even_7346 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    quarterGamma570 χ ≤ -8 * (7346 / 10000) := by
  have h0 :=
    AnalyticNumberTheory.DirichletLFunction.re_gammaFactor_even he (σ := (1 / 2 : ℝ) + 51 / 50)
      (by norm_num only)
  have h1 := gamma_even_deriv_identity he (u := (51 / 50 : ℝ)) (by norm_num only)
  have hc : (((1 / 2 : ℝ) + 51 / 50) / 2 : ℝ) = 19 / 25 := by norm_num only
  rw [hc] at h0 h1
  have hd := point570
  unfold digammaReal at hd
  have h2 := even_second_eq he (u := 51 / 50) (by norm_num only)
  rw [hc] at h2
  unfold quarterGamma570
  dsimp only
  rw [h1, h2]
  linarith only [h0, hd, first570, second570, Analysis.log_pi_ge_2096_div_1831]

/-- The sharper even-Gamma estimate implies the section 31 constant 0.7345. -/
theorem quarter_gamma_even_570 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    quarterGamma570 χ ≤ -8 * (7345 / 10000) := by
  exact (quarter_gamma_even_7346 he).trans (by norm_num only)

/-- The section 94 Euler lower bound and the three sharpened even-Gamma
bounds supply the recovery constant used in the section 99 mass comparison. -/
theorem quarter_recovery_134154 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.Even) (hb : b.Even) (hc : c.Even)
    (hE :
      (37372 / 10000 : ℝ) ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) :
    (134154 / 10000 : ℝ) ≤
      3 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
        (quarterGamma570 a + quarterGamma570 b + quarterGamma570 c) / 8 := by
  linarith only [hE, quarter_gamma_even_7346 ha, quarter_gamma_even_7346 hb,
    quarter_gamma_even_7346 hc]

/-- For three even characters the certified gamma and total Euler estimates leave only
the complementary Euler tail in the section 31 mass bound. -/
theorem quarter_mass_even_570 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {R T : ℝ}
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (hRH : RiemannHypothesis) (heA : a.Even)
    (heB : b.Even) (heC : c.Even)
    (htail :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
        T) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤ 3 / 4 * R - 13386 / 1000 + 4 * T := by
  apply
    quarter_mass_gap_570 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC s hS ht hA
      hB hC hlog hRH _ htail
  linarith only [quarter_gamma_even_570 heA, quarter_gamma_even_570 heB, quarter_gamma_even_570 heC]

/-- Up to radius 1000 the finite psi error bounds the mass of the three even
characters by the explicit Euler tail. Squaring the radius stays within the
certified range up to one million. -/
theorem quarter_mass_radius_1000 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {R : ℝ} (hl : 278 ≤ R) (hu : R ≤ 1000)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (hRH : RiemannHypothesis) (heA : a.Even)
    (heB : b.Even) (heC : c.Even) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤
      3 / 4 * R - 13386 / 1000 + 4 * positiveTail570 (R ^ 2) := by
  have hp : 0 ≤ R := by linarith only [hl]
  have hx : 2701 ≤ R ^ 2 :=
    (by norm_num only : (2701 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2)
  have hv : R ^ 2 ≤ 1000000 := (pow_le_pow_left₀ hp hu 2).trans (by norm_num only)
  exact
    quarter_mass_even_570 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      (Finset.Ioc 0 ⌊R ^ 2⌋₊)
      (fun k hk ↦ (Nat.le_floor_iff (sq_nonneg R)).mp (Finset.mem_Ioc.mp hk).2) ht hA hB hC hlog hRH
      heA heB heC (positive_tail_upper_570 hRH hx hv)

/-- Across the section 62 interval, the combined zero mass is at most
three quarters of the radius minus 12.7636. Insert the uniform Euler tail cap. -/
theorem quarter_mass_numeric_574 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {R : ℝ} (hl : 285 ≤ R) (hu : R ≤ 287)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (hRH : RiemannHypothesis) (heA : a.Even)
    (heB : b.Even) (heC : c.Even) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤ 3 / 4 * R - 127636 / 10000 := by
  have hm :=
    quarter_mass_radius_1000 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      (by linarith only [hl] : 278 ≤ R) (by linarith only [hu]) ht hA hB hC hlog hRH heA heB heC
  linarith only [hm, radius_tail_numeric_574 hl hu]

/-- For radii from 278 through 285, the section 31 mass estimate for three even characters
uses the explicit positive tail at the squared radius. The prefix consists of all positive
indices through that cutoff, so no external finite-set or tail estimate is required. -/
theorem quarter_mass_radius_570 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {R : ℝ} (hl : 278 ≤ R) (hu : R ≤ 285)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (hRH : RiemannHypothesis) (heA : a.Even)
    (heB : b.Even) (heC : c.Even) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤
      3 / 4 * R - 13386 / 1000 + 4 * positiveTail570 (R ^ 2) := by
  exact
    quarter_mass_radius_1000 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC hl
      (hu.trans (by norm_num only)) ht hA hB hC hlog hRH heA heB heC

end PseudoPrime.PrimeTestBounds.MillerRabin
