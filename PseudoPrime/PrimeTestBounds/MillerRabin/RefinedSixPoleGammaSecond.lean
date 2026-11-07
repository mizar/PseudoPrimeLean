/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaDerivative
public import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Second derivative and certified even Gamma correction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the half-line above `1/2`, a shifted reciprocal square is bounded by
four times the reciprocal square of `n+1`. Compare the positive denominators
and square their reciprocals. This gives a summable uniform series majorant. -/
theorem inv_shift_sq_bound {u : ℝ} (hu : 1 / 2 < u) (n : ℕ) :
    (u + n)⁻¹ ^ 2 ≤ 4 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < u + n := by linarith only [hu, hn]
  have hsmall : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
  have hden : ((n : ℝ) + 1) / 2 ≤ u + n := by linarith only [hu, hn]
  have hi : (u + n)⁻¹ ≤ (((n : ℝ) + 1) / 2)⁻¹ := (inv_le_inv₀ hpos hsmall).mpr hden
  have hnon : 0 ≤ (u + n)⁻¹ := inv_nonneg.mpr hpos.le
  have hs := pow_le_pow_left₀ hnon hi 2
  rw [inv_div, div_eq_mul_inv] at hs
  nlinarith only [hs]

/-- On the real half-line above `1/2`, the normalized digamma reciprocal
series differentiates termwise to the reciprocal-square series. Uniform
summable control and convergence at one justify exchanging derivative and sum. -/
theorem hasDerivAt_digamma_series {u : ℝ} (hu : 1 / 2 < u) :
    HasDerivAt (fun x : ℝ ↦ ∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (x + n))) (∑' n : ℕ, (u + n)⁻¹ ^ 2)
      u := by
  let U : Set ℝ := Set.Ioi (1 / 2)
  have hp : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num only : (1 : ℝ) < 2))
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_two] using h
  have hg :
    ∀ n : ℕ,
      ∀ x ∈ U, HasDerivAt (fun t : ℝ ↦ 1 / ((n : ℝ) + 1) - 1 / (t + n)) ((x + n)⁻¹ ^ 2) x := by
    intro n x hx
    change (1 / 2 : ℝ) < x at hx
    have hx0 : 0 < x + (n : ℝ) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith only [hx, hn]
    have h := ((hasDerivAt_id x).add_const (n : ℝ)).inv hx0.ne'
    have h' := (hasDerivAt_const x (1 / ((n : ℝ) + 1))).sub h
    convert h' using 1
    · funext t; simp only [Pi.sub_apply, Pi.inv_apply, id_eq, one_div]
    · simp only [inv_pow, one_div, neg_div, zero_sub, neg_neg, id_eq]
  have hb : ∀ n : ℕ, ∀ x ∈ U, ‖(x + n)⁻¹ ^ 2‖ ≤ 4 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    intro n x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← inv_pow]
    exact inv_shift_sq_bound hx n
  have hbase : Summable (fun n : ℕ ↦ (1 / ((n : ℝ) + 1) - 1 / ((1 : ℝ) + n))) := by
    simpa only [add_comm (1 : ℝ), sub_self] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  have h1 : (1 : ℝ) ∈ U := by norm_num only [U, Set.mem_Ioi]
  exact
    hasDerivAt_tsum_of_isPreconnected (hp.mul_left 4) isOpen_Ioi (convex_Ioi (1 / 2)).isPreconnected
      hg hb h1 hbase hu

/-- On the half-line above `1/2`, twice the shifted reciprocal cube is at
most sixteen times the reciprocal square of `n+1`. Combine the square
majorant with the bound on one reciprocal. This controls the derivative of
the reciprocal-square series uniformly. -/
theorem inv_shift_cub_bound {u : ℝ} (hu : 1 / 2 < u) (n : ℕ) :
    2 * (u + n)⁻¹ ^ 3 ≤ 16 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < u + n := by linarith only [hu, hn]
  have hi : (u + n)⁻¹ ≤ 2 := by
    have h :=
      (inv_le_inv₀ hpos (by norm_num only : (0 : ℝ) < 1 / 2)).mpr
        (by linarith only [hu, hn] : (1 / 2 : ℝ) ≤ u + n)
    norm_num only [inv_div, one_div, inv_one, mul_one] at h
    exact h
  have hsq := inv_shift_sq_bound hu n
  have hs : 0 ≤ (u + n)⁻¹ ^ 2 := sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hi hs
  nlinarith only [hm, hsq]

/-- The real reciprocal-square series is differentiable above `1/2`, with
termwise derivative minus twice the reciprocal-cube series. A summable
uniform majorant permits differentiation and supplies the second digamma
series needed for the Gamma estimate. -/
theorem hasDerivAt_digamma_deriv_series {u : ℝ} (hu : 1 / 2 < u) :
    HasDerivAt (fun x : ℝ ↦ ∑' n : ℕ, (x + n)⁻¹ ^ 2) (∑' n : ℕ, -2 * (u + n)⁻¹ ^ 3) u := by
  let U : Set ℝ := Set.Ioi (1 / 2)
  have hp : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num only : (1 : ℝ) < 2))
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_two] using h
  have hg : ∀ n : ℕ, ∀ x ∈ U, HasDerivAt (fun t : ℝ ↦ (t + n)⁻¹ ^ 2) (-2 * (x + n)⁻¹ ^ 3) x := by
    intro n x hx
    change (1 / 2 : ℝ) < x at hx
    have hx0 : 0 < x + (n : ℝ) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith only [hx, hn]
    have h := (((hasDerivAt_id x).add_const (n : ℝ)).inv hx0.ne').pow 2
    convert h using 1
    · funext t; rfl
    · simp only [id_eq, one_div, neg_div, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.inv_apply,
        ← inv_pow]
      ring
  have hb : ∀ n : ℕ, ∀ x ∈ U, ‖-2 * (x + n)⁻¹ ^ 3‖ ≤ 16 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    intro n x hx
    change (1 / 2 : ℝ) < x at hx
    have hx0 : 0 ≤ (x + (n : ℝ))⁻¹ :=
      inv_nonneg.mpr
        (by
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith only [hx, hn])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by norm_num only : (-2 : ℝ) ≤ 0),
      abs_of_nonneg (pow_nonneg hx0 _), ← inv_pow]
    norm_num only [neg_neg]
    exact inv_shift_cub_bound hx n
  have hbase : Summable (fun n : ℕ ↦ ((1 : ℝ) + n)⁻¹ ^ 2) := by
    simpa only [← inv_pow, add_comm (1 : ℝ)] using hp
  have h1 : (1 : ℝ) ∈ U := by norm_num only [U, Set.mem_Ioi]
  exact
    hasDerivAt_tsum_of_isPreconnected (hp.mul_left 16) isOpen_Ioi
      (convex_Ioi (1 / 2)).isPreconnected hg hb h1 hbase hu

/-- Above `1/2`, real digamma is minus Euler''s constant plus the normalized
real reciprocal series. The complex series is absolutely convergent, so its
real part can be taken termwise. This connects the derivative series to the
actual Gamma logarithmic derivative. -/
theorem digammaReal_eq_series {u : ℝ} (hu : 1 / 2 < u) :
    digammaReal u =
      -Real.eulerMascheroniConstant + ∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (u + n)) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hs :=
    AnalyticNumberTheory.Gamma.summable_digammaResolvent (s := (u : ℂ))
      (by simpa only [Complex.ofReal_re] using hu0.le)
  have hd :=
    AnalyticNumberTheory.Gamma.digamma_eq_resolventSeries (s := (u : ℂ))
      (by simpa only [Complex.ofReal_re] using hu0)
  have h := congrArg Complex.re hd
  rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.re_tsum hs] at h
  unfold digammaReal
  rw [h]
  congr 1
  apply tsum_congr
  intro n
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
    ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re]

/-- Above `1/2`, real digamma has the reciprocal-square series as its
derivative. The exact reciprocal representation holds in a neighborhood,
where its termwise derivative has already been justified. -/
theorem digammaReal_hasDeriv {u : ℝ} (hu : 1 / 2 < u) :
    HasDerivAt digammaReal (∑' n : ℕ, (u + n)⁻¹ ^ 2) u := by
  have h := (hasDerivAt_digamma_series hu).const_add (-Real.eulerMascheroniConstant)
  have he :
    digammaReal =ᶠ[nhds u]
      (fun x : ℝ ↦
        -Real.eulerMascheroniConstant + ∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (x + n))) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    exact digammaReal_eq_series hx
  exact h.congr_of_eventuallyEq he

/-- Above `1/2`, the derivative of real digamma has derivative minus twice
the reciprocal-cube series. The first derivative agrees locally with the
reciprocal-square series, whose termwise derivative is established above. -/
theorem digammaReal_second_series {u : ℝ} (hu : 1 / 2 < u) :
    HasDerivAt (deriv digammaReal) (∑' n : ℕ, -2 * (u + n)⁻¹ ^ 3) u := by
  have he : deriv digammaReal =ᶠ[nhds u] (fun x : ℝ ↦ ∑' n : ℕ, (x + n)⁻¹ ^ 2) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    exact (digammaReal_hasDeriv hx).deriv
  exact (hasDerivAt_digamma_deriv_series hu).congr_of_eventuallyEq he

/-- At `79/100`, the second real derivative of digamma is strictly below
`-4573/1000`. The first eight nonnegative reciprocal-cube terms give an exact
rational lower bound for the positive series. This bounds the final signed
term in the sixth-pole Gamma operator. -/
theorem refined_digamma_second_upper :
    deriv (deriv digammaReal) (79 / 100) < -(4573 / 1000 : ℝ) := by
  have hu : (1 / 2 : ℝ) < 79 / 100 := by norm_num only
  have hp : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num only : (1 : ℝ) < 2))
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_two] using h
  have hpos (n : ℕ) : 0 ≤ 2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3 := by positivity
  have hs : Summable (fun n : ℕ ↦ 2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3) := by
    apply (hp.mul_left 16).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos n), ← inv_pow]
    exact inv_shift_cub_bound hu n
  have hsum := hs.sum_le_tsum (Finset.range 8) (fun n _ ↦ hpos n)
  have hd := (digammaReal_second_series hu).deriv
  rw [show
      (fun n : ℕ ↦ -2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3) =
        (fun n : ℕ ↦ -(2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3))
      from funext (fun n ↦ by ring),
    tsum_neg] at hd
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one] at hsum
  linarith only [hsum, hd]

/-- For an even character and distance above `1/2`, the first derivative of
the shifted Gamma logarithmic derivative is one quarter of the derivative of
real digamma at the half-argument. The even Gamma formula holds locally and
the chain rule gives the scaling. -/
theorem gamma_even_deriv_identity {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) {u : ℝ}
    (hu : 1 / 2 < u) :
    deriv (fun v : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + v : ℝ) : ℂ)).re) u =
      deriv digammaReal (((1 / 2 : ℝ) + u) / 2) / 4 := by
  have hz : (1 / 2 : ℝ) < ((1 / 2 : ℝ) + u) / 2 := by linarith only [hu]
  have hd := (digammaReal_hasDeriv hz).deriv
  have hs :=
    (digammaReal_hasDeriv hz).comp u (((hasDerivAt_id u).const_add (1 / 2 : ℝ)).div_const 2)
  have ht := (hs.sub_const (Real.log Real.pi)).div_const 2
  simp only [Function.comp_def, id_eq] at ht
  have heq :
    (fun v : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + v : ℝ) : ℂ)).re) =ᶠ[nhds u]
      (fun v : ℝ ↦ (digammaReal (((1 / 2 : ℝ) + v) / 2) - Real.log Real.pi) / 2) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    change (1 / 2 : ℝ) < v at hv
    have hv0 : (0 : ℝ) < 1 / 2 + v := by linarith only [hv]
    exact AnalyticNumberTheory.DirichletLFunction.re_gammaFactor_even he hv0
  rw [heq.deriv_eq, ht.deriv, hd]
  ring

/-- For an even character, the second derivative of the shifted real Gamma
logarithmic derivative at `27/25` is below `-4573/8000`. Differentiate the
local half-argument formula and apply the certified digamma bound. -/
theorem refined_gamma_even_second_upper {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    deriv (deriv (fun u : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re)) (27 / 25) <
      -(4573 / 8000 : ℝ) := by
  have ha : (1 / 2 : ℝ) < 27 / 25 := by norm_num only
  have hz : (1 / 2 : ℝ) < 79 / 100 := by norm_num only
  have hc : (((1 / 2 : ℝ) + 27 / 25) / 2 : ℝ) = 79 / 100 := by norm_num only
  have heq :
    deriv
        (fun u : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) =ᶠ[nhds (27 / 25 : ℝ)]
      (fun u : ℝ ↦ deriv digammaReal (((1 / 2 : ℝ) + u) / 2) / 4) := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    exact gamma_even_deriv_identity he hu
  have hd := digammaReal_second_series hz
  rw [← hc] at hd
  have hd' :=
    (hd.comp (27 / 25 : ℝ)
          (((hasDerivAt_id (27 / 25 : ℝ)).const_add (1 / 2 : ℝ)).div_const 2)).div_const
      4
  simp only [Function.comp_def, id_eq, hc] at hd'
  have hnum := refined_digamma_second_upper
  have hsecond : deriv (deriv digammaReal) (79 / 100) = ∑' n : ℕ, -2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3 :=
    (digammaReal_second_series hz).deriv
  rw [heq.deriv_eq, hd'.deriv]
  linarith only [hnum, hsecond]

/-- The full normalized sixth-pole Gamma correction of an even character
is strictly below `-(18/5)(27/25)^5`. The point, first derivative and second
derivative bounds give an exact rational inequality. This removes the Gamma
numerical hypothesis from the three-character zero-mass bound when all three
characters are even. -/
theorem refined_gamma_even_upper {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    sixGamma χ < -(18 / 5 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h0 := refined_gamma_even_point_lt he
  have h1 := refined_gamma_even_deriv_lower he
  have h2 := refined_gamma_even_second_upper he
  unfold sixGamma
  norm_num only at h0 h1 h2 ⊢
  linarith only [h0, h1, h2]

/-- For three even primitive nonprincipal characters under individual RH,
the refined zero-mass bound has the numerical correction `6.366`, provided
the stated universal Euler-total and finite-prefix estimates hold. The
certified even Gamma bound discharges the former Gamma hypothesis. -/
theorem refined_three_mass_even_numeric {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even)
    {X : ℝ} (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1)
    (hE :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) <
        (53 / 25 : ℝ) * (27 / 25 : ℝ) ^ 5)
    (hprefix :
      (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5 <
        ∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hΓA := refined_gamma_even_upper heA
  have hΓB := refined_gamma_even_upper heB
  have hΓC := refined_gamma_even_upper heC
  have hΓ : sixGamma a + sixGamma b + sixGamma c ≤ -(54 / 5 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    linarith only [hΓA, hΓB, hΓC]
  exact
    refined_three_mass_numeric a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC s hS
      ht hA hB hC hΓ hE hprefix

end PseudoPrime.PrimeTestBounds.MillerRabin
