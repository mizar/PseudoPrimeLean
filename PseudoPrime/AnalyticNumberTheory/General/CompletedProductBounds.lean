/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EndpointRegularization
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import PseudoPrime.AnalyticNumberTheory.General.LogCoefficientBounds
public import PseudoPrime.AnalyticNumberTheory.General.ReflectedZeroCount

/-!
# Completed-product decomposition and local zero-count bounds

Separate the endpoint order, conductor, gamma factor, and arithmetic series
in the logarithmic derivative of a regularized completed function.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A nonzero complex base q contributes log(q)/2 to the logarithmic derivative
of q^(s/2). Differentiate the exponential power and cancel its nonzero value.
This separates the conductor term of a completed L-function. -/
theorem logDeriv_conductorPower {q : ℂ} (hq : q ≠ 0) (s : ℂ) :
    logDeriv (fun z ↦ q ^ (z / 2)) s = Complex.log q / 2 := by
  have hd := ((hasDerivAt_id' s).div_const 2).const_cpow (c := q) (Or.inl hq)
  have hp : q ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  rw [logDeriv_apply, hd.deriv]
  calc
    _ = (q ^ (s / 2) * (Complex.log q / 2)) / q ^ (s / 2) := by
      congr 1; ring
    _ = _ := mul_div_cancel_left₀ _ hp

/-- At a point where G and L are differentiable and nonzero, the completion
q^(s/2)*G(s)*L(s) has logarithmic derivative log(q)/2+G'/G+L'/L for q nonzero.
Apply the product rule twice and the conductor-power identity. This gives
the factor decomposition used in the explicit formula. -/
theorem logDeriv_completedProduct {q : ℂ} (hq : q ≠ 0) {G L : ℂ → ℂ} {s : ℂ} (hG : G s ≠ 0)
    (hL : L s ≠ 0) (hdG : DifferentiableAt ℂ G s) (hdL : DifferentiableAt ℂ L s) :
    logDeriv (fun z ↦ q ^ (z / 2) * G z * L z) s =
      Complex.log q / 2 + logDeriv G s + logDeriv L s := by
  have hp : q ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  have hd := ((hasDerivAt_id' s).div_const 2).const_cpow (c := q) (Or.inl hq)
  rw [logDeriv_fun_mul (f := fun z ↦ q ^ (z / 2) * G z) (g := L) s (mul_ne_zero hp hG) hL
      (hd.differentiableAt.mul hdG) hdL,
    logDeriv_fun_mul (f := fun z ↦ q ^ (z / 2)) (g := G) s hp hG hd.differentiableAt hdG,
    logDeriv_conductorPower hq]

/-- Away from zero and one, the regularized completion with integer order k
has logarithmic derivative k*(1/s+1/(s-1))+log(q)/2+G'/G+L'/L.
Require the regularization identity only off the endpoints and differentiable
nonzero factors at the evaluation point. The endpoint and completion product
rules give the decomposition for subsequent estimates. -/
theorem logDeriv_regularizedCompletion {F G L : ℂ → ℂ} {q : ℂ} (hq : q ≠ 0) (k : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * (q ^ (z / 2) * G z * L z)) {s : ℂ}
    (hs : s ≠ 0) (h1 : s ≠ 1) (hG : G s ≠ 0) (hL : L s ≠ 0) (hdG : DifferentiableAt ℂ G s)
    (hdL : DifferentiableAt ℂ L s) :
    logDeriv F s =
      (k : ℂ) * (1 / s + 1 / (s - 1)) + Complex.log q / 2 + logDeriv G s + logDeriv L s := by
  have hp : q ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  have hd := ((hasDerivAt_id' s).div_const 2).const_cpow (c := q) (Or.inl hq)
  rw [logDeriv_eq_of_endpointRegularization k hreg hs h1,
    logDeriv_endpointRegularization (L := fun z ↦ q ^ (z / 2) * G z * L z) k hs h1
      (mul_ne_zero (mul_ne_zero hp hG) hL) ((hd.differentiableAt.mul hdG).mul hdL),
    logDeriv_completedProduct hq hG hL hdG hdL]
  ring

/-- On Re s>=2, the integer endpoint correction has norm at most 2*abs(k).
Both s and s-1 have norm at least one, so their reciprocal norms are at most
one. The triangle inequality then controls their sum. This gives a height
independent endpoint contribution to the local zero count. -/
theorem norm_endpointLogDeriv_le (k : ℤ) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(k : ℂ) * (1 / s + 1 / (s - 1))‖ ≤ 2 * |(k : ℝ)| := by
  have hn : 1 ≤ ‖s‖ := (by linarith only [hs] : (1 : ℝ) ≤ s.re).trans (Complex.re_le_norm s)
  have ht : 1 ≤ ‖s - 1‖ := by
    have hh := Complex.re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re] at hh
    linarith only [hs, hh]
  have hsn : 0 < ‖s‖ := zero_lt_one.trans_le hn
  have htn : 0 < ‖s - 1‖ := zero_lt_one.trans_le ht
  have hb : ‖1 / s + 1 / (s - 1)‖ ≤ 2 := by
    have htri := norm_add_le (1 / s) (1 / (s - 1))
    simp only [one_div, norm_inv] at htri
    have hsi := (inv_le_one₀ hsn).mpr hn
    have hti := (inv_le_one₀ htn).mpr ht
    simp only [one_div]
    linarith only [htri, hsi, hti]
  rw [norm_mul, Complex.norm_intCast]
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- For natural conductor q>=1 and degree d, suppose the logarithmic-derivative
series coefficients satisfy norm(a n)<=d*n*log n and represent -L'/L at
Re s=3. A completion with differentiable nonzero factors then has regularized
logarithmic derivative bounded by 2*abs(k)+log(q)/2+norm(G'/G)+d*sum(log n/n^2).
Use the exact factor decomposition, endpoint bound, and convergent arithmetic
majorant. Only the gamma-factor contribution remains unevaluated. -/
theorem norm_logDeriv_regularizedCompletion_at_three_le {F G L : ℂ → ℂ} {q d : ℕ} (hq : 1 ≤ q)
    (k : ℤ) (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * G z * L z))
    {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) {s : ℂ} (hs : s.re = 3) (hG : G s ≠ 0)
    (hL : L s ≠ 0) (hdG : DifferentiableAt ℂ G s) (hdL : DifferentiableAt ℂ L s)
    (hlog : logDeriv L s = -LSeries a s) :
    ‖logDeriv F s‖ ≤
      2 * |(k : ℝ)| + Real.log q / 2 + ‖logDeriv G s‖ +
        (d : ℝ) * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq))
  have hsn : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    norm_num only at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    norm_num only at hs
  have hf := logDeriv_regularizedCompletion hqC k hreg hsn hs1 hG hL hdG hdL
  have he :=
    norm_endpointLogDeriv_le k
      (show 2 ≤ s.re from by
        rw [hs]; norm_num only)
  have hc : ‖Complex.log (q : ℂ) / 2‖ = Real.log q / 2 := by
    rw [norm_div, ← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg q), Complex.norm_ofNat]
  have hl := (summable_series_and_norm_le_log_majorant ha hs).2
  have hLn : ‖logDeriv L s‖ ≤ (d : ℝ) * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
    rw [hlog, norm_neg]
    exact hl
  let A := (k : ℂ) * (1 / s + 1 / (s - 1))
  have htri1 := norm_add_le A (Complex.log (q : ℂ) / 2)
  have htri2 := norm_add_le (A + Complex.log (q : ℂ) / 2) (logDeriv G s)
  have htri3 := norm_add_le (A + Complex.log (q : ℂ) / 2 + logDeriv G s) (logDeriv L s)
  rw [hf]
  change ‖A + Complex.log (q : ℂ) / 2 + logDeriv G s + logDeriv L s‖ ≤ _
  change ‖A‖ ≤ 2 * |(k : ℝ)| at he
  linarith only [he, hc, hLn, htri1, htri2, htri3]

/-- An entire regularized completion of order at most one, nonzero at zero
and in Re s>1, satisfying the conjugate functional equation has local zero
count bounded by ten times the endpoint, conductor, gamma, and arithmetic
contributions at 3+iT. The logarithmic-derivative series identity and its
coefficient bound are explicit inputs. Combine the reflected local-count
identity with the completion estimate. This reduces the analytic estimate
in Proposition 5.7 to a gamma logarithmic-derivative bound. -/
theorem localZeroCount_le_completedProductBound {F G L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q)
    (k : ℤ) (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * G z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (T : ℝ)
    (hG : G (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0) (hL : L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdG : DifferentiableAt ℂ G (((3 : ℝ) : ℂ) + T * Complex.I))
    (hdL : DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I)) :
    (∑' ρ : ℂ, localZeroMultiplicity F T ρ) ≤
      10 *
        (2 * |(k : ℝ)| + Real.log q / 2 + ‖logDeriv G (((3 : ℝ) : ℂ) + T * Complex.I)‖ +
          (d : ℝ) * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) := by
  have hs : ((((3 : ℝ) : ℂ) + T * Complex.I)).re = 3 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  have hc := (localZeroCount_bound_of_orderAtMostOne hε hfe hright hF h0 horder T).2
  have hn := norm_logDeriv_regularizedCompletion_at_three_le hq k hreg ha hs hG hL hdG hdL hlog
  exact
    hc.trans
      ((mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num only)).trans
        (mul_le_mul_of_nonneg_left hn (by norm_num only)))

/-- Away from both endpoints, a regularized completion with differentiable
completed and gamma factors and nonzero conductor and gamma value determines
a differentiable ordinary factor. Express that factor locally as the completed
function divided by the regularizing and completion factors, whose denominator
is differentiable and nonzero. This derives ordinary differentiability for
applying the completion logarithmic-derivative decomposition. -/
theorem differentiableAt_of_regularizedCompletion {F G L : ℂ → ℂ} {q : ℂ} (hq : q ≠ 0) (k : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * (q ^ (z / 2) * G z * L z)) {s : ℂ}
    (hs : s ≠ 0) (h1 : s ≠ 1) (hG : G s ≠ 0) (hdF : DifferentiableAt ℂ F s)
    (hdG : DifferentiableAt ℂ G s) : DifferentiableAt ℂ L s := by
  let D : ℂ → ℂ := fun z ↦ (z * (1 - z)) ^ k * (q ^ (z / 2) * G z)
  have hsn : s * (1 - s) ≠ 0 := mul_ne_zero hs (sub_ne_zero.mpr h1.symm)
  have hdq := ((hasDerivAt_id' s).div_const 2).const_cpow (c := q) (Or.inl hq)
  have hdid : DifferentiableAt ℂ (fun z : ℂ ↦ z) s := differentiableAt_id
  have hdD : DifferentiableAt ℂ D s :=
    ((hdid.mul (hdid.const_sub (1 : ℂ))).zpow (m := k) (Or.inl hsn)).mul
      (hdq.differentiableAt.mul hdG)
  have hD : D s ≠ 0 :=
    mul_ne_zero (zpow_ne_zero k hsn) (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hq)) hG)
  apply (hdF.div hdD hD).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hs, eventually_ne_nhds h1,
    hdD.continuousAt.eventually_ne hD] with z hz hz1 hDz
  dsimp only [Pi.div_apply]
  apply (eq_div_iff hDz).mpr
  rw [hreg z hz hz1]
  dsimp only [D]
  ring

/-- Away from both endpoints, nonvanishing of a regularized completed value
forces the ordinary factor to be nonzero. A zero ordinary factor would make
the product identity vanish. This supplies ordinary nonvanishing from the
right-half-plane nonvanishing of the completion. -/
theorem ne_zero_of_regularizedCompletion {F G L : ℂ → ℂ} {q : ℂ} (k : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * (q ^ (z / 2) * G z * L z)) {s : ℂ}
    (hs : s ≠ 0) (h1 : s ≠ 1) (hF : F s ≠ 0) : L s ≠ 0 := by
  intro hL
  apply hF
  simp only [hreg s hs h1, hL, mul_zero]

end PseudoPrime.AnalyticNumberTheory.General
