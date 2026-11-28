/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWindow576

/-! # Abel summation on the wide triangle of section 76 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A smooth triangle branch with logarithmic intercept a and slope b, divided
by the square root of its argument, for Abel summation on positive intervals. -/
noncomputable def triangleLogBranch (a b t : ℝ) : ℝ :=
  (a + b * Real.log t) / Real.sqrt t

/-- Abel summation on one positive branch expresses its Mangoldt sum through
the endpoint values of psi and the integral of psi times the branch derivative. -/
theorem triangle_branch_abel {l u : ℝ} (hl : 0 < l) (hu : l ≤ u) (a b : ℝ) :
    (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊u⌋₊, triangleLogBranch a b n * ArithmeticFunction.vonMangoldt n) =
      triangleLogBranch a b u * Chebyshev.psi u - triangleLogBranch a b l * Chebyshev.psi l -
        ∫ t in l..u, deriv (triangleLogBranch a b) t * Chebyshev.psi t := by
  have hc {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ 1 (triangleLogBranch a b) x := by
    have hs : ContDiffAt ℝ 1 Real.sqrt x := Real.contDiffAt_sqrt hx.ne'
    unfold triangleLogBranch
    fun_prop (disch := positivity)
  have hd : ContDiffOn ℝ 1 (triangleLogBranch a b) (Set.Ioi 0) := fun x hx =>
    (hc hx).contDiffWithinAt
  have hi :=
    (hd.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (show Set.Icc l u ⊆ Set.Ioi 0 from fun x hx => hl.trans_le hx.1)
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt hl.le hu
      (fun x hx => (hc (hl.trans_le hx.1)).differentiableAt (by decide)) hi.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hu] at h
  simpa only [← Chebyshev.psi_eq_sum_Icc] using h

/-- At logarithmic origin v, both triangle branches vanish at the outer
endpoints and agree at the peak. Their joined Abel formula has no boundary term. -/
theorem triangle_joined_abel (v : ℝ) :
    let l := Real.exp v
    let m := Real.exp (v + 5 / 2)
    let u := Real.exp (v + 5)
    let f := triangleLogBranch (-(2 * v / 5)) (2 / 5)
    let g := triangleLogBranch (2 + 2 * v / 5) (-(2 / 5))
    (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊m⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ Finset.Ioc ⌊m⌋₊ ⌊u⌋₊, g n * ArithmeticFunction.vonMangoldt n) =
      -(∫ t in l..m, deriv f t * Chebyshev.psi t) - ∫ t in m..u, deriv g t * Chebyshev.psi t := by
  dsimp only
  rw [triangle_branch_abel (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith only)),
    triangle_branch_abel (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith only))]
  simp only [triangleLogBranch, Real.log_exp]
  ring

/-- Differentiating a smooth branch exposes its affine logarithmic variation
and the common factor that cancels against the psi envelope and Jacobian. -/
theorem triangle_branch_deriv (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (triangleLogBranch a b) t = (b - (a + b * Real.log t) / 2) / (t * Real.sqrt t) := by
  have hs := Real.sqrt_pos.mpr ht
  have h :=
    (((Real.hasDerivAt_log ht.ne').const_mul b).const_add a).div (Real.hasDerivAt_sqrt ht.ne')
      hs.ne'
  apply h.deriv.trans
  field_simp [ht.ne', hs.ne']
  rw [Real.sq_sqrt ht.le]
  ring

/-- In logarithmic coordinates the Jacobian and the square-root psi envelope
cancel the denominator of the absolute branch derivative exactly. -/
theorem triangle_branch_variation (a b y : ℝ) :
    |deriv (triangleLogBranch a b) (Real.exp y)| *
        (Real.sqrt (Real.exp y) * (Real.log (Real.exp y)) ^ 2 / 24) *
        Real.exp y =
      y ^ 2 * |b - (a + b * y) / 2| / 24 := by
  have ht := Real.exp_pos y
  have hs := Real.sqrt_pos.mpr ht
  rw [triangle_branch_deriv a b ht, abs_div, abs_of_pos (mul_pos ht hs), Real.log_exp]
  field_simp [ht.ne', hs.ne']

/-- On the range of the RH psi estimate the centered Abel integrand in
logarithmic coordinates is bounded by the triangle variation density. -/
theorem triangle_branch_psi_error (hRH : RiemannHypothesis) (a b y : ℝ) (hy : 101 ≤ Real.exp y) :
    |deriv (triangleLogBranch a b) (Real.exp y) * (Chebyshev.psi (Real.exp y) - Real.exp y)| *
        Real.exp y ≤
      y ^ 2 * |b - (a + b * y) / 2| / 24 := by
  rw [← triangle_branch_variation, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos y).le
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [mul_div_assoc] using psi_log_sq_of_RH hRH hy

/-- The main Abel integral on a positive branch has an elementary primitive.
Evaluating it at both ends keeps the peak term for the joined triangle. -/
theorem triangle_branch_main (a b : ℝ) {l u : ℝ} (hl : 0 < l) (hu : l ≤ u) :
    (∫ t in l..u, deriv (triangleLogBranch a b) t * t) =
      Real.sqrt u * (4 * b - a - b * Real.log u) - Real.sqrt l * (4 * b - a - b * Real.log l) := by
  have hd (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x => Real.sqrt x * (4 * b - a - b * Real.log x))
      ((b - (a + b * Real.log t) / 2) / Real.sqrt t) t := by
    have h :=
      (Real.hasDerivAt_sqrt ht.ne').mul
        (((Real.hasDerivAt_log ht.ne').const_mul b).const_sub (4 * b - a))
    apply h.congr_deriv
    field_simp [ht.ne', (Real.sqrt_pos.mpr ht).ne']
    nlinarith only [congrArg (fun x : ℝ => b * x) (Real.sq_sqrt ht.le)]
  have hc :
    ContinuousOn (fun t => (b - (a + b * Real.log t) / 2) / Real.sqrt t) (Set.uIcc l u) := by
    rw [Set.uIcc_of_le hu]
    apply ContinuousOn.div
    · exact
        continuousOn_const.sub
          ((continuousOn_const.add
                (continuousOn_const.mul
                  (Real.continuousOn_log.mono
                    (fun t (ht : t ∈ Set.Icc l u) => (hl.trans_le ht.1).ne')))).div_const
            2)
    · exact Real.continuous_sqrt.continuousOn
    · exact fun t ht => (Real.sqrt_pos.mpr (hl.trans_le ht.1)).ne'
  rw [←
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (hl.trans_le ((Set.uIcc_of_le hu ▸ ht : t ∈ Set.Icc l u).1)))
      hc.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hu] at ht
  have hp := hl.trans_le ht.1
  dsimp only
  rw [triangle_branch_deriv a b hp]
  field_simp [hp.ne', (Real.sqrt_pos.mpr hp).ne']

/-- The two main Abel integrals combine to the exact section 76 coefficient
times the radius; the sign is the minus sign of partial summation. -/
theorem triangle_joined_main {r : ℝ} (hr : 0 < r) :
    let v := 2 * Real.log r
    let M := fun a b l u : ℝ =>
      ∫ t in Real.exp (v + l)..Real.exp (v + u), deriv (triangleLogBranch a b) t * t
    0 - (M (-(2 * v / 5)) (2 / 5) 0 (5 / 2)) - M (2 + 2 * v / 5) (-(2 / 5)) (5 / 2) 5 =
      (8 / 5) * (Real.exp (5 / 4) - 1) ^ 2 * r := by
  intro v M
  dsimp only [M]
  rw [triangle_branch_main _ _ (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith only)),
    triangle_branch_main _ _ (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith only))]
  have hs (x : ℝ) : Real.sqrt (Real.exp (v + x)) = r * Real.exp (x / 2) := by
    rw [← Real.exp_half,
      show (v + x) / 2 = Real.log r + x / 2 by
        dsimp only [v]; ring,
      Real.exp_add, Real.exp_log hr]
  simp only [Real.log_exp, hs, zero_div, Real.exp_zero, mul_one]
  rw [show (5 / 2 : ℝ) / 2 = 5 / 4 by ring, show (5 / 2 : ℝ) = 5 / 4 + 5 / 4 by ring, Real.exp_add]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
