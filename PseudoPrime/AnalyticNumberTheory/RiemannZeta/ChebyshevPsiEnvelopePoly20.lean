/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiScale20

/-! # Polynomial-exponential decay above logarithmic height 20 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Differentiate the cubic envelope majorant multiplied by `exp(-t/2)`.
The explicit derivative supports a uniform estimate above height 20. -/
private theorem envelope_poly20_deriv {t : ℝ} :
    HasDerivAt
      (fun x : ℝ ↦
        (25 * x ^ 3 / 2512 - 175 * x ^ 2 / 2512 + 43137 * x / 251200 + 46 / 25) * Real.exp (-x / 2))
      ((75 * t ^ 2 / 2512 - 350 * t / 2512 + 43137 / 251200 -
          (25 * t ^ 3 / 2512 - 175 * t ^ 2 / 2512 + 43137 * t / 251200 + 46 / 25) / 2) *
        Real.exp (-t / 2))
      t := by
  have hi := hasDerivAt_id t
  have hp1 := ((hi.pow 3).const_mul 25).div_const 2512
  have hp2 := ((hi.pow 2).const_mul 175).div_const 2512
  have hp3 := (hi.const_mul 43137).div_const 251200
  have hp := ((hp1.sub hp2).add hp3).add_const (46 / 25)
  have he := (Real.hasDerivAt_exp (-t / 2)).comp t ((hi.neg).div_const 2)
  have hh := hp.mul he
  convert hh using 1
  · funext x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Pi.neg_apply,
      Function.comp_apply, id_eq]
  · simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Pi.neg_apply, Function.comp_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

/-- Above `L = 20`, the polynomial-exponential majorant and `exp(-L)/5`
sum to at most `3/1000`. The cubic product decreases on this half-line and
the exponential at the endpoint exceeds 22000. -/
theorem envelope_poly20_bound {L : ℝ} (hL : 20 ≤ L) :
    (25 * L ^ 3 / 2512 - 175 * L ^ 2 / 2512 + 43137 * L / 251200 + 46 / 25) * Real.exp (-L / 2) +
        Real.exp (-L) / 5 ≤
      3 / 1000 := by
  have hmono :
    AntitoneOn
      (fun x : ℝ ↦
        (25 * x ^ 3 / 2512 - 175 * x ^ 2 / 2512 + 43137 * x / 251200 + 46 / 25) * Real.exp (-x / 2))
      (Set.Ici (20 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro t ht
      exact envelope_poly20_deriv.continuousAt.continuousWithinAt
    · intro t ht
      exact envelope_poly20_deriv.differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : (20 : ℝ) ≤ t := interior_subset ht
      rw [envelope_poly20_deriv.deriv]
      have h1 : 0 ≤ t - 20 := by linarith only [ht']
      have h2 : 0 ≤ (t - 20) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ (t - 20) ^ 3 := pow_nonneg h1 _
      have hq :
        (75 * t ^ 2 / 2512 - 350 * t / 2512 + 43137 / 251200) -
            (25 * t ^ 3 / 2512 - 175 * t ^ 2 / 2512 + 43137 * t / 251200 + 46 / 25) / 2 ≤
          0 := by
        nlinarith only [h1, h2, h3]
      exact mul_nonpos_of_nonpos_of_nonneg hq (Real.exp_pos _).le
  have hm := hmono (show (20 : ℝ) ∈ Set.Ici (20 : ℝ) from le_rfl) hL hL
  have he0 : Real.exp (-(20 : ℝ) / 2) ≤ 1 / 22000 := by
    rw [show (-(20 : ℝ) / 2) = -10 by norm_num only, Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num only : (0 : ℝ) < 22000)).2 exp_ten_ge_22000
  have heL : Real.exp (-L) ≤ (1 / 22000 : ℝ) ^ 2 := by
    have hhalf : Real.exp (-L / 2) ≤ (1 / 22000 : ℝ) := by
      have h := Real.exp_le_exp.mpr (show -L / 2 ≤ -(20 : ℝ) / 2 by linarith only [hL])
      exact h.trans he0
    have hp : 0 ≤ Real.exp (-L / 2) := (Real.exp_pos _).le
    have hs := mul_le_mul hhalf hhalf hp (by norm_num only : (0 : ℝ) ≤ 1 / 22000)
    have he : Real.exp (-L) = Real.exp (-L / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    nlinarith only [hs]
  have hP :
    0 ≤
      (25 * (20 : ℝ) ^ 3 / 2512 - 175 * (20 : ℝ) ^ 2 / 2512 + 43137 * (20 : ℝ) / 251200 +
        46 / 25) := by
    norm_num only
  have hmul := mul_le_mul_of_nonneg_left he0 hP
  nlinarith only [hm, hmul, heL]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
