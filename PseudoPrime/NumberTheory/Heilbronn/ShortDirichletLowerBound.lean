/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnDirichletKernel
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # A pointwise lower bound for the short Dirichlet kernel -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- If 32t<=N, the residue character at t has distance at most 1/2 from one.
Use the exponential remainder estimate and pi<4 without reducing t modulo N. -/
theorem norm_stdAddChar_nat_sub_one_le_half {N t : ℕ} [NeZero N] (ht : 32 * t ≤ N) :
    ‖ZMod.stdAddChar (t : ZMod N) - 1‖ ≤ (1 / 2 : ℝ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have htr : (32 : ℝ) * t ≤ N := by exact_mod_cast ht
  have harg : ‖2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (N : ℂ)‖ ≤ (1 / 4 : ℝ) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [Complex.norm_ofNat]
    apply (div_le_iff₀ hN).mpr
    have hp := Real.pi_lt_four.le
    have ht0 := Nat.cast_nonneg (α := ℝ) t
    nlinarith only [hp, ht0, htr]
  have he := Complex.norm_exp_sub_one_le (le_trans harg (by norm_num only))
  have htcast : (t : ZMod N) = ((t : ℤ) : ZMod N) := by rw [Int.cast_natCast]
  rw [htcast, ZMod.stdAddChar_coe, Int.cast_natCast]
  linarith only [he, harg]

/-- If 32Ha<=N, all character terms have real part at least 1/2.
Summing them gives (H+1)^2<=4 times the squared norm of the short Dirichlet sum. -/
theorem shortDirichletSum_normSq_lower {N H a : ℕ} [NeZero N] (hHa : 32 * H * a ≤ N) :
    (H + 1 : ℝ) ^ 2 ≤ 4 * Complex.normSq (shortDirichletSum H (a : ZMod N)) := by
  have hterm (j : ℤ) (hj : j ∈ Finset.Icc (0 : ℤ) H) :
    (1 / 2 : ℝ) ≤ (ZMod.stdAddChar ((a : ZMod N) * (j : ZMod N))).re := by
    have hb := Finset.mem_Icc.mp hj
    have hnat : j.toNat ≤ H := Int.toNat_le.mpr hb.2
    have ht : 32 * (a * j.toNat) ≤ N := by
      calc
        _ = 32 * j.toNat * a := by ring
        _ ≤ 32 * H * a := Nat.mul_le_mul_right a (Nat.mul_le_mul_left 32 hnat)
        _ ≤ N := hHa
    have h := norm_stdAddChar_nat_sub_one_le_half ht
    have he : (a : ZMod N) * (j : ZMod N) = ((a * j.toNat : ℕ) : ZMod N) := by
      have hjcast : (j : ZMod N) = (j.toNat : ZMod N) := by
        simpa only [Int.cast_natCast] using
          congrArg (fun t : ℤ ↦ (t : ZMod N)) (Int.toNat_of_nonneg hb.1).symm
      rw [Nat.cast_mul, hjcast]
    have hr := Complex.re_le_norm ((1 : ℂ) - ZMod.stdAddChar ((a : ZMod N) * (j : ZMod N)))
    rw [he, norm_sub_rev] at hr
    simp only [Complex.sub_re, Complex.one_re] at hr
    rw [he]
    linarith only [hr, h]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Int.card_Icc, sub_zero, ← Int.natCast_one, ← Nat.cast_add,
    Int.toNat_natCast, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  have hre : (H + 1 : ℝ) / 2 ≤ (shortDirichletSum H (a : ZMod N)).re := by
    rw [shortDirichletSum, Complex.re_sum]
    linarith only [hsum]
  have hr := Complex.re_le_norm (shortDirichletSum H (a : ZMod N))
  have hn := norm_nonneg (shortDirichletSum H (a : ZMod N))
  rw [Complex.normSq_eq_norm_sq]
  nlinarith only [hre, hr, hn, Nat.cast_nonneg (α := ℝ) H]

end PseudoPrime.NumberTheory.Heilbronn
