/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelZeroMass
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedZeroHeightTests
public import Mathlib.Topology.UrysohnsLemma

/-!
# Sharp conductor-uniform Mellin-kernel zero mass

Use compact continuous height tests and completed-zero equidistribution for
bounded heights. The previously proved uniform tails then give the full mass bound.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For an admissible Mellin kernel, the norm of its restriction to the imaginary
axis is continuous. The axis lies in the holomorphic region away from the possible
pole at -1/2. This supplies continuous compact cutoffs of the absolute kernel. -/
theorem continuous_norm_imaginary_axis (K : MellinKernel) :
    Continuous (fun t : ℝ ↦ ‖K.function (Complex.I * t)‖) := by
  apply Continuous.norm
  apply continuous_iff_continuousAt.mpr
  intro t
  have hr : Complex.I * (t : ℂ) ∈ K.region := by
    apply K.strip_subset
    simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    constructor <;> linarith only [K.delta_pos]
  have hn : Complex.I * (t : ℂ) ≠ (-1 / 2 : ℂ) := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re] at hh
    norm_num only at hh
  have hd :=
    K.holomorphic.differentiableAt ((K.region_open.sdiff isClosed_singleton).mem_nhds ⟨hr, hn⟩)
  have hline : Continuous (fun t : ℝ ↦ Complex.I * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  exact hd.continuousAt.comp (f := fun t : ℝ ↦ Complex.I * (t : ℂ)) hline.continuousAt

/-- For a nonprincipal character, an absolute kernel zero term is its natural
completed-zero multiplicity times the kernel norm at the height. Entire completion
identifies the divisor with analytic order. This connects the LLS ledger to height tests. -/
theorem norm_kernelZeroTerm_eq_order_mul (K : MellinKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (ρ : ℂ) :
    ‖K.kernelZeroTerm χ ρ‖ =
      (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖K.function (Complex.I * ρ.im)‖ := by
  rw [kernelZeroTerm,
    AnalyticNumberTheory.DirichletLFunction.completed_divisor_eq_analyticOrderNatAt hne,
    Int.cast_natCast, norm_mul, norm_natCast]

/-- For a nonprincipal character and any cutoff height, the truncated absolute
kernel sum over the complex plane equals the natural-multiplicity sum over actual
completed zeros. Terms vanish outside the zero set. This permits applying the
continuous-test zero-distribution estimate to the LLS zero ledger. -/
theorem tsum_truncated_norm_kernelZeroTerm_eq_completedZero_sum (K : MellinKernel) {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (T : ℝ) :
    (∑' ρ : ℂ, if |ρ.im| < T then ‖K.kernelZeroTerm χ ρ‖ else 0) =
      ∑' ρ : AnalyticNumberTheory.DirichletLFunction.CompletedZero χ,
        if |(ρ : ℂ).im| < T then
          (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) *
            ‖K.function (Complex.I * (ρ : ℂ).im)‖
        else 0 := by
  simp_rw [norm_kernelZeroTerm_eq_order_mul K hne]
  symm
  apply
    tsum_subtype_eq_of_support_subset (s := {ρ : ℂ | χ.completedLFunction ρ = 0}) (f := fun ρ : ℂ ↦
      if |ρ.im| < T then
        (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖K.function (Complex.I * ρ.im)‖
      else 0)
  intro ρ hρ
  by_contra hn
  have ho : analyticOrderNatAt χ.completedLFunction ρ = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
  exact hρ (by simp only [ho, Nat.cast_zero, zero_mul, ite_self])

open AnalyticNumberTheory.DirichletLFunction in
/-- For an admissible kernel, positive height cutoff and positive error, sufficiently
large moduli bound the truncated absolute zero sum by (kernel mass+error)*log(q),
uniformly over primitive nonprincipal characters under individual RH. Choose a
continuous compact cutoff equal to one on the height interval and between zero
and one elsewhere. Apply completed-zero height convergence and bound its integral
by the full kernel norm integral. This proves the compact input of the sharp mass bound. -/
theorem exists_uniform_truncated_kernelZeroSum_le_mass (K : MellinKernel) (T : ℝ) (_hT : 0 < T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                (∑' ρ : ℂ, if |ρ.im| < T then ‖K.kernelZeroTerm χ ρ‖ else 0) ≤
                  (K.mass + δ) * Real.log q := by
  obtain ⟨f, hf, _, hc, h01⟩ :=
    exists_continuous_one_zero_of_isCompact (s := Set.Icc (-T) T) (t := (∅ : Set ℝ)) isCompact_Icc
      isClosed_empty (Set.disjoint_empty _)
  let g : ℝ → ℝ := fun t ↦ f t * ‖K.function (Complex.I * t)‖
  have hg : Continuous g := f.continuous.mul (continuous_norm_imaginary_axis K)
  have hcg : HasCompactSupport g := hc.mul_right
  have hpos : ∀ t, 0 ≤ g t := fun t ↦ mul_nonneg (h01 t).1 (norm_nonneg _)
  have hle : ∀ t, g t ≤ ‖K.function (Complex.I * t)‖ := fun t ↦
    (mul_le_mul_of_nonneg_right (h01 t).2 (norm_nonneg _)).trans_eq (one_mul _)
  have hik : MeasureTheory.Integrable (fun t : ℝ ↦ ‖K.function (Complex.I * t)‖) := by
    have hi := (integrable_line K (c := 0) (by norm_num only) (by linarith only [K.delta_pos])).norm
    simpa only [Complex.ofReal_zero, zero_add] using hi
  have hint := MeasureTheory.integral_mono (hg.integrable_of_hasCompactSupport hcg) hik hle
  have hmass : (∫ t : ℝ, g t) / (2 * Real.pi) ≤ K.mass :=
    div_le_div_of_nonneg_right hint (mul_nonneg (by norm_num only) Real.pi_pos.le)
  obtain ⟨Q, hQ, hb⟩ := exists_uniform_completedZero_real_height_test_upper_bound g hg hcg hδ
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hscomplex :=
    summable_completedZero_height_test (hQ.trans hq) hRH hp hne hinv (fun t ↦ (g t : ℂ))
      (Complex.continuous_ofReal.comp hg) (hcg.comp_left Complex.ofReal_zero)
  have hs :
    Summable
      (fun ρ : CompletedZero χ ↦
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) * g (ρ : ℂ).im) := by
    apply hscomplex.norm.congr
    intro ρ
    simp only [norm_mul, norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hpos (ρ : ℂ).im)]
  have ht :
    ∀ ρ : CompletedZero χ,
      (if |(ρ : ℂ).im| < T then
          (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) *
            ‖K.function (Complex.I * (ρ : ℂ).im)‖
        else 0) ≤
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) * g (ρ : ℂ).im := by
    intro ρ
    split_ifs with hρ
    · have hone := hf ((abs_le.mp hρ.le) : (ρ : ℂ).im ∈ Set.Icc (-T) T)
      change f (ρ : ℂ).im = 1 at hone
      dsimp only [g]
      rw [hone, one_mul]
    · exact mul_nonneg (Nat.cast_nonneg _) (hpos _)
  have hinside :=
    Summable.of_nonneg_of_le
      (fun ρ : CompletedZero χ ↦ ite_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) le_rfl)
      ht hs
  rw [tsum_truncated_norm_kernelZeroTerm_eq_completedZero_sum K hne T]
  exact
    ((Summable.tsum_le_tsum ht hinside hs).trans (hb q hq χ hRH hp hne hinv)).trans
      (mul_le_mul_of_nonneg_right (add_le_add hmass (le_refl δ)) (Real.log_natCast_nonneg q))

/-- Under global GRH, every admissible Mellin kernel has its full absolute completed
zero sum bounded eventually by (1+epsilon)*kernel mass*log(q), uniformly over primitive
nonprincipal characters and their nonprincipal inverses. Supply the proved compact
height estimate to the uniform-tail reduction. No compact-mass hypothesis remains;
this is the sharp conductor coefficient required by Lemma 6.1. -/
theorem exists_uniform_kernelZeroSum_le_mass (K : MellinKernel)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ Q : ℕ,
          2 ≤ Q ∧
            ∀ (q : ℕ) [NeZero q],
              Q ≤ q →
                ∀ (χ : DirichletCharacter ℂ q),
                  χ.IsPrimitive →
                    χ ≠ 1 →
                    χ⁻¹ ≠ 1 →
                    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ (1 + ε) * K.mass * Real.log q := by
  apply exists_uniform_kernelZeroSum_le_mass_of_truncations K hGRH
  intro T hT δ hδ
  obtain ⟨Q, hQ, hb⟩ := exists_uniform_truncated_kernelZeroSum_le_mass K T hT hδ
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hp hne hinv
  exact hb q hq χ (hGRH q χ hp) hp hne hinv

end PseudoPrime.LLS.PaperStatements.MellinKernel
