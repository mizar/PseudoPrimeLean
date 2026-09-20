/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BasicBounds

/-!
# Left-half-plane logarithmic-derivative estimates

The Gamma integral gives `‖Γ(σ+it)‖ ≤ Γ(σ)` for positive `σ`.
Reflection and conjugation give `‖Γ(1+it)‖² = πt/sinh(πt)` for nonzero `t`.
On a pole-free disk, use a holomorphic primitive of digamma whose real part
is `log ‖Γ‖`, not the principal logarithm composed with Gamma.
Borel–Carathéodory and Cauchy estimates then bound digamma; recurrence and the
zeta functional equation yield logarithmic-derivative estimates on the left.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- If `Re z ≥ 1`, shifting `z` right by a natural number cannot decrease
`‖Γ z‖`: each recurrence factor has norm at least one. This reduces lower
bounds at arbitrary nonnegative real shifts to shifts in `[0,1)`. -/
theorem norm_Gamma_le_Gamma_add_nat {z : ℂ} (hz : 1 ≤ z.re) (n : ℕ) :
    ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + n)‖ := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero]; exact le_rfl
  | succ n
    ih =>
    have hzn_re : (z + (n : ℂ)).re = z.re + n := by simp only [Complex.add_re, Complex.natCast_re]
    have hzn_ne : z + (n : ℂ) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hzn_re] at hre
      simp only [Complex.zero_re] at hre
      have hzle : z.re ≤ z.re + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
      have hpos : (0 : ℝ) < z.re + (n : ℝ) :=
        lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hz) hzle
      exact (ne_of_gt hpos) hre
    have hrec : Complex.Gamma (z + ((n : ℕ) + 1 : ℕ)) = (z + (n : ℂ)) * Complex.Gamma (z + n) := by
      rw [show z + (((n : ℕ) + 1 : ℕ) : ℂ) = (z + (n : ℂ)) + 1 from by
          push_cast; ring,
        Complex.Gamma_add_one (z + (n : ℂ)) hzn_ne]
    rw [hrec, norm_mul]
    have h1 : (1 : ℝ) ≤ ‖z + (n : ℂ)‖ :=
      calc
        (1 : ℝ) ≤ z.re + n := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
        _ = (z + (n : ℂ)).re := hzn_re.symm
        _ ≤ ‖z + (n : ℂ)‖ := Complex.re_le_norm _
    calc
      ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + n)‖ := ih
      _ ≤ ‖z + (n : ℂ)‖ * ‖Complex.Gamma (z + n)‖ := by
        nlinarith only [norm_nonneg (Complex.Gamma (z + (n : ℂ))), h1]

/-- Exact identity for the squared norm of `Γ` on the line `Re s = 1`, via the reflection
formula, the recurrence relation, and the Schwarz reflection `Γ(conj s) = conj (Γ s)`. -/
theorem norm_Gamma_one_add_mul_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) := by
  have htI : (t : ℂ) * Complex.I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, ht, Complex.I_ne_zero, or_self,
      not_false_eq_true]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * Complex.I)
  have hadd := Complex.Gamma_add_one ((t : ℂ) * Complex.I) htI
  rw [show (t : ℂ) * Complex.I + 1 = 1 + (t : ℂ) * Complex.I from by ring] at hadd
  have hconjeq : (1 : ℂ) - (t : ℂ) * Complex.I = starRingEnd ℂ (1 + (t : ℂ) * Complex.I) := by
    simp only [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      Complex.ext_iff, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero,
      Complex.add_re, Complex.neg_re, neg_zero, add_zero, Complex.sub_im, Complex.one_im,
      Complex.mul_im, zero_sub, Complex.add_im, Complex.neg_im, zero_add, and_self]
  have hconjGamma :
    Complex.Gamma (1 - (t : ℂ) * Complex.I) =
      starRingEnd ℂ (Complex.Gamma (1 + (t : ℂ) * Complex.I)) := by
    rw [hconjeq, Complex.Gamma_conj]
  rw [hconjGamma] at hrefl
  have hstep :
    Complex.Gamma (1 + (t : ℂ) * Complex.I) *
        starRingEnd ℂ (Complex.Gamma (1 + (t : ℂ) * Complex.I)) =
      (t : ℂ) * Complex.I * (Real.pi : ℂ) /
        Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) := by
    calc
      Complex.Gamma (1 + (t : ℂ) * Complex.I) *
            starRingEnd ℂ (Complex.Gamma (1 + (t : ℂ) * Complex.I)) =
          (t : ℂ) * Complex.I * Complex.Gamma ((t : ℂ) * Complex.I) *
            starRingEnd ℂ (Complex.Gamma (1 + (t : ℂ) * Complex.I)) :=
        by rw [hadd]
      _ =
          (t : ℂ) * Complex.I *
            (Complex.Gamma ((t : ℂ) * Complex.I) *
              starRingEnd ℂ (Complex.Gamma (1 + (t : ℂ) * Complex.I))) :=
        by ring
      _ =
          (t : ℂ) * Complex.I *
            ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I))) :=
        by rw [hrefl]
      _ =
          (t : ℂ) * Complex.I * (Real.pi : ℂ) /
            Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) :=
        by ring
  have hnormSq :
    ((Complex.normSq (Complex.Gamma (1 + (t : ℂ) * Complex.I)) : ℝ) : ℂ) =
      (t : ℂ) * Complex.I * (Real.pi : ℂ) /
        Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    exact hstep
  have hsin :
    Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) =
      (Real.sinh (Real.pi * t) : ℂ) * Complex.I := by
    rw [show (Real.pi : ℂ) * ((t : ℂ) * Complex.I) = ((Real.pi * t : ℝ) : ℂ) * Complex.I from by
        push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [hsin] at hnormSq
  have hsinh_ne : Real.sinh (Real.pi * t) ≠ 0 := by
    rcases ht.lt_or_gt with h | h
    · exact ne_of_lt (Real.sinh_neg_iff.mpr (by nlinarith [Real.pi_pos]))
    · exact ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  have hrhs :
    (t : ℂ) * Complex.I * (Real.pi : ℂ) / ((Real.sinh (Real.pi * t) : ℂ) * Complex.I) =
      ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    push_cast
    field_simp [hsinh_ne]
  rw [hrhs] at hnormSq
  have hreal :
    Complex.normSq (Complex.Gamma (1 + (t : ℂ) * Complex.I)) =
      Real.pi * t / Real.sinh (Real.pi * t) := by
    exact_mod_cast hnormSq
  rw [← Complex.normSq_eq_norm_sq]
  exact hreal

/-- Elementary: `sinh x ≤ exp x` for `x ≥ 0`
(the zeta-side estimate groundwork, for a crude lower bound on `Γ`). -/
theorem sinh_le_exp {x : ℝ} (_hx : 0 ≤ x) : Real.sinh x ≤ Real.exp x := by
  rw [Real.sinh_eq]
  apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
  calc
    Real.exp x - Real.exp (-x) ≤ Real.exp x := sub_le_self _ (Real.exp_pos (-x)).le
    _ ≤ Real.exp x + Real.exp x := le_add_of_nonneg_right (Real.exp_pos x).le
    _ = Real.exp x * 2 := by ring

/-- A crude, explicit lower bound on `‖Γ(1+it)‖`, valid for all `t ≠ 0`: from the exact identity
`‖Γ(1+it)‖² = π|t|/sinh(π|t|)` and `sinh(π|t|) ≤ exp(π|t|)`.
Needed to bound the zeta-side estimate's left
vertical edge, whose integrand's dominant term is `-log‖Γ(1-it)‖` (real part `Re s = 1`, `t`
ranging over a growing interval). -/
theorem norm_Gamma_one_add_mul_I_ge {t : ℝ} (ht : t ≠ 0) :
    Real.sqrt (Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2)) ≤
      ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ := by
  have hsq := norm_Gamma_one_add_mul_I_sq ht
  have habs_pos : (0 : ℝ) < |t| := abs_pos.mpr ht
  have hEq : Real.pi * t / Real.sinh (Real.pi * t) = Real.pi * |t| / Real.sinh (Real.pi * |t|) := by
    rcases abs_cases t with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
    · rw [h1, show Real.pi * -t = -(Real.pi * t) from by ring, Real.sinh_neg]
      field_simp
  rw [hEq] at hsq
  have hsinh_pos : (0 : ℝ) < Real.sinh (Real.pi * |t|) := Real.sinh_pos_iff.mpr (by positivity)
  have hsinh_le : Real.sinh (Real.pi * |t|) ≤ Real.exp (Real.pi * |t|) :=
    sinh_le_exp (by positivity)
  have hlower :
    Real.pi * |t| * Real.exp (-(Real.pi * |t|)) ≤ Real.pi * |t| / Real.sinh (Real.pi * |t|) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hsinh_pos]
    nlinarith [mul_le_mul_of_nonneg_left hsinh_le (show (0 : ℝ) ≤ Real.pi * |t| by positivity)]
  have hsq_ge :
    Real.pi * |t| * Real.exp (-(Real.pi * |t|)) ≤ ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2 :=
    hsq ▸ hlower
  have hexp_sq : Real.exp (-(Real.pi * |t| / 2)) ^ 2 = Real.exp (-(Real.pi * |t|)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hrhs_eq :
    Real.pi * |t| * Real.exp (-(Real.pi * |t|)) =
      (Real.sqrt (Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hexp_sq]
  rw [hrhs_eq] at hsq_ge
  have hnn1 : (0 : ℝ) ≤ Real.sqrt (Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2)) := by positivity
  have hnn2 : (0 : ℝ) ≤ ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  have hroot := Real.sqrt_le_sqrt hsq_ge
  rwa [Real.sqrt_sq hnn1, Real.sqrt_sq hnn2] at hroot

/-- A crude, explicit upper bound on `-log‖Γ(1+it)‖`, valid for all `t ≠ 0`. -/
theorem neg_log_norm_Gamma_one_add_mul_I_le {t : ℝ} (ht : t ≠ 0) :
    -Real.log ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ≤
      Real.pi * |t| / 2 - Real.log (Real.sqrt (Real.pi * |t|)) := by
  have habs_pos : (0 : ℝ) < |t| := abs_pos.mpr ht
  have hlb := norm_Gamma_one_add_mul_I_ge ht
  have hlb_pos : (0 : ℝ) < Real.sqrt (Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
    positivity
  have hlog := Real.log_le_log hlb_pos hlb
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith only [hlog]

/-- `Γ` is differentiable (hence continuous) at every point `1 + it` (`t` real), since the real
part `1` is never a non-positive integer. -/
theorem differentiableAt_Gamma_one_add_mul_I (t : ℝ) :
    DifferentiableAt ℂ Complex.Gamma (1 + (t : ℂ) * Complex.I) := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  have hre := congrArg Complex.re hn
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.neg_re,
    Complex.natCast_re] at hre
  have hle : (1 : ℝ) + 0 ≤ 0 := hre.le.trans (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact (not_le_of_gt (by norm_num only : (0 : ℝ) < 1)) (by simpa only [add_zero] using hle)

/-- `t ↦ -log‖Γ(1+it)‖` is continuous, since `Γ` is differentiable (hence continuous) and
zero-free at every such point. -/
theorem continuous_neg_log_norm_Gamma_one_add_mul_I :
    Continuous (fun t : ℝ => -Real.log ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖) := by
  have haffine : Continuous fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I := by fun_prop
  have hgamma_cont : Continuous fun t : ℝ => Complex.Gamma (1 + (t : ℂ) * Complex.I) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    change ContinuousAt (Complex.Gamma ∘ fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) t
    exact
      ContinuousAt.comp ((differentiableAt_Gamma_one_add_mul_I t).continuousAt)
        (haffine.continuousAt (x := t))
  apply Continuous.neg
  apply Continuous.log hgamma_cont.norm
  intro t
  exact
    (norm_pos_iff.mpr
        (Complex.Gamma_ne_zero_of_re_pos
          (by
            simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
              Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
              zero_lt_one]))).ne'

/-- Continuity gives a fixed upper bound for `-log ‖Γ(1+it)‖` on `|t| ≤ 1`
by compactness. The constant is existential, not an evaluated numerical bound. -/
theorem exists_forall_neg_log_norm_Gamma_one_add_mul_I_le_of_abs_le_one :
    ∃ C₀ : ℝ, ∀ t : ℝ, |t| ≤ 1 → -Real.log ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ≤ C₀ := by
  have hcont := continuous_neg_log_norm_Gamma_one_add_mul_I.continuousOn (s := Set.Icc (-1 : ℝ) 1)
  obtain ⟨t₀, -, ht₀max⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc ⟨0, by constructor <;> norm_num only⟩ hcont
  rw [isMaxOn_iff] at ht₀max
  exact ⟨-Real.log ‖Complex.Gamma (1 + (t₀ : ℂ) * Complex.I)‖, fun t ht => ht₀max t (abs_le.mp ht)⟩

/-- A fixed constant `C₀` bounds `-log ‖Γ(1+it)‖` by `C₀+π|t|/2` for all
real `t`. Combine compactness on `|t| ≤ 1` with the hyperbolic-sine estimate outside. -/
theorem exists_neg_log_norm_Gamma_one_add_mul_I_le_uniform :
    ∃ C₀ : ℝ,
      ∀ t : ℝ, -Real.log ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ≤ C₀ + Real.pi * |t| / 2 := by
  obtain ⟨C₀, hC₀⟩ := exists_forall_neg_log_norm_Gamma_one_add_mul_I_le_of_abs_le_one
  refine ⟨max C₀ 0, fun t => ?_⟩
  by_cases ht : |t| ≤ 1
  · have h1 := hC₀ t ht
    have h2 : C₀ ≤ max C₀ 0 := le_max_left _ _
    have h3 : (0 : ℝ) ≤ Real.pi * |t| / 2 := by positivity
    linarith only [h1, h2, h3]
  · rw [not_le] at ht
    have htne : t ≠ 0 := by
      intro h
      rw [h] at ht
      norm_num only at ht
    have hb := neg_log_norm_Gamma_one_add_mul_I_le htne
    have hpi1 : (1 : ℝ) ≤ Real.pi * |t| := by nlinarith only [Real.pi_gt_three, ht]
    have hlogpos : (0 : ℝ) ≤ Real.log (Real.sqrt (Real.pi * |t|)) := by
      apply Real.log_nonneg
      rw [Real.le_sqrt' (by norm_num only)]
      nlinarith only [hpi1]
    have h4 : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
    linarith only [hb, hlogpos, h4]

/-- On a disk of positive-real-part points, `digamma` has a primitive `g` whose real part
agrees with `log ‖Γ‖` everywhere on the disk.  This avoids the branch cut of `Complex.log`,
which is unsound to compose directly with `Γ` on a fixed-radius disk once `Γ`'s phase winds
fast enough (which happens for large imaginary part). -/
theorem exists_hasDerivAt_digamma_re_eq_log_norm_Gamma {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ w ∈ Metric.ball c r, 0 < w.re) :
    ∃ g : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt g (Complex.digamma w) w) ∧
        ∀ w ∈ Metric.ball c r, (g w).re = Real.log ‖Complex.Gamma w‖ := by
  have hGammaDiffOn : DifferentiableOn ℂ Complex.Gamma (Metric.ball c r) := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
    intro m hm
    have hwre := hball w hw
    rw [hm, Complex.neg_re, Complex.natCast_re] at hwre
    linarith only [hwre, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
  have hGammaNe : ∀ w ∈ Metric.ball c r, Complex.Gamma w ≠ 0 := fun w hw =>
    Complex.Gamma_ne_zero_of_re_pos (hball w hw)
  have hdigammaEq : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def, logDeriv_apply]
  have hdigammaDiffOn : DifferentiableOn ℂ Complex.digamma (Metric.ball c r) := by
    rw [hdigammaEq]
    exact (hGammaDiffOn.deriv Metric.isOpen_ball).div hGammaDiffOn hGammaNe
  obtain ⟨g, hgc, hg'⟩ :=
    (hdigammaDiffOn.isExactOn_ball).with_val_at c (Complex.log (Complex.Gamma c))
  set G : ℂ → ℂ := fun w => Complex.exp (g w) * (Complex.Gamma w)⁻¹ with hG_def
  have hGhasDerivAt : ∀ w ∈ Metric.ball c r, HasDerivAt G 0 w := by
    intro w hw
    have hgw := hg' w hw
    have hGammaNew := hGammaNe w hw
    have hderivGamma : deriv Complex.Gamma w = Complex.digamma w * Complex.Gamma w := by
      have hlog : Complex.digamma w = deriv Complex.Gamma w / Complex.Gamma w := by rw [hdigammaEq]
      rw [hlog, div_mul_cancel₀]
      exact hGammaNew
    have hGammaHasDeriv : HasDerivAt Complex.Gamma (Complex.digamma w * Complex.Gamma w) w := by
      rw [← hderivGamma]
      exact (hGammaDiffOn w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw) |>.hasDerivAt
    have hexpw :
      HasDerivAt (fun w => Complex.exp (g w)) (Complex.exp (g w) * Complex.digamma w) w := hgw.cexp
    have hinvw :
      HasDerivAt (fun w => (Complex.Gamma w)⁻¹)
        (-(Complex.digamma w * Complex.Gamma w) / (Complex.Gamma w) ^ 2) w :=
      hGammaHasDeriv.inv hGammaNew
    have hGw :
      HasDerivAt G
        (Complex.exp (g w) * Complex.digamma w * (Complex.Gamma w)⁻¹ +
          Complex.exp (g w) * (-(Complex.digamma w * Complex.Gamma w) / (Complex.Gamma w) ^ 2))
        w :=
      hexpw.mul hinvw
    have hzero :
      Complex.exp (g w) * Complex.digamma w * (Complex.Gamma w)⁻¹ +
          Complex.exp (g w) * (-(Complex.digamma w * Complex.Gamma w) / (Complex.Gamma w) ^ 2) =
        0 := by
      field_simp
      ring
    rw [hzero] at hGw
    exact hGw
  have hGDiffOn : DifferentiableOn ℂ G (Metric.ball c r) := fun w hw =>
    (hGhasDerivAt w hw).differentiableAt.differentiableWithinAt
  have hderiv0 : (Metric.ball c r).EqOn (deriv G) 0 := fun w hw => (hGhasDerivAt w hw).deriv
  have hcmem : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hGammaNec := hGammaNe c hcmem
  have hGc : G c = 1 := by
    change Complex.exp (g c) * (Complex.Gamma c)⁻¹ = 1
    rw [hgc, Complex.exp_log hGammaNec, mul_inv_cancel₀ hGammaNec]
  have hconst := fun w (hw : w ∈ Metric.ball c r) =>
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected hGDiffOn hderiv0
      hcmem hw
  refine ⟨g, hg', fun w hw => ?_⟩
  have hGw1 : G w = 1 := (hconst w hw).symm.trans hGc
  have hGammaNew := hGammaNe w hw
  have hexpeq : Complex.exp (g w) = Complex.Gamma w := by
    have : Complex.exp (g w) * (Complex.Gamma w)⁻¹ = 1 := hGw1
    field_simp at this
    exact this
  have hnormeq : Real.exp (g w).re = ‖Complex.Gamma w‖ := by rw [← Complex.norm_exp, hexpeq]
  have hpos : (0 : ℝ) < ‖Complex.Gamma w‖ := norm_pos_iff.mpr hGammaNew
  rw [← hnormeq, Real.log_exp]

/-- A uniform bound for `Real.Gamma` on `[1/2, 3/2]`, via convexity (the max of a convex function
on a segment is attained at an endpoint) and the exact value `Γ(1/2) = √π`. -/
theorem Real.Gamma_le_sqrt_pi_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ)) :
    Real.Gamma σ ≤ Real.sqrt Real.pi := by
  have h1 : Real.Gamma (3 / 2 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 from by norm_num only, Real.Gamma_add_one (by norm_num only),
      Real.Gamma_one_half_eq]
    nlinarith [Real.sqrt_nonneg Real.pi]
  have hseg : σ ∈ segment ℝ (1 / 2 : ℝ) (3 / 2 : ℝ) := by
    rw [segment_eq_Icc (by norm_num only : (1 / 2 : ℝ) ≤ 3 / 2)]; exact hσ
  have hconv :=
    Real.convexOn_Gamma.le_on_segment
      (show (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) by
        simp only [Set.mem_Ioi]
        norm_num only)
      (show (3 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) by
        simp only [Set.mem_Ioi]
        norm_num only)
      hseg
  rw [Real.Gamma_one_half_eq] at hconv
  exact hconv.trans (max_le (le_refl _) h1)

/-- For `r ≥ 0`, convexity bounds Gamma on `[r+1/2,r+3/2]` by the maximum
of its endpoint values. At `r=0` these are `√π` and `√π/2`, respectively. -/
theorem Real.Gamma_le_max_of_mem_Icc {r σ : ℝ} (hr : 0 ≤ r)
    (hσ : σ ∈ Set.Icc (r + 1 / 2) (r + 3 / 2)) :
    Real.Gamma σ ≤ max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) := by
  have hseg : σ ∈ segment ℝ (r + 1 / 2) (r + 3 / 2) := by
    rw [segment_eq_Icc (by linarith only [hr] : r + 1 / 2 ≤ r + 3 / 2)]
    exact hσ
  exact
    Real.convexOn_Gamma.le_on_segment
      (Set.mem_Ioi.mpr (show (0 : ℝ) < r + 1 / 2 by linarith only [hr]))
      (Set.mem_Ioi.mpr (show (0 : ℝ) < r + 3 / 2 by linarith only [hr])) hseg

/-- The fully general form of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.Real.Gamma_le_max_of_mem_Icc`:
on *any* interval `[a, b] ⊆ (0, ∞)`,
`Γ`'s maximum is attained at an endpoint (convexity). Needed to bound `Γ` uniformly as the real
part of the evaluation point ranges over an interval (the zeta-side estimate's horizontal-edge
bound), not just over the fixed-width `[r+1/2, r+3/2]` shape. -/
theorem Real.Gamma_le_max_of_mem_Icc' {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) : Real.Gamma x ≤ max (Real.Gamma a) (Real.Gamma b) := by
  have hseg : x ∈ segment ℝ a b := by
    rw [segment_eq_Icc hab]; exact hx
  exact
    Real.convexOn_Gamma.le_on_segment (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr (lt_of_lt_of_le ha hab))
      hseg

/-- **The horizontal-edge `Γ`-lower-bound gap, closed.** For any real `a ≥ 1` and `f` with
`|f| ≤ 1/2`, `-log‖Γ(a+f+it)‖` is controlled by `-log‖Γ(a+it)‖` plus an explicit correction, via
Borel-Carathéodory applied to a primitive of `digamma` on a disk of radius `3/4` around `a+it`,
stopping at the bound on the primitive's *variation* rather than continuing to the Cauchy estimate
for its derivative (which is all
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_digamma_one_add_mul_I_le` needed).
Combined with `Γ(n+it) = Γ(1+it) * ∏_{k=1}^{n-1}(k+it)` (so `‖Γ(n+it)‖ ≥ ‖Γ(1+it)‖` for `n : ℕ`,
`n ≥ 1`, via `PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_Gamma_le_Gamma_add_nat`),
applying this at `a := n` for the nearest integer `n` to `1+r`
covers *every* real part `1 + r` (`r ≥ 0`), not just `r ∈ [0, 1/2]` from a single center. -/
theorem neg_log_norm_Gamma_add_add_mul_I_le_of_abs_le_half {a : ℝ} (ha : 1 ≤ a) {f t : ℝ}
    (hf : |f| ≤ 1 / 2) :
    -Real.log ‖Complex.Gamma ((a : ℂ) + (f : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      -Real.log ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ +
        4 *
          (Real.log (max (Real.Gamma (a - 3 / 4)) (Real.Gamma (a + 3 / 4)) + 1) -
            Real.log ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
  set c : ℂ := (a : ℂ) + (t : ℂ) * Complex.I with hc_def
  have hcre : c.re = a := by
    simp only [hc_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hre_bound : ∀ w : ℂ, w ∈ Metric.ball c (3 / 4 : ℝ) → |w.re - a| < 3 / 4 := by
    intro w hw
    have hd : ‖w - c‖ < 3 / 4 := by simpa only [Metric.mem_ball, Complex.dist_eq] using hw
    have hle := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re, hcre] at hle
    linarith only [hd, hle]
  have hball : ∀ w ∈ Metric.ball c (3 / 4 : ℝ), 0 < w.re := by
    intro w hw
    have := (abs_lt.mp (hre_bound w hw)).1
    linarith only [this, ha]
  obtain ⟨g, hg', hgRe⟩ :=
    exists_hasDerivAt_digamma_re_eq_log_norm_Gamma (by norm_num only : (0 : ℝ) < 3 / 4) hball
  set Gbound : ℝ := max (Real.Gamma (a - 3 / 4)) (Real.Gamma (a + 3 / 4)) + 1 with hGbound_def
  have hRe_le : ∀ w ∈ Metric.ball c (3 / 4 : ℝ), (g w).re ≤ Real.log Gbound := by
    intro w hw
    have hwre_mem : w.re ∈ Set.Icc (a - 3 / 4 : ℝ) (a + 3 / 4 : ℝ) := by
      have := abs_lt.mp (hre_bound w hw)
      constructor <;> linarith only [this.1, this.2]
    have hwre_pos : 0 < w.re := by linarith only [hwre_mem.1, ha]
    rw [hgRe w hw]
    have h1 : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := norm_Gamma_le_Gamma_re hwre_pos
    have h2 : Real.Gamma w.re ≤ max (Real.Gamma (a - 3 / 4)) (Real.Gamma (a + 3 / 4)) :=
      Real.Gamma_le_max_of_mem_Icc' (by linarith only [ha]) (by linarith only []) hwre_mem
    apply Real.log_le_log (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hwre_pos))
    calc
      ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := h1
      _ ≤ max (Real.Gamma (a - 3 / 4)) (Real.Gamma (a + 3 / 4)) := h2
      _ ≤ Gbound := by
        rw [hGbound_def]; linarith only []
  have hccenter : c ∈ Metric.ball c (3 / 4 : ℝ) := Metric.mem_ball_self (by norm_num only)
  set M : ℝ := Real.log Gbound - (g c).re with hM_def
  have hMpos : 0 < M := by
    have hle := hRe_le c hccenter
    rw [hgRe c hccenter] at hle
    have hGammaCne : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (hball c hccenter)
    have hGammaC_le : ‖Complex.Gamma c‖ ≤ Real.Gamma c.re :=
      norm_Gamma_le_Gamma_re (hball c hccenter)
    rw [hcre] at hGammaC_le
    have hGammaC_le_max : Real.Gamma a ≤ max (Real.Gamma (a - 3 / 4)) (Real.Gamma (a + 3 / 4)) :=
      Real.Gamma_le_max_of_mem_Icc' (by linarith only [ha]) (by linarith only [])
        (by constructor <;> linarith only [])
    have hlt : Real.log ‖Complex.Gamma c‖ < Real.log Gbound := by
      apply Real.log_lt_log (norm_pos_iff.mpr hGammaCne)
      calc
        ‖Complex.Gamma c‖ ≤ Real.Gamma a := hGammaC_le
        _ ≤ max (Real.Gamma (a - 3 / 4)) (Real.Gamma (a + 3 / 4)) := hGammaC_le_max
        _ < Gbound := by
          rw [hGbound_def]; linarith only []
    rw [hgRe c hccenter] at hM_def
    linarith only [hlt, hM_def]
  set h : ℂ → ℂ := fun z => g (c + z) - g c with hh_def
  have hgc_shift_diffOn : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) (3 / 4 : ℝ)) := by
    intro z hz
    have hcz_mem : c + z ∈ Metric.ball c (3 / 4 : ℝ) := by
      simpa only [Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz
    have : DifferentiableAt ℂ (fun z => g (c + z)) z :=
      ((hg' (c + z) hcz_mem).differentiableAt).comp z (((differentiableAt_id).const_add c))
    exact (this.sub_const (g c)).differentiableWithinAt
  have hh0 : h 0 = 0 := by simp only [hh_def, add_zero, sub_self]
  have hh_bound : ∀ z ∈ Metric.ball (0 : ℂ) (3 / 4 : ℝ), (h z).re ≤ M := by
    intro z hz
    have hcz_mem : c + z ∈ Metric.ball c (3 / 4 : ℝ) := by
      simpa only [Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz
    have := hRe_le (c + z) hcz_mem
    simp only [hh_def, Complex.sub_re]
    linarith only [this, hM_def]
  have hz_eq : ‖(f : ℂ)‖ = |f| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hz_lt : ‖(f : ℂ)‖ < (3 / 4 : ℝ) := by
    rw [hz_eq]; linarith only [hf]
  have hz_mem : (f : ℂ) ∈ Metric.ball (0 : ℂ) (3 / 4 : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hz_lt
  have hBC :=
    Complex.borelCaratheodory_zero hMpos hgc_shift_diffOn (fun w hw => hh_bound w hw)
      (by norm_num only) hz_mem hh0
  rw [hz_eq] at hBC
  have hfle : |f| / (3 / 4 - |f|) ≤ 2 := by
    rw [div_le_iff₀ (by linarith only [hf])]
    linarith only [hf]
  have hBC' : ‖h (f : ℂ)‖ ≤ 4 * M := by
    calc
      ‖h (f : ℂ)‖ ≤ 2 * M * |f| / (3 / 4 - |f|) := hBC
      _ = 2 * M * (|f| / (3 / 4 - |f|)) := by ring
      _ ≤ 2 * M * 2 := mul_le_mul_of_nonneg_left hfle (by positivity)
      _ = 4 * M := by ring
  have hcf_mem : c + (f : ℂ) ∈ Metric.ball c (3 / 4 : ℝ) := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs] using hz_lt
  have hre_diff :
    (h (f : ℂ)).re = Real.log ‖Complex.Gamma (c + (f : ℂ))‖ - Real.log ‖Complex.Gamma c‖ := by
    rw [hh_def]
    simp only [Complex.sub_re]
    rw [hgRe (c + (f : ℂ)) hcf_mem, hgRe c hccenter]
  have hre_abs_le : |(h (f : ℂ)).re| ≤ 4 * M := (Complex.abs_re_le_norm _).trans hBC'
  have hre_ge : -(4 * M) ≤ (h (f : ℂ)).re := (abs_le.mp hre_abs_le).1
  rw [hre_diff] at hre_ge
  have hMeq : M = Real.log Gbound - Real.log ‖Complex.Gamma c‖ := by rw [hM_def, hgRe c hccenter]
  rw [show c + (f : ℂ) = (a : ℂ) + (f : ℂ) + (t : ℂ) * Complex.I from by
      rw [hc_def]; ring] at hre_ge
  rw [hMeq, hGbound_def] at hre_ge
  linarith only [hre_ge]

/-- **Full `f ∈ [0, 1)` case**, combining `PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`neg_log_norm_Gamma_add_add_mul_I_le_of_abs_le_half`
applied at the two centers `a = 1` (covering `f ∈ [0, 1/2]`) and `a = 2` (covering `f ∈ (1/2, 1)`,
via the exact identity `Γ(2+it) = (1+it)·Γ(1+it)`, hence `‖Γ(2+it)‖ ≥ ‖Γ(1+it)‖`) into a single
bound, entirely in terms of `-log‖Γ(1+it)‖`. -/
theorem neg_log_norm_Gamma_one_add_add_mul_I_le_of_lt_one {f t : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) :
    -Real.log ‖Complex.Gamma (1 + (f : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      5 * (-Real.log ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖) +
        4 *
          Real.log
            (max (max (Real.Gamma (1 / 4)) (Real.Gamma (7 / 4)))
                (max (Real.Gamma (5 / 4)) (Real.Gamma (11 / 4))) +
              1) := by
  set GboundFull : ℝ :=
    max (max (Real.Gamma (1 / 4)) (Real.Gamma (7 / 4)))
        (max (Real.Gamma (5 / 4)) (Real.Gamma (11 / 4))) +
      1 with
    hGboundFull_def
  have hGboundFull_pos : 0 < GboundFull := by positivity
  have hle1 : max (Real.Gamma (1 / 4)) (Real.Gamma (7 / 4)) + 1 ≤ GboundFull := by
    have :=
      le_max_left (max (Real.Gamma (1 / 4)) (Real.Gamma (7 / 4)))
        (max (Real.Gamma (5 / 4)) (Real.Gamma (11 / 4)))
    rw [hGboundFull_def]; linarith only [this]
  have hle2 : max (Real.Gamma (5 / 4)) (Real.Gamma (11 / 4)) + 1 ≤ GboundFull := by
    have :=
      le_max_right (max (Real.Gamma (1 / 4)) (Real.Gamma (7 / 4)))
        (max (Real.Gamma (5 / 4)) (Real.Gamma (11 / 4)))
    rw [hGboundFull_def]; linarith only [this]
  by_cases hf : f ≤ 1 / 2
  · have hbound :=
      neg_log_norm_Gamma_add_add_mul_I_le_of_abs_le_half (a := 1) (le_refl 1) (f := f) (t := t)
        (by
          rw [abs_of_nonneg hf0]; exact hf)
    push_cast at hbound
    norm_num only at hbound
    have hlog_le :
      Real.log (max (Real.Gamma (1 / 4)) (Real.Gamma (7 / 4)) + 1) ≤ Real.log GboundFull :=
      Real.log_le_log (by positivity) hle1
    linarith only [hbound, hlog_le]
  · push Not at hf
    set f' : ℝ := f - 1 with hf'_def
    have hf'abs : |f'| ≤ 1 / 2 := by
      rw [abs_of_nonpos (by linarith only [hf1, hf'_def]), hf'_def]; linarith only [hf]
    have hbound :=
      neg_log_norm_Gamma_add_add_mul_I_le_of_abs_le_half (a := 2) (by norm_num only) (f := f') (t :=
        t) hf'abs
    push_cast at hbound
    norm_num only at hbound
    have heq : (2 : ℂ) + (f' : ℂ) + (t : ℂ) * Complex.I = 1 + (f : ℂ) + (t : ℂ) * Complex.I := by
      have : (f' : ℂ) = (f : ℂ) - 1 := by
        rw [hf'_def]; push_cast; ring
      rw [this]; ring
    rw [heq] at hbound
    have hlog_le2 :
      Real.log (max (Real.Gamma (5 / 4)) (Real.Gamma (11 / 4)) + 1) ≤ Real.log GboundFull :=
      Real.log_le_log (by positivity) hle2
    have hone_ne : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re,
        one_ne_zero] at this
    have hgamma_eq :
      Complex.Gamma (1 + (t : ℂ) * Complex.I + 1) =
        (1 + (t : ℂ) * Complex.I) * Complex.Gamma (1 + (t : ℂ) * Complex.I) :=
      Complex.Gamma_add_one _ hone_ne
    have hshift : (1 : ℂ) + (t : ℂ) * Complex.I + 1 = 2 + (t : ℂ) * Complex.I := by ring
    rw [hshift] at hgamma_eq
    have hnorm_one_it : (1 : ℝ) ≤ ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ := by
      have hre : ((1 : ℂ) + (t : ℂ) * Complex.I).re = 1 := by
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      have := Complex.abs_re_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I)
      rw [hre] at this
      simpa only [ge_iff_le, abs_one] using this
    have hnorm_ge :
      ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ≤ ‖Complex.Gamma (2 + (t : ℂ) * Complex.I)‖ := by
      rw [hgamma_eq, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hnorm_one_it
    have hGamma1_ne : Complex.Gamma (1 + (t : ℂ) * Complex.I) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos
        (by
          simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
            zero_lt_one])
    have hneg_log_ge :
      -Real.log ‖Complex.Gamma (2 + (t : ℂ) * Complex.I)‖ ≤
        -Real.log ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ := by
      have := Real.log_le_log (norm_pos_iff.mpr hGamma1_ne) hnorm_ge
      linarith only [this]
    linarith only [hbound, hlog_le2, hneg_log_ge]

/-- For nonnegative `r`, split `r` into its natural and fractional parts.
Gamma recurrence transfers the lower norm bound on fractional shifts to `1+r+it`,
with a bound independent of `r`. -/
theorem neg_log_norm_Gamma_one_add_add_mul_I_le_of_nonneg {r t : ℝ} (hr : 0 ≤ r) :
    -Real.log ‖Complex.Gamma (1 + (r : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      5 * (-Real.log ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖) +
        4 *
          Real.log
            (max (max (Real.Gamma (1 / 4)) (Real.Gamma (7 / 4)))
                (max (Real.Gamma (5 / 4)) (Real.Gamma (11 / 4))) +
              1) := by
  set n : ℕ := ⌊r⌋₊ with hn_def
  set f : ℝ := r - n with hf_def
  have hn_le : (n : ℝ) ≤ r := Nat.floor_le hr
  have hn_lt : r < n + 1 := Nat.lt_floor_add_one r
  have hf0 : 0 ≤ f := by
    rw [hf_def]; linarith
  have hf1 : f < 1 := by
    rw [hf_def]; linarith
  have hfn : f + n = r := by
    rw [hf_def]; ring
  have hzre : (1 : ℝ) ≤ (1 + (f : ℂ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    linarith
  have hstep := norm_Gamma_le_Gamma_add_nat hzre n
  have heq :
    (1 : ℂ) + (f : ℂ) + (t : ℂ) * Complex.I + (n : ℕ) = 1 + (r : ℂ) + (t : ℂ) * Complex.I := by
    have : ((n : ℕ) : ℂ) = (n : ℝ) := by
      push_cast; ring
    rw [this,
      show ((r : ℝ) : ℂ) = ((f : ℝ) : ℂ) + ((n : ℝ) : ℂ) from by
        rw [← hfn]; push_cast; ring]
    ring
  rw [heq] at hstep
  have hGammaf_ne : Complex.Gamma (1 + (f : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by linarith [hzre])
  have hneg_log_ge :
    -Real.log ‖Complex.Gamma (1 + (r : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      -Real.log ‖Complex.Gamma (1 + (f : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have := Real.log_le_log (norm_pos_iff.mpr hGammaf_ne) hstep
    linarith
  linarith [hneg_log_ge, neg_log_norm_Gamma_one_add_add_mul_I_le_of_lt_one (t := t) hf0 hf1]

/-- There are constants giving an affine-in-`|t|` upper bound for
`-log ‖Γ(1+r+it)‖`, simultaneously for all `r ≥ 0` and real `t`. -/
theorem exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform :
    ∃ C₁ : ℝ,
      ∀ r t : ℝ,
        0 ≤ r →
          -Real.log ‖Complex.Gamma (1 + (r : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C₁ + 5 * Real.pi * |t| / 2 := by
  obtain ⟨C₀, hC₀⟩ := exists_neg_log_norm_Gamma_one_add_mul_I_le_uniform
  refine
    ⟨5 * C₀ +
        4 *
          Real.log
            (max (max (Real.Gamma (1 / 4)) (Real.Gamma (7 / 4)))
                (max (Real.Gamma (5 / 4)) (Real.Gamma (11 / 4))) +
              1),
      fun r t hr => ?_⟩
  have h1 := neg_log_norm_Gamma_one_add_add_mul_I_le_of_nonneg (r := r) (t := t) hr
  have h2 := hC₀ t
  linarith only [h1, h2]

/-- The mirror of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_digamma_one_add_mul_I_le`,
generalized from `Re s = 1` to any
`Re s = 1 + r` with `r ≥ 0` real (not necessarily an integer). The bound uses
`max(Γ(r+1/2), Γ(r+3/2)) + 1` (a harmless `+1` slack) in place of `√π`, so that the center
strict-inequality step doesn't need strict convexity of `Γ`.
Needed for the zeta-side estimate's horizontal-edge
bound, whose real part ranges continuously over an interval. -/
theorem norm_digamma_shift_add_mul_I_le (r : ℝ) (hr : 0 ≤ r) (t : ℝ) :
    ‖Complex.digamma ((1 + r : ℝ) + (t : ℂ) * Complex.I)‖ ≤
      8 *
        (Real.log (max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1) -
          Real.log ‖Complex.Gamma ((1 + r : ℝ) + (t : ℂ) * Complex.I)‖) := by
  set c : ℂ := (1 + r : ℝ) + (t : ℂ) * Complex.I with hc_def
  have hcre : c.re = 1 + r := by
    simp only [hc_def, Complex.ofReal_add, Complex.ofReal_one, Complex.add_re, Complex.one_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_self, add_zero]
  have hre_bound : ∀ w : ℂ, w ∈ Metric.ball c (1 / 2 : ℝ) → |w.re - (1 + r)| < 1 / 2 := by
    intro w hw
    have hd : ‖w - c‖ < 1 / 2 := by simpa only [Metric.mem_ball, Complex.dist_eq] using hw
    have hle := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re, hcre] at hle
    linarith
  have hball : ∀ w ∈ Metric.ball c (1 / 2 : ℝ), 0 < w.re := by
    intro w hw
    have := (abs_lt.mp (hre_bound w hw)).1
    linarith
  obtain ⟨g, hg', hgRe⟩ :=
    exists_hasDerivAt_digamma_re_eq_log_norm_Gamma (by norm_num only : (0 : ℝ) < 1 / 2) hball
  set Gbound : ℝ := max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1 with hGbound_def
  have hRe_le : ∀ w ∈ Metric.ball c (1 / 2 : ℝ), (g w).re ≤ Real.log Gbound := by
    intro w hw
    have hwre_mem : w.re ∈ Set.Icc (r + 1 / 2 : ℝ) (r + 3 / 2) := by
      have := abs_lt.mp (hre_bound w hw)
      constructor <;> linarith [this.1, this.2]
    have hwre_pos : 0 < w.re := by linarith [hwre_mem.1]
    rw [hgRe w hw]
    have h1 : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := norm_Gamma_le_Gamma_re hwre_pos
    have h2 : Real.Gamma w.re ≤ max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) :=
      Real.Gamma_le_max_of_mem_Icc hr hwre_mem
    apply Real.log_le_log (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hwre_pos))
    calc
      ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := h1
      _ ≤ max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) := h2
      _ ≤ Gbound := by
        rw [hGbound_def]; linarith
  have hccenter : c ∈ Metric.ball c (1 / 2 : ℝ) := Metric.mem_ball_self (by norm_num only)
  set M : ℝ := Real.log Gbound - (g c).re with hM_def
  have hMpos : 0 < M := by
    have hle := hRe_le c hccenter
    rw [hgRe c hccenter] at hle
    have hGammaCne : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (hball c hccenter)
    have hGammaC_le : ‖Complex.Gamma c‖ ≤ Real.Gamma c.re :=
      norm_Gamma_le_Gamma_re (hball c hccenter)
    rw [hcre] at hGammaC_le
    have hGammaC_le_max :
      Real.Gamma (1 + r) ≤ max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) := by
      apply Real.Gamma_le_max_of_mem_Icc hr
      constructor <;> linarith
    have hlt : Real.log ‖Complex.Gamma c‖ < Real.log Gbound := by
      apply Real.log_lt_log (norm_pos_iff.mpr hGammaCne)
      calc
        ‖Complex.Gamma c‖ ≤ Real.Gamma (1 + r) := hGammaC_le
        _ ≤ max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) := hGammaC_le_max
        _ < Gbound := by
          rw [hGbound_def]; linarith
    rw [hgRe c hccenter] at hM_def
    linarith [hlt]
  set h : ℂ → ℂ := fun z => g (c + z) - g c with hh_def
  have hgc_shift_diffOn : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) (1 / 2 : ℝ)) := by
    intro z hz
    have hcz_mem : c + z ∈ Metric.ball c (1 / 2 : ℝ) := by
      simpa only [one_div, Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz
    have : DifferentiableAt ℂ (fun z => g (c + z)) z :=
      ((hg' (c + z) hcz_mem).differentiableAt).comp z (((differentiableAt_id).const_add c))
    exact (this.sub_const (g c)).differentiableWithinAt
  have hh0 : h 0 = 0 := by simp only [hh_def, add_zero, sub_self]
  have hh_bound : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2 : ℝ), (h z).re ≤ M := by
    intro z hz
    have hcz_mem : c + z ∈ Metric.ball c (1 / 2 : ℝ) := by
      simpa only [one_div, Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz
    have := hRe_le (c + z) hcz_mem
    simp only [hh_def, Complex.sub_re]
    linarith [hM_def]
  have hBC : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2 : ℝ), ‖h z‖ ≤ 2 * M * ‖z‖ / ((1 / 2 : ℝ) - ‖z‖) := by
    intro z hz
    exact
      Complex.borelCaratheodory_zero hMpos hgc_shift_diffOn (fun w hw => hh_bound w hw)
        (by norm_num only) hz hh0
  set f : ℂ → ℂ := fun w => g w - g c with hf_def
  have hfh : ∀ w : ℂ, f w = h (w - c) := by
    intro w
    simp only [hf_def, hh_def, add_sub_cancel]
  have hf_diffOn : DifferentiableOn ℂ f (Metric.ball c (1 / 4 : ℝ)) := by
    intro w hw
    have hw' : w ∈ Metric.ball c (1 / 2 : ℝ) := by
      have := Metric.mem_ball.mp hw
      exact Metric.mem_ball.mpr (by linarith)
    exact ((hg' w hw').differentiableAt.sub_const (g c)).differentiableWithinAt
  have hf_diffContOnCl : DiffContOnCl ℂ f (Metric.ball c (1 / 4 : ℝ)) := by
    constructor
    · exact hf_diffOn
    · have hDiffCl : DifferentiableOn ℂ f (closure (Metric.ball c (1 / 4 : ℝ))) := by
        intro w hw
        have hw' : w ∈ Metric.ball c (1 / 2 : ℝ) := by
          have hw2 := Metric.closure_ball_subset_closedBall hw
          have := Metric.mem_closedBall.mp hw2
          exact Metric.mem_ball.mpr (by linarith)
        exact ((hg' w hw').differentiableAt.sub_const (g c)).differentiableWithinAt
      exact hDiffCl.continuousOn
  have hsphere_bound : ∀ w ∈ Metric.sphere c (1 / 4 : ℝ), ‖f w‖ ≤ 2 * M := by
    intro w hw
    have hw_norm : ‖w - c‖ = 1 / 4 := by
      have := Metric.mem_sphere.mp hw
      rwa [Complex.dist_eq] at this
    have hw_mem : w - c ∈ Metric.ball (0 : ℂ) (1 / 2 : ℝ) := by
      rw [Metric.mem_ball, dist_zero_right, hw_norm]; norm_num only
    have := hBC (w - c) hw_mem
    rw [hw_norm] at this
    rw [hfh w]
    calc
      ‖h (w - c)‖ ≤ 2 * M * (1 / 4 : ℝ) / ((1 / 2 : ℝ) - (1 / 4 : ℝ)) := this
      _ = 2 * M := by ring
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) (c := c) (R := (1 / 4 : ℝ))
      (C := 2 * M) 1 (by norm_num only) hf_diffContOnCl hsphere_bound
  simp only [iteratedDeriv_one] at hcauchy
  have hderivf : deriv f c = Complex.digamma c := by
    have hderivg : deriv g c = Complex.digamma c := (hg' c hccenter).deriv
    have : deriv f c = deriv g c := by
      simp only [hf_def]
      rw [deriv_sub_const]
    rw [this, hderivg]
  rw [hderivf] at hcauchy
  have hfactorial : (Nat.factorial 1 : ℝ) * (2 * M) / (1 / 4 : ℝ) ^ 1 = 8 * M := by
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
    ring
  rw [hfactorial] at hcauchy
  have hMeq : M = Real.log Gbound - Real.log ‖Complex.Gamma c‖ := by rw [hM_def, hgRe c hccenter]
  rw [hMeq] at hcauchy
  exact hcauchy

/-- The crude `O(t)` growth bound for `digamma` on the line `Re s = 1`, via a primitive of
`digamma` matching `log ‖Γ‖` in real part, the elementary bound on `Γ` on a strip, and
Borel-Carathéodory combined with the Cauchy estimate for derivatives. -/
theorem norm_digamma_one_add_mul_I_le (t : ℝ) :
    ‖Complex.digamma (1 + (t : ℂ) * Complex.I)‖ ≤
      8 * (Real.log (Real.sqrt Real.pi) - Real.log ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖) := by
  set c : ℂ := 1 + (t : ℂ) * Complex.I with hc_def
  have hcre : c.re = 1 := by
    simp only [hc_def, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hre_bound : ∀ w : ℂ, w ∈ Metric.ball c (1 / 2 : ℝ) → |w.re - 1| < 1 / 2 := by
    intro w hw
    have hd : ‖w - c‖ < 1 / 2 := by simpa only [Metric.mem_ball, Complex.dist_eq] using hw
    have hle := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re, hcre] at hle
    linarith
  have hball : ∀ w ∈ Metric.ball c (1 / 2 : ℝ), 0 < w.re := by
    intro w hw
    have := (abs_lt.mp (hre_bound w hw)).1
    linarith
  obtain ⟨g, hg', hgRe⟩ :=
    exists_hasDerivAt_digamma_re_eq_log_norm_Gamma (by norm_num only : (0 : ℝ) < 1 / 2) hball
  have hRe_le : ∀ w ∈ Metric.ball c (1 / 2 : ℝ), (g w).re ≤ Real.log (Real.sqrt Real.pi) := by
    intro w hw
    have hwre_mem : w.re ∈ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ) := by
      have := abs_lt.mp (hre_bound w hw)
      constructor <;> linarith [this.1, this.2]
    have hwre_pos : 0 < w.re := by linarith [hwre_mem.1]
    rw [hgRe w hw]
    have h1 : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := norm_Gamma_le_Gamma_re hwre_pos
    have h2 : Real.Gamma w.re ≤ Real.sqrt Real.pi := Real.Gamma_le_sqrt_pi_of_mem_Icc hwre_mem
    exact
      Real.log_le_log (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hwre_pos)) (h1.trans h2)
  have hccenter : c ∈ Metric.ball c (1 / 2 : ℝ) := Metric.mem_ball_self (by norm_num only)
  set M : ℝ := Real.log (Real.sqrt Real.pi) - (g c).re with hM_def
  have hMpos : 0 < M := by
    have := hRe_le c hccenter
    rw [hgRe c hccenter] at this
    have hGammaCne : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (hball c hccenter)
    have hGammaC_le : ‖Complex.Gamma c‖ ≤ Real.Gamma c.re :=
      norm_Gamma_le_Gamma_re (hball c hccenter)
    rw [hcre, Real.Gamma_one] at hGammaC_le
    have hlt : Real.log ‖Complex.Gamma c‖ < Real.log (Real.sqrt Real.pi) := by
      apply Real.log_lt_log (norm_pos_iff.mpr hGammaCne)
      calc
        ‖Complex.Gamma c‖ ≤ 1 := hGammaC_le
        _ < Real.sqrt Real.pi := by
          rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
          exact Real.sqrt_lt_sqrt (by norm_num only) (by linarith [Real.pi_gt_three])
    rw [hgRe c hccenter] at hM_def
    linarith [hlt]
  set h : ℂ → ℂ := fun z => g (c + z) - g c with hh_def
  have hgc_shift_diffOn : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) (1 / 2 : ℝ)) := by
    intro z hz
    have hcz_mem : c + z ∈ Metric.ball c (1 / 2 : ℝ) := by
      simpa only [one_div, Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz
    have : DifferentiableAt ℂ (fun z => g (c + z)) z :=
      ((hg' (c + z) hcz_mem).differentiableAt).comp z (((differentiableAt_id).const_add c))
    exact (this.sub_const (g c)).differentiableWithinAt
  have hh0 : h 0 = 0 := by simp only [hh_def, add_zero, sub_self]
  have hh_bound : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2 : ℝ), (h z).re ≤ M := by
    intro z hz
    have hcz_mem : c + z ∈ Metric.ball c (1 / 2 : ℝ) := by
      simpa only [one_div, Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz
    have := hRe_le (c + z) hcz_mem
    simp only [hh_def, Complex.sub_re]
    linarith [hM_def]
  have hBC : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2 : ℝ), ‖h z‖ ≤ 2 * M * ‖z‖ / ((1 / 2 : ℝ) - ‖z‖) := by
    intro z hz
    exact
      Complex.borelCaratheodory_zero hMpos hgc_shift_diffOn (fun w hw => hh_bound w hw)
        (by norm_num only) hz hh0
  set f : ℂ → ℂ := fun w => g w - g c with hf_def
  have hfh : ∀ w : ℂ, f w = h (w - c) := by
    intro w
    simp only [hf_def, hh_def, add_sub_cancel]
  have hf_diffOn : DifferentiableOn ℂ f (Metric.ball c (1 / 4 : ℝ)) := by
    intro w hw
    have hw' : w ∈ Metric.ball c (1 / 2 : ℝ) := by
      have := Metric.mem_ball.mp hw
      exact Metric.mem_ball.mpr (by linarith)
    exact ((hg' w hw').differentiableAt.sub_const (g c)).differentiableWithinAt
  have hf_diffContOnCl : DiffContOnCl ℂ f (Metric.ball c (1 / 4 : ℝ)) := by
    constructor
    · exact hf_diffOn
    · have hDiffCl : DifferentiableOn ℂ f (closure (Metric.ball c (1 / 4 : ℝ))) := by
        intro w hw
        have hw' : w ∈ Metric.ball c (1 / 2 : ℝ) := by
          have hw2 := Metric.closure_ball_subset_closedBall hw
          have := Metric.mem_closedBall.mp hw2
          exact Metric.mem_ball.mpr (by linarith)
        exact ((hg' w hw').differentiableAt.sub_const (g c)).differentiableWithinAt
      exact hDiffCl.continuousOn
  have hsphere_bound : ∀ w ∈ Metric.sphere c (1 / 4 : ℝ), ‖f w‖ ≤ 2 * M := by
    intro w hw
    have hw_norm : ‖w - c‖ = 1 / 4 := by
      have := Metric.mem_sphere.mp hw
      rwa [Complex.dist_eq] at this
    have hw_mem : w - c ∈ Metric.ball (0 : ℂ) (1 / 2 : ℝ) := by
      rw [Metric.mem_ball, dist_zero_right, hw_norm]; norm_num only
    have := hBC (w - c) hw_mem
    rw [hw_norm] at this
    rw [hfh w]
    calc
      ‖h (w - c)‖ ≤ 2 * M * (1 / 4 : ℝ) / ((1 / 2 : ℝ) - (1 / 4 : ℝ)) := this
      _ = 2 * M := by ring
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) (c := c) (R := (1 / 4 : ℝ))
      (C := 2 * M) 1 (by norm_num only) hf_diffContOnCl hsphere_bound
  simp only [iteratedDeriv_one] at hcauchy
  have hderivf : deriv f c = Complex.digamma c := by
    have hderivg : deriv g c = Complex.digamma c := (hg' c hccenter).deriv
    have : deriv f c = deriv g c := by
      simp only [hf_def]
      rw [deriv_sub_const]
    rw [this, hderivg]
  rw [hderivf] at hcauchy
  have hfactorial : (Nat.factorial 1 : ℝ) * (2 * M) / (1 / 4 : ℝ) ^ 1 = 8 * M := by
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
    ring
  rw [hfactorial] at hcauchy
  have hMeq : M = Real.log (Real.sqrt Real.pi) - Real.log ‖Complex.Gamma c‖ := by
    rw [hM_def, hgRe c hccenter]
  rw [hMeq] at hcauchy
  exact hcauchy

/-- Propagating the `Re s = 1` digamma bound to `Re s = 1 + n` via the recurrence
`digamma (s + 1) = digamma s + s⁻¹`: each of the `n` steps contributes at most `1` in norm,
since the shifted point has real part `≥ 1`. -/
theorem norm_digamma_one_sub_mul_I_add_nat_sub_le (t : ℝ) (n : ℕ) :
    ‖Complex.digamma ((1 - (t : ℂ) * Complex.I) + n) - Complex.digamma (1 - (t : ℂ) * Complex.I)‖ ≤
      n := by
  induction n with
  | zero => simp only [CharP.cast_eq_zero, add_zero, sub_self, norm_zero, Std.le_refl]
  | succ n ih =>
    set base : ℂ := 1 - (t : ℂ) * Complex.I with hbase_def
    have hbase_re : base.re = 1 := by
      simp only [hbase_def, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]
    have hshift_re : (base + n).re = 1 + n := by rw [Complex.add_re, hbase_re, Complex.natCast_re]
    have hshift_ne : ∀ m : ℕ, base + (n : ℂ) ≠ -m := by
      intro m hm
      have hre := congrArg Complex.re hm
      rw [hshift_re, Complex.neg_re, Complex.natCast_re] at hre
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ)), (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hrec := Complex.digamma_apply_add_one (base + n) hshift_ne
    have heq : base + ((n : ℕ) + 1 : ℕ) = (base + n) + 1 := by
      push_cast; ring
    rw [heq, hrec]
    have hinv_le : ‖(base + (n : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      have hge : (1 : ℝ) ≤ ‖base + (n : ℂ)‖ := by
        calc
          (1 : ℝ) ≤ 1 + n := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
          _ = (base + (n : ℂ)).re := hshift_re.symm
          _ ≤ ‖base + (n : ℂ)‖ := Complex.re_le_norm _
      rw [inv_le_one_iff₀]
      exact Or.inr hge
    calc
      ‖Complex.digamma (base + n) + (base + (n : ℂ))⁻¹ - Complex.digamma base‖ ≤
          ‖Complex.digamma (base + n) - Complex.digamma base‖ + ‖(base + (n : ℂ))⁻¹‖ :=
        by
        have := norm_add_le (Complex.digamma (base + n) - Complex.digamma base) ((base + (n : ℂ))⁻¹)
        calc
          ‖Complex.digamma (base + n) + (base + (n : ℂ))⁻¹ - Complex.digamma base‖ =
              ‖(Complex.digamma (base + n) - Complex.digamma base) + (base + (n : ℂ))⁻¹‖ :=
            by ring_nf
          _ ≤ _ := this
      _ ≤ (n : ℝ) + 1 := by linarith [ih, hinv_le]
      _ = ((n : ℕ) + 1 : ℕ) := by
        push_cast; ring

/-- The `O(t)` digamma growth bound, propagated from `Re s = 1` to any fixed even positive
integer real part `2m+2`, as needed for the functional-equation composition (`s = 1 - z` with
`z = -(2m+1) + it`). -/
theorem norm_digamma_two_mul_add_two_sub_mul_I_le (m : ℕ) (t : ℝ) :
    ‖Complex.digamma ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I)‖ ≤
      8 * (Real.log (Real.sqrt Real.pi) - Real.log ‖Complex.Gamma (1 - (t : ℂ) * Complex.I)‖) +
        (2 * m + 1) := by
  have hbase :
    (1 - (t : ℂ) * Complex.I) + ((2 * m + 1 : ℕ) : ℂ) = (2 * m + 2 : ℂ) - (t : ℂ) * Complex.I := by
    push_cast; ring
  have hprop := norm_digamma_one_sub_mul_I_add_nat_sub_le t (2 * m + 1)
  rw [hbase] at hprop
  have hone :
    ‖Complex.digamma (1 - (t : ℂ) * Complex.I)‖ ≤
      8 * (Real.log (Real.sqrt Real.pi) - Real.log ‖Complex.Gamma (1 - (t : ℂ) * Complex.I)‖) := by
    have hlem := norm_digamma_one_add_mul_I_le (-t)
    rw [show (1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = 1 - (t : ℂ) * Complex.I from by
        push_cast; ring] at hlem
    exact hlem
  have hsplit :
    Complex.digamma ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I) =
      (Complex.digamma ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I) -
          Complex.digamma (1 - (t : ℂ) * Complex.I)) +
        Complex.digamma (1 - (t : ℂ) * Complex.I) := by
    ring
  calc
    ‖Complex.digamma ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I)‖ =
        ‖(Complex.digamma ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I) -
              Complex.digamma (1 - (t : ℂ) * Complex.I)) +
            Complex.digamma (1 - (t : ℂ) * Complex.I)‖ :=
      by rw [← hsplit]
    _ ≤
        ‖Complex.digamma ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I) -
              Complex.digamma (1 - (t : ℂ) * Complex.I)‖ +
          ‖Complex.digamma (1 - (t : ℂ) * Complex.I)‖ :=
      norm_add_le _ _
    _ ≤
        ((2 * m + 1 : ℕ) : ℝ) +
          8 * (Real.log (Real.sqrt Real.pi) - Real.log ‖Complex.Gamma (1 - (t : ℂ) * Complex.I)‖) :=
      by linarith [hprop, hone]
    _ =
        8 * (Real.log (Real.sqrt Real.pi) - Real.log ‖Complex.Gamma (1 - (t : ℂ) * Complex.I)‖) +
          (2 * m + 1) :=
      by
      push_cast; ring

/-- The zeta functional equation holds on an entire neighborhood of any point with `Re s > 1`. -/
theorem eventually_riemannZeta_one_sub_eq {s : ℂ} (hs : 1 < s.re) :
    (fun w => riemannZeta (1 - w)) =ᶠ[nhds s]
      (fun w =>
        2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2) *
          riemannZeta w) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  obtain ⟨hw1, hw2⟩ := side_conditions_of_one_lt_re hw
  exact riemannZeta_one_sub hw1 hw2

/-- The logarithmic derivative of `w ↦ (2π)^(-w)` is the constant `-log(2π)`. -/
theorem logDeriv_two_pi_cpow_neg (s : ℂ) :
    logDeriv (fun w => (2 * (Real.pi : ℂ)) ^ (-w)) s = -Complex.log (2 * (Real.pi : ℂ)) := by
  have hne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      or_self, not_false_eq_true]
  have hf : HasDerivAt (fun w : ℂ => -w) (-1) s := (hasDerivAt_id s).neg
  have hderiv :
    HasDerivAt (fun w => (2 * (Real.pi : ℂ)) ^ (-w))
      ((2 * (Real.pi : ℂ)) ^ (-s) * Complex.log (2 * (Real.pi : ℂ)) * (-1)) s :=
    hf.const_cpow (Or.inl hne)
  have hval_ne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    intro h
    exact hne ((Complex.cpow_eq_zero_iff _ _).mp h).1
  rw [logDeriv_apply, hderiv.deriv]
  field_simp

/-- The logarithmic derivative of `w ↦ cos(πw/2)` is `-(π/2) tan(πs/2)`. -/
theorem logDeriv_cos_pi_mul_div_two (s : ℂ) :
    logDeriv (fun w => Complex.cos ((Real.pi : ℂ) * w / 2)) s =
      -((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2) := by
  have hf : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w / 2) ((Real.pi : ℂ) / 2) s := by
    have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) s := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (Real.pi : ℂ)
    simpa only using h1.div_const 2
  have hderiv :
    HasDerivAt (fun w => Complex.cos ((Real.pi : ℂ) * w / 2))
      (-Complex.sin ((Real.pi : ℂ) * s / 2) * ((Real.pi : ℂ) / 2)) s :=
    hf.ccos
  rw [logDeriv_apply, hderiv.deriv, Complex.tan]
  ring

/-- The logarithmic-derivative form of the zeta functional equation: differentiating
`ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)` and dividing by `ζ(1-s)` reduces the entire `Re s < 0`
growth question to the growth of `digamma` on `Re s = 1` plus the already-known `Re s > 1`
bound on `ζ'/ζ` and the bounded `tan(πs/2)` term. -/
theorem logDeriv_riemannZeta_one_sub {s : ℂ} (hs : 1 < s.re)
    (hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0) :
    logDeriv riemannZeta (1 - s) =
      Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s +
        ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2) - logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by
    rw [h] at hs
    change (1 : ℝ) < 0 at hs
    norm_num only at hs
  have hGammane : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith only [hs])
  have hzetane : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hcpowne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    intro h
    exact (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (by simpa only [Complex.ofReal_eq_zero, Real.pi_ne_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
        or_self] using ((Complex.cpow_eq_zero_iff _ _).mp h).1)
  have hdiffGamma : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s (fun n hn => by
      have hre := congrArg Complex.re hn
      rw [Complex.neg_re, Complex.natCast_re] at hre
      linarith only [hs, hre, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
  have hdiffZeta : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (fun h => by rw [h] at hs; simp only [Complex.one_re,
      lt_self_iff_false] at hs)
  have h2pine : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      or_self, not_false_eq_true]
  have hdiffCpow : DifferentiableAt ℂ (fun w => (2 * (Real.pi : ℂ)) ^ (-w)) s :=
    (((hasDerivAt_id s).neg).const_cpow (c := 2 * (Real.pi : ℂ)) (Or.inl h2pine)).differentiableAt
  have hdiffCos : DifferentiableAt ℂ (fun w => Complex.cos ((Real.pi : ℂ) * w / 2)) s := by
    have hf : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w / 2) ((Real.pi : ℂ) / 2) s := by
      have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) s := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (Real.pi : ℂ)
      simpa only using h1.div_const 2
    exact hf.ccos.differentiableAt
  have hf1ne : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := mul_ne_zero two_ne_zero hcpowne
  have hf1diff : DifferentiableAt ℂ (fun w => (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-w)) s :=
    (differentiableAt_const 2).mul hdiffCpow
  have hf2ne : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s ≠ 0 :=
    mul_ne_zero hf1ne hGammane
  have hf2diff : DifferentiableAt ℂ
      (fun w => (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) s :=
    hf1diff.mul hdiffGamma
  have hf3ne : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
      Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := mul_ne_zero hf2ne hcos
  have hf3diff : DifferentiableAt ℂ (fun w => (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-w) *
      Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)) s :=
    hf2diff.mul hdiffCos
  have hRHS : logDeriv (fun w => 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
      Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w) s =
      -Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma s -
        ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2) + logDeriv riemannZeta s := by
    change logDeriv ((fun w ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
        Complex.cos ((Real.pi : ℂ) * w / 2)) * riemannZeta) s = _
    rw [logDeriv_mul s hf3ne hzetane hf3diff hdiffZeta,
      show (fun w ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
          Complex.cos ((Real.pi : ℂ) * w / 2)) =
        (fun w ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) *
          (fun w ↦ Complex.cos ((Real.pi : ℂ) * w / 2)) from by funext w; rfl,
      logDeriv_mul s hf2ne hcos hf2diff hdiffCos,
      show (fun w ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) =
        (fun w : ℂ ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-w)) *
          (fun w : ℂ ↦ Complex.Gamma w) from by
          funext w
          simp only [Pi.mul_apply]
          ,
      logDeriv_mul s hf1ne hGammane hf1diff hdiffGamma,
      logDeriv_const_mul s _ (two_ne_zero),
      logDeriv_two_pi_cpow_neg s, logDeriv_cos_pi_mul_div_two s,
      show logDeriv Complex.Gamma s = Complex.digamma s from (Complex.digamma_def ▸ rfl)]
    ring
  have heqnhds := eventually_riemannZeta_one_sub_eq hs
  have hLHS : logDeriv (fun w => riemannZeta (1 - w)) s = -logDeriv riemannZeta (1 - s) := by
    have hcompderiv : HasDerivAt (fun w : ℂ => 1 - w) (-1) s := (hasDerivAt_id s).const_sub 1
    have h1sne : (1 : ℂ) - s ≠ 1 := by
      intro h
      apply hs0
      have := congrArg (fun z => 1 - z) h
      simpa only [sub_sub_cancel, sub_self] using this
    have hcomp := logDeriv_comp (f := riemannZeta) (g := fun w : ℂ => 1 - w)
      (differentiableAt_riemannZeta h1sne) hcompderiv.differentiableAt
    rw [show riemannZeta ∘ (fun w : ℂ => 1 - w) = fun w => riemannZeta (1 - w) from rfl] at hcomp
    rw [hcomp, hcompderiv.deriv]
    ring
  have hval := (logDeriv_congr_nhds heqnhds).self_of_nhds
  rw [hRHS] at hval
  rw [hLHS] at hval
  linear_combination -hval

/-- `cos(πs/2) ≠ 0` at `s = (2m+2) - it`, since `π(m+1)` (an integer multiple of `π`) is never
an odd multiple of `π/2`, and the imaginary shift `-πt/2` can only vanish when `t = 0`. -/
theorem cos_pi_mul_two_mul_add_two_sub_mul_I_div_two_ne_zero (m : ℕ) (t : ℝ) :
    Complex.cos ((Real.pi : ℂ) * ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I) / 2) ≠ 0 := by
  have hrw :
    (Real.pi : ℂ) * ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I) / 2 =
      ((Real.pi * (m + 1) : ℝ) : ℂ) - ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrw]
  intro hcos0
  rw [Complex.cos_eq_zero_iff] at hcos0
  obtain ⟨k, hk⟩ := hcos0
  have him := congrArg Complex.im hk
  have hre := congrArg Complex.re hk
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.add_im, Complex.natCast_im, Complex.one_im, add_zero, mul_zero, Complex.ofReal_im,
    Complex.add_re, Complex.natCast_re, Complex.one_re, zero_mul, Complex.div_ofNat_re,
    Complex.mul_re, sub_zero, Complex.I_im, mul_one, Complex.div_ofNat_im, zero_div, Complex.I_re,
    zero_sub, Complex.re_ofNat, Complex.intCast_re, Complex.im_ofNat, Complex.intCast_im,
    neg_eq_zero, div_eq_zero_iff, mul_eq_zero, Real.pi_ne_zero, false_or, OfNat.ofNat_ne_zero,
    or_false, Complex.sub_re, sub_self] at him hre
  have hpi := Real.pi_ne_zero
  have h2 : Real.pi * (m + 1) = (2 * (k : ℝ) + 1) * Real.pi / 2 := by linarith [hre]
  have hfactor : Real.pi * ((m + 1 : ℝ) - (2 * (k : ℝ) + 1) / 2) = 0 := by linear_combination h2
  have hzero : (m + 1 : ℝ) - (2 * (k : ℝ) + 1) / 2 = 0 := (mul_eq_zero.mp hfactor).resolve_left hpi
  have hcontra : (2 : ℝ) * (m + 1) = 2 * k + 1 := by linarith [hzero]
  have hint : (2 : ℤ) * (m + 1) = 2 * k + 1 := by exact_mod_cast hcontra
  omega

/-- `‖tan(πs/2)‖ ≤ 1` at `s = (2m+2) - it`: the integer-multiple-of-`π` real part makes
`sin`/`cos` collapse to `∓sinh(πt/2)·I`/`±cosh(πt/2)`, whose ratio is a bounded hyperbolic
tangent. -/
theorem norm_tan_pi_mul_two_mul_add_two_sub_mul_I_div_two_le (m : ℕ) (t : ℝ) :
    ‖Complex.tan ((Real.pi : ℂ) * ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤ 1 := by
  have hrw :
    (Real.pi : ℂ) * ((2 * m + 2 : ℂ) - (t : ℂ) * Complex.I) / 2 =
      ((Real.pi * (m + 1) : ℝ) : ℂ) - ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hcast : ((((m : ℕ) + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by
    push_cast; ring
  have hsinreal : Real.sin (Real.pi * (m + 1)) = 0 := by
    have h := Real.sin_nat_mul_pi (m + 1)
    rw [mul_comm, hcast] at h
    exact h
  have hcosreal : Real.cos (Real.pi * (m + 1)) = (-1) ^ (m + 1) := by
    have h := Real.cos_nat_mul_pi (m + 1)
    rw [mul_comm, hcast] at h
    exact h
  have hsin_eq :
    Complex.sin (((Real.pi * (m + 1) : ℝ) : ℂ) - ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) =
      ((-1 : ℝ) ^ (m + 1) : ℂ) * (-(Complex.sinh ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.sin_sub, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_sin, ←
      Complex.ofReal_cos, hsinreal, hcosreal]
    push_cast; ring
  have hcos_eq :
    Complex.cos (((Real.pi * (m + 1) : ℝ) : ℂ) - ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) =
      ((-1 : ℝ) ^ (m + 1) : ℂ) * Complex.cosh ((Real.pi * t / 2 : ℝ) : ℂ) := by
    rw [Complex.cos_sub, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_sin, ←
      Complex.ofReal_cos, hsinreal, hcosreal]
    push_cast; ring
  have hsign : ((-1 : ℝ) ^ (m + 1) : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_neg, Complex.ofReal_one, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, pow_eq_zero_iff, neg_eq_zero]
  have htan_eq :
    Complex.tan (((Real.pi * (m + 1) : ℝ) : ℂ) - ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) =
      -(Complex.sinh ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) /
        Complex.cosh ((Real.pi * t / 2 : ℝ) : ℂ) := by
    rw [Complex.tan, hsin_eq, hcos_eq, mul_div_mul_left _ _ hsign]
  rw [hrw, htan_eq]
  have hcoshpos : (0 : ℝ) < Real.cosh (Real.pi * t / 2) := Real.cosh_pos _
  rw [norm_div, norm_neg, norm_mul, Complex.norm_I, mul_one,
    show Complex.sinh ((Real.pi * t / 2 : ℝ) : ℂ) = ((Real.sinh (Real.pi * t / 2) : ℝ) : ℂ) from
      (Complex.ofReal_sinh _).symm,
    show Complex.cosh ((Real.pi * t / 2 : ℝ) : ℂ) = ((Real.cosh (Real.pi * t / 2) : ℝ) : ℂ) from
      (Complex.ofReal_cosh _).symm,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [div_le_one (by rwa [abs_of_pos hcoshpos]), abs_of_pos hcoshpos]
  nlinarith only [Real.cosh_sq_sub_sinh_sq (Real.pi * t / 2), sq_abs (Real.sinh (Real.pi * t / 2)),
    abs_nonneg (Real.sinh (Real.pi * t / 2)), hcoshpos]

/-- At `z=-(2m+1)+it`, the functional equation bounds `‖ζ'/ζ(z)‖`
by fixed constants, a bounded tangent term, and the shifted digamma estimate. -/
theorem norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le (m : ℕ) (t : ℝ) :
    ‖logDeriv riemannZeta (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log (2 * Real.pi) +
        (8 * (Real.log (Real.sqrt Real.pi) - Real.log ‖Complex.Gamma (1 - (t : ℂ) * Complex.I)‖) +
          (2 * m + 1)) +
        Real.pi / 2 +
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (2 * m + 2 : ℝ) := by
  set s : ℂ := (2 * m + 2 : ℂ) - (t : ℂ) * Complex.I with hs_def
  have hzs : (1 : ℂ) - s = -(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I := by
    rw [hs_def]; ring
  have hs_re : (1 : ℝ) < s.re := by
    rw [hs_def]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
    have : ((2 * m + 2 : ℂ)).re = 2 * m + 2 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
        Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
    rw [this]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
  have hcos_ne := cos_pi_mul_two_mul_add_two_sub_mul_I_div_two_ne_zero m t
  rw [← hs_def] at hcos_ne
  have hident := logDeriv_riemannZeta_one_sub hs_re hcos_ne
  rw [hzs] at hident
  have hdigamma_le := norm_digamma_two_mul_add_two_sub_mul_I_le m t
  rw [← hs_def] at hdigamma_le
  have htan_le := norm_tan_pi_mul_two_mul_add_two_sub_mul_I_div_two_le m t
  rw [← hs_def] at htan_le
  have hzeta_le :
    ‖logDeriv riemannZeta s‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (2 * m + 2 : ℝ) := by
    have heq : s = ((2 * m + 2 : ℝ) : ℂ) + (-t) * Complex.I := by
      rw [hs_def]; push_cast; ring
    rw [heq, logDeriv_apply]
    have :=
      norm_deriv_riemannZeta_div_le (τ := (2 * m + 2 : ℝ))
        (by
          have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith)
        (-t)
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, neg_mul, Complex.norm_div, ge_iff_le, Complex.ofReal_neg] using this
  have hlogpi_le : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ Real.log (2 * Real.pi) := by
    have h2pi1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by
        push_cast; ring,
      ← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos h2pi1)]
  have hA :
    ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s‖ ≤
      ‖Complex.log (2 * (Real.pi : ℂ))‖ + ‖Complex.digamma s‖ :=
    norm_sub_le _ _
  have hB : ‖((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2)‖ ≤ Real.pi / 2 := by
    rw [norm_mul]
    have hpi2 : ‖(Real.pi : ℂ) / 2‖ = Real.pi / 2 := by
      rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) from by
          push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hpi2]
    calc
      Real.pi / 2 * ‖Complex.tan ((Real.pi : ℂ) * s / 2)‖ ≤ Real.pi / 2 * 1 :=
        mul_le_mul_of_nonneg_left htan_le (by positivity)
      _ = Real.pi / 2 := mul_one _
  have hfull :
    ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s +
            ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2) -
          logDeriv riemannZeta s‖ ≤
      ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s‖ +
        ‖((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2)‖ +
        ‖logDeriv riemannZeta s‖ := by
    calc
      ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s +
                ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2) -
              logDeriv riemannZeta s‖ ≤
          ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s +
                ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2)‖ +
            ‖logDeriv riemannZeta s‖ :=
        norm_sub_le _ _
      _ ≤
          (‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s‖ +
              ‖((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2)‖) +
            ‖logDeriv riemannZeta s‖ :=
        by
        gcongr
        exact norm_add_le _ _
  rw [hident]
  linarith [hfull, hA, hB, hlogpi_le, hdigamma_le, hzeta_le]

/-!
### A tangent bound independent of the real part

For nonzero imaginary part, `‖tan z‖ ≤ √(1+1/sinh(Im z)²)`.
This extends integer-line bounds to a continuous range of real parts.
-/

/-- `‖sin z‖² = sin(Re z)² cosh(Im z)² + cos(Re z)² sinh(Im z)²`. -/
theorem normSq_sin_eq (z : ℂ) :
    Complex.normSq (Complex.sin z) =
      Real.sin z.re ^ 2 * Real.cosh z.im ^ 2 + Real.cos z.re ^ 2 * Real.sinh z.im ^ 2 := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  have heq :
    Complex.sin z =
      ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ) +
        ((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [hz]
    rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I]
    push_cast
    ring
  rw [heq, Complex.normSq_add_mul_I]
  ring

/-- `‖cos z‖² = cos(Re z)² cosh(Im z)² + sin(Re z)² sinh(Im z)²`. -/
theorem normSq_cos_eq (z : ℂ) :
    Complex.normSq (Complex.cos z) =
      Real.cos z.re ^ 2 * Real.cosh z.im ^ 2 + Real.sin z.re ^ 2 * Real.sinh z.im ^ 2 := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  have heq :
    Complex.cos z =
      ((Real.cos z.re * Real.cosh z.im : ℝ) : ℂ) +
        ((-(Real.sin z.re * Real.sinh z.im) : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [hz]
    rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I]
    push_cast
    ring
  rw [heq, Complex.normSq_add_mul_I]
  ring

/-- **A uniform `tan` bound, independent of `Re z`.** For `z` with `Im z ≠ 0`,
`‖tan z‖ ≤ √(1 + 1/sinh(Im z)²)`: unlike the closed-form bound at integer real parts, this holds
for the entire horizontal strip needed by the zeta-side estimate's left-edge treatment. -/
theorem norm_tan_le_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    ‖Complex.tan z‖ ≤ Real.sqrt (1 + 1 / Real.sinh z.im ^ 2) := by
  have hspos : (0 : ℝ) < Real.sinh z.im ^ 2 := by
    have := Real.sinh_ne_zero.mpr hz
    positivity
  have hpyth : Real.sin z.re ^ 2 + Real.cos z.re ^ 2 = 1 := Real.sin_sq_add_cos_sq z.re
  have hhyp : Real.cosh z.im ^ 2 - Real.sinh z.im ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z.im
  have hdiff :
    Complex.normSq (Complex.sin z) - Complex.normSq (Complex.cos z) =
      Real.sin z.re ^ 2 - Real.cos z.re ^ 2 := by
    rw [normSq_sin_eq, normSq_cos_eq]
    nlinarith [hhyp]
  have hcos_ge : Real.sinh z.im ^ 2 ≤ Complex.normSq (Complex.cos z) := by
    rw [normSq_cos_eq]
    nlinarith [sq_nonneg (Real.cos z.re), hpyth]
  have hcos_pos : (0 : ℝ) < Complex.normSq (Complex.cos z) := lt_of_lt_of_le hspos hcos_ge
  have hcos_ne : Complex.cos z ≠ 0 := by
    intro h
    rw [h, Complex.normSq_zero] at hcos_pos
    exact absurd hcos_pos (lt_irrefl 0)
  have hkey :
    Complex.normSq (Complex.sin z) / Complex.normSq (Complex.cos z) ≤
      1 + 1 / Real.sinh z.im ^ 2 := by
    rw [div_le_iff₀ hcos_pos]
    have h1 : Real.sin z.re ^ 2 - Real.cos z.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos z.re)]
    have h2 : Complex.normSq (Complex.sin z) ≤ Complex.normSq (Complex.cos z) + 1 := by linarith
    have h3 :
      (1 + 1 / Real.sinh z.im ^ 2) * Complex.normSq (Complex.cos z) =
        Complex.normSq (Complex.cos z) + Complex.normSq (Complex.cos z) / Real.sinh z.im ^ 2 := by
      field_simp
    rw [h3]
    have h4 : (1 : ℝ) ≤ Complex.normSq (Complex.cos z) / Real.sinh z.im ^ 2 := by
      rw [le_div_iff₀ hspos]; linarith [hcos_ge]
    linarith
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  rw [show ‖Complex.sin z‖ = Real.sqrt (Complex.normSq (Complex.sin z)) from by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)],
    show ‖Complex.cos z‖ = Real.sqrt (Complex.normSq (Complex.cos z)) from by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)],
    ← Real.sqrt_div (Complex.normSq_nonneg _)]
  exact Real.sqrt_le_sqrt hkey

/-!
### Logarithmic derivatives at arbitrary negative real parts

Combine the zeta functional equation, the shifted digamma bound, and the
tangent estimate to bound `ζ'/ζ` at nonzero height and any negative real part.
-/

/-- `cos(πs/2) ≠ 0` whenever `Im s ≠ 0`: a zero would force `s` to be an odd integer
(`Complex.cos_eq_zero_iff`), which is real, contradicting `Im s ≠ 0`. Generalizes
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.cos_pi_mul_two_mul_add_two_sub_mul_I_div_two_ne_zero`
away from the integer-real-part case. -/
theorem cos_pi_mul_div_two_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
  intro hcos0
  rw [Complex.cos_eq_zero_iff] at hcos0
  obtain ⟨k, hk⟩ := hcos0
  apply hs
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs_eq : s = 2 * (k : ℂ) + 1 := by
    have h2 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by linear_combination 2 * hk
    exact mul_left_cancel₀ hpi_ne h2
  have him := congrArg Complex.im hs_eq
  simpa only [Complex.add_im, Complex.mul_im, Complex.re_ofNat, Complex.intCast_im, mul_zero,
    Complex.im_ofNat, Complex.intCast_re, zero_mul, add_zero, Complex.one_im] using him

/-- For any negative real part and nonzero height, the functional equation,
shifted digamma bound, and tangent estimate bound `‖ζ'/ζ‖`. -/
theorem norm_logDeriv_riemannZeta_neg_add_mul_I_le {σ : ℝ} (hσ : σ < 0) {t : ℝ} (ht : t ≠ 0) :
    ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log (2 * Real.pi) +
        8 *
          (Real.log (max (Real.Gamma (-σ + 1 / 2)) (Real.Gamma (-σ + 3 / 2)) + 1) -
            Real.log ‖Complex.Gamma ((1 - σ : ℝ) - (t : ℂ) * Complex.I)‖) +
        Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi * t / 2) ^ 2) +
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - σ : ℝ) := by
  set s : ℂ := (1 - σ : ℝ) - (t : ℂ) * Complex.I with hs_def
  have hzs : (1 : ℂ) - s = (σ : ℂ) + (t : ℂ) * Complex.I := by
    rw [hs_def]; push_cast; ring
  have hs_re : (1 : ℝ) < s.re := by
    rw [hs_def]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
    linarith
  have hs_im : s.im ≠ 0 := by
    rw [hs_def]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one,
      Complex.I_re, mul_zero, add_zero, zero_sub]
    simpa only [Complex.ofReal_re, ne_eq, neg_eq_zero] using ht
  have hcos_ne := cos_pi_mul_div_two_ne_zero_of_im_ne_zero hs_im
  have hident := logDeriv_riemannZeta_one_sub hs_re hcos_ne
  rw [hzs] at hident
  set r : ℝ := -σ with hr_def
  have hr_nonneg : (0 : ℝ) ≤ r := by
    rw [hr_def]; linarith
  have hdigamma_le := norm_digamma_shift_add_mul_I_le r hr_nonneg (-t)
  have hseq : ((1 + r : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = s := by
    rw [hs_def, hr_def]; push_cast; ring
  rw [hseq] at hdigamma_le
  have htan_le :
    ‖Complex.tan ((Real.pi : ℂ) * s / 2)‖ ≤
      Real.sqrt (1 + 1 / Real.sinh (Real.pi * t / 2) ^ 2) := by
    have hz_eq :
      (Real.pi : ℂ) * s / 2 =
        ((Real.pi * (1 - σ) / 2 : ℝ) : ℂ) + ((-(Real.pi * t / 2) : ℝ) : ℂ) * Complex.I := by
      rw [hs_def]; push_cast; ring
    have hz_im : ((Real.pi : ℂ) * s / 2).im = -(Real.pi * t / 2) := by
      rw [hz_eq]; simp
    have hz_im_ne : ((Real.pi : ℂ) * s / 2).im ≠ 0 := by
      rw [hz_im]
      intro h
      apply ht
      have hpi_pos := Real.pi_pos
      nlinarith [h]
    have hbound := norm_tan_le_of_im_ne_zero hz_im_ne
    rwa [hz_im, Real.sinh_neg, neg_sq] at hbound
  have hzeta_le :
    ‖logDeriv riemannZeta s‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - σ : ℝ) := by
    have heq : s = ((1 - σ : ℝ) : ℂ) + (-t) * Complex.I := by
      rw [hs_def]; push_cast; ring
    rw [heq, logDeriv_apply]
    have := norm_deriv_riemannZeta_div_le (τ := (1 - σ : ℝ)) (by linarith) (-t)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, neg_mul, Complex.norm_div, ge_iff_le,
      Complex.ofReal_neg] using this
  have hlogpi_le : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ Real.log (2 * Real.pi) := by
    have h2pi1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by
        push_cast; ring,
      ← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos h2pi1)]
  have hA :
    ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s‖ ≤
      ‖Complex.log (2 * (Real.pi : ℂ))‖ + ‖Complex.digamma s‖ :=
    norm_sub_le _ _
  have hB :
    ‖((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2)‖ ≤
      Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi * t / 2) ^ 2) := by
    rw [norm_mul]
    have hpi2 : ‖(Real.pi : ℂ) / 2‖ = Real.pi / 2 := by
      rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) from by
          push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hpi2]
    exact mul_le_mul_of_nonneg_left htan_le (by positivity)
  have hfull :
    ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s +
            ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2) -
          logDeriv riemannZeta s‖ ≤
      ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s‖ +
        ‖((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2)‖ +
        ‖logDeriv riemannZeta s‖ := by
    calc
      ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s +
                ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2) -
              logDeriv riemannZeta s‖ ≤
          ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s +
                ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2)‖ +
            ‖logDeriv riemannZeta s‖ :=
        norm_sub_le _ _
      _ ≤
          (‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma s‖ +
              ‖((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * s / 2)‖) +
            ‖logDeriv riemannZeta s‖ :=
        by
        gcongr
        exact norm_add_le _ _
  rw [hident]
  linarith [hfull, hA, hB, hlogpi_le, hdigamma_le, hzeta_le]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
