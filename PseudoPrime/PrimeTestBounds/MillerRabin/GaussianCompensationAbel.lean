/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerError570

/-! # Centered Abel estimate for the high Gaussian compensation -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem compensation_error_le (hRH : RiemannHypothesis) {a b t w : ℝ} (ha : 1000000 ≤ a)
    (ht : t ∈ Set.Icc a b) :
    -((Chebyshev.psi t - t) * w) ≤ Real.log b ^ 2 / 24 * (Real.sqrt t * |w|) := by
  have ht₀ := (by norm_num only : (0 : ℝ) < 1000000).trans_le (ha.trans ht.1)
  have hlog :=
    pow_le_pow_left₀
      (Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 1000000).trans (ha.trans ht.1)))
      (Real.log_le_log ht₀ ht.2) 2
  have hψ := euler570_psi_high hRH (ha.trans ht.1)
  calc
    _ ≤ |(Chebyshev.psi t - t) * w| := neg_le_abs _
    _ = |Chebyshev.psi t - t| * |w| := abs_mul _ _
    _ ≤ (Real.sqrt t * (Real.log t ^ 2 / 24)) * |w| := mul_le_mul_of_nonneg_right hψ (abs_nonneg _)
    _ ≤ _ := by
      rw [show
          Real.log b ^ 2 / 24 * (Real.sqrt t * |w|) = (Real.sqrt t * (Real.log b ^ 2 / 24)) * |w| by
          ring]
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog (by norm_num only))
            (Real.sqrt_nonneg _))
          (abs_nonneg _)

/-- Apply the RH square-log bound to the centered Abel formula on one
smooth piece. Keep the endpoint terms so that adjacent pieces can cancel. -/
theorem gaussian_compensation_piece (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1000000 ≤ a)
    (hab : a ≤ b) {f : ℝ → ℝ} (hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * f n) ≤
      (∫ t in a..b, f t) + (Chebyshev.psi b - b) * f b - (Chebyshev.psi a - a) * f a +
        Real.log b ^ 2 / 24 * (∫ t in a..b, Real.sqrt t * |deriv f t|) := by
  have ha₀ := (by norm_num only : (0 : ℝ) ≤ 1000000).trans ha
  have hψ := integrableOn_mul_sum_Icc (fun n ↦ ArithmeticFunction.vonMangoldt n) (m := 0) ha₀ hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at hψ
  have ht := hi.mul_continuousOn continuousOn_id isCompact_Icc
  have herr :
    MeasureTheory.IntegrableOn (fun t ↦ -((Chebyshev.psi t - t) * deriv f t)) (Set.Icc a b) := by
    convert (hψ.sub ht).neg using 1
    funext t
    simp only [Pi.sub_apply, Pi.neg_apply, id_eq]
    ring
  have hfabs : MeasureTheory.IntegrableOn (fun t ↦ |deriv f t|) (Set.Icc a b) := hi.abs
  have hv := hfabs.mul_continuousOn Real.continuous_sqrt.continuousOn isCompact_Icc
  have hv' :
    MeasureTheory.IntegrableOn (fun t ↦ Real.log b ^ 2 / 24 * (Real.sqrt t * |deriv f t|))
      (Set.Icc a b) := by
    simpa only [MeasureTheory.IntegrableOn, mul_comm (Real.sqrt _)] using
      hv.const_mul (Real.log b ^ 2 / 24)
  have hmono :=
    intervalIntegral.integral_mono_on hab
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr herr)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hv')
      (fun t ht ↦ compensation_error_le hRH ha ht (w := deriv f t))
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hmono
  have h := AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha₀ hab hd hi
  linarith only [h, hmono]

/-- For a compensation weight vanishing at both endpoints, the main
integral plus the RH variation charge bounds the entire Mangoldt sum. -/
theorem gaussian_compensation_interval (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1000000 ≤ a)
    (hab : a ≤ b) {f : ℝ → ℝ} (hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) (hfa : f a = 0) (hfb : f b = 0) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * f n) ≤
      (∫ t in a..b, f t) + Real.log b ^ 2 / 24 * (∫ t in a..b, Real.sqrt t * |deriv f t|) := by
  simpa only [hfa, hfb, mul_zero, add_zero, sub_zero] using
    gaussian_compensation_piece hRH ha hab hd hi

/-- The physical compensation weight on a polynomial piece of the high kernel. -/
@[expose]
noncomputable def gaussianCompensationWeight (P : Polynomial ℝ) (X b a t : ℝ) : ℝ :=
  let v := b - Real.log (t / X)
  t ^ (-(1 / 2) : ℝ) * Real.exp (-a * v) * P.eval v

private theorem compensation_log_div_deriv {X t : ℝ} (hX : 0 < X) (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ Real.log (z / X)) t⁻¹ t := by
  have h := (Real.hasDerivAt_log (div_ne_zero ht.ne' hX.ne')).comp t ((hasDerivAt_id t).div_const X)
  have he : (t / X)⁻¹ * (1 / X) = t⁻¹ := by
    rw [inv_div, one_div, div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hX.ne', one_mul]
  rw [he] at h
  exact h

/-- On a positive physical argument the profile derivative gives the signed
variation polynomial appearing in H14. -/
theorem gaussian_compensation_hasDerivAt (P : Polynomial ℝ) {X b a t : ℝ} (hX : 0 < X)
    (ht : 0 < t) :
    let v := b - Real.log (t / X)
    HasDerivAt (gaussianCompensationWeight P X b a)
      (t ^ (-(1 / 2) : ℝ) * t⁻¹ * Real.exp (-a * v) *
        ((a - 1 / 2) * P.eval v - P.derivative.eval v))
      t := by
  intro v
  have hl := compensation_log_div_deriv hX ht
  have hv := hl.const_sub b
  have he := (Real.hasDerivAt_exp (-a * v)).comp t (hv.const_mul (-a))
  have hP := (P.hasDerivAt v).comp t hv
  have hw := Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl ht.ne')
  convert (hw.mul he).mul hP using 1
  · rfl
  · dsimp only [Function.comp_apply, Pi.mul_apply, v]
    rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
    ring

/-- The derivative of a polynomial compensation weight is integrable on
every compact physical interval with positive left endpoint. -/
theorem gaussian_compensation_deriv_integrable (P : Polynomial ℝ) {X b a l r : ℝ} (hX : 0 < X)
    (hl : 0 < l) :
    MeasureTheory.IntegrableOn (deriv (gaussianCompensationWeight P X b a)) (Set.Icc l r) := by
  apply ContinuousOn.integrableOn_Icc
  refine
    ContinuousOn.congr ?_
      (fun t ht ↦
        (gaussian_compensation_hasDerivAt P (b := b) (a := a) hX (hl.trans_le ht.1)).deriv)
  intro t ht
  have ht₀ := (hl.trans_le ht.1).ne'
  have hv := ((compensation_log_div_deriv hX (hl.trans_le ht.1)).const_sub b).continuousAt
  have hp :=
    (Real.continuousAt_rpow_const t (-(1 / 2) : ℝ) (Or.inl ht₀)).mul (continuousAt_id.inv₀ ht₀)
  have he : ContinuousAt (fun x ↦ Real.exp (-a * (b - Real.log (x / X)))) t :=
    Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hv)
  exact
    ((hp.mul he).mul
        ((continuousAt_const.mul (P.continuous.continuousAt.comp hv)).sub
          (P.derivative.continuous.continuousAt.comp hv))).continuousWithinAt

/-- The square-root factor in the RH error cancels the radial inverse
square root. The remaining physical variation is the log-scale integrand. -/
theorem gaussian_compensation_variation (P : Polynomial ℝ) {X b a t : ℝ} (hX : 0 < X) (ht : 0 < t) :
    let v := b - Real.log (t / X)
    Real.sqrt t * |deriv (gaussianCompensationWeight P X b a) t| =
      Real.exp (-a * v) * |(a - 1 / 2) * P.eval v - P.derivative.eval v| / t := by
  intro v
  rw [(gaussian_compensation_hasDerivAt P (b := b) (a := a) hX ht).deriv]
  rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t)),
    abs_of_nonneg (inv_nonneg.mpr ht.le), abs_of_nonneg (Real.exp_pos _).le]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 ht).ne', one_mul]
  dsimp only [v]
  ring

private theorem compensation_log_reverse {X b : ℝ} (hX : 0 < X) (hb : 0 ≤ b) {G : ℝ → ℝ}
    (hG : Continuous G) :
    (∫ t in X..X * Real.exp b, G (b - Real.log (t / X)) / t) = ∫ v in 0..b, G v := by
  let f := fun t : ℝ ↦ b - Real.log (t / X)
  have hXY : X ≤ X * Real.exp b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp hb) hX.le
  have ht (t : ℝ) (hm : t ∈ Set.uIcc X (X * Real.exp b)) : 0 < t :=
    hX.trans_le (Set.uIcc_of_le hXY ▸ hm).1
  have hc : ContinuousOn (fun t : ℝ ↦ -t⁻¹) (Set.uIcc X (X * Real.exp b)) :=
    (continuousOn_id.inv₀ (fun t hm ↦ (ht t hm).ne')).neg
  have h :=
    intervalIntegral.integral_comp_mul_deriv (f := f) (g := G)
      (fun t hm ↦ (compensation_log_div_deriv hX (ht t hm)).const_sub b) hc hG
  have hl : f X = b := by simp only [f, div_self hX.ne', Real.log_one, sub_zero]
  have hu : f (X * Real.exp b) = 0 := by
    change b - Real.log (X * Real.exp b / X) = 0
    rw [show X * Real.exp b / X = Real.exp b by rw [mul_comm, mul_div_cancel_right₀ _ hX.ne'],
      Real.log_exp, sub_self]
  rw [hl, hu, intervalIntegral.integral_symm 0 b] at h
  have hneg :
    (∫ t in X..X * Real.exp b, (G ∘ f) t * -t⁻¹) =
      -(∫ t in X..X * Real.exp b, G (b - Real.log (t / X)) / t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Function.comp_apply, f, div_eq_mul_inv, mul_neg]
  rw [hneg] at h
  exact neg_injective h

/-- Reverse the logarithmic coordinate on a subinterval of the physical support. -/
theorem gaussian_log_cell_integral {X b l r : ℝ} (hX : 0 < X) (hlr : l ≤ r) {G : ℝ → ℝ}
    (hG : Continuous G) :
    (∫ t in X * Real.exp (b - r)..X * Real.exp (b - l), G (b - Real.log (t / X)) / t) =
      ∫ v in l..r, G v := by
  let x := fun v : ℝ ↦ X * Real.exp (b - v)
  let f := fun t : ℝ ↦ b - Real.log (t / X)
  have hx : x r ≤ x l :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hlr b)) hX.le
  have hp (t : ℝ) (ht : t ∈ Set.uIcc (x r) (x l)) : 0 < t :=
    (mul_pos hX (Real.exp_pos _)).trans_le (Set.uIcc_of_le hx ▸ ht).1
  have hc : ContinuousOn (fun t : ℝ ↦ -t⁻¹) (Set.uIcc (x r) (x l)) :=
    (continuousOn_id.inv₀ (fun t ht ↦ (hp t ht).ne')).neg
  have he (v : ℝ) : f (x v) = v := by
    simp only [f, x, mul_div_cancel_left₀ _ hX.ne', Real.log_exp, sub_sub_cancel]
  have h :=
    intervalIntegral.integral_comp_mul_deriv (f := f) (g := G)
      (fun t ht ↦ (compensation_log_div_deriv hX (hp t ht)).const_sub b) hc hG
  rw [he, he, intervalIntegral.integral_symm l r] at h
  apply neg_injective
  simpa only [Function.comp_apply, f, mul_neg, ← intervalIntegral.integral_neg,
    div_eq_mul_inv] using h

/-- On a whole polynomial piece from X to X exp b, the physical variation
equals the log-scale variation in H14. -/
theorem gaussian_compensation_variation_integral (P : Polynomial ℝ) {X b a : ℝ} (hX : 0 < X)
    (hb : 0 ≤ b) :
    (∫ t in X..X * Real.exp b, Real.sqrt t * |deriv (gaussianCompensationWeight P X b a) t|) =
      ∫ v in 0..b, Real.exp (-a * v) * |(a - 1 / 2) * P.eval v - P.derivative.eval v| := by
  have hXY : X ≤ X * Real.exp b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp hb) hX.le
  let G := fun v : ℝ ↦ Real.exp (-a * v) * |(a - 1 / 2) * P.eval v - P.derivative.eval v|
  have hc : Continuous G :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_const.mul P.continuous).sub P.derivative.continuous).abs
  refine Eq.trans ?_ (compensation_log_reverse hX hb hc)
  apply intervalIntegral.integral_congr
  intro t ht
  exact gaussian_compensation_variation P hX (hX.trans_le (Set.uIcc_of_le hXY ▸ ht).1)

/-- The main integral on a log cell factors into the physical cutoff
multiplier and the exponential log-coordinate integral. -/
theorem gaussian_compensation_main_cell (P : Polynomial ℝ) {X b a l r : ℝ} (hX : 0 < X)
    (hlr : l ≤ r) :
    (∫ t in X * Real.exp (b - r)..X * Real.exp (b - l), gaussianCompensationWeight P X b a t) =
      (Real.sqrt X * Real.exp (b / 2)) * ∫ v in l..r, Real.exp (-(a + 1 / 2) * v) * P.eval v := by
  have hXY := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hlr b)) hX.le
  let G := fun v : ℝ ↦ Real.exp (-(a + 1 / 2) * v) * P.eval v
  let k := Real.sqrt X * Real.exp (b / 2)
  have hc : Continuous G :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul P.continuous
  have hr :=
    gaussian_log_cell_integral (b := b) (G := fun v ↦ k * G v) hX hlr (continuous_const.mul hc)
  change _ = k * ∫ v in l..r, G v
  rw [← intervalIntegral.integral_const_mul, ← hr]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht₀ := (mul_pos hX (Real.exp_pos (b - r))).trans_le (Set.uIcc_of_le hXY ▸ ht).1
  let v := b - Real.log (t / X)
  have ht' : t = X * Real.exp (b - v) := by
    rw [show b - v = Real.log (t / X) by
        dsimp only [v]; ring,
      Real.exp_log (div_pos ht₀ hX), mul_div_cancel₀ _ hX.ne']
  have hs : Real.sqrt t = Real.sqrt X * Real.exp ((b - v) / 2) := by
    rw [Real.exp_half, ← Real.sqrt_mul hX.le, ← ht']
  have hf : t ^ (-(1 / 2) : ℝ) = Real.sqrt t / t := by
    rw [Real.rpow_neg ht₀.le, ← Real.sqrt_eq_rpow]
    apply (eq_div_iff ht₀.ne').mpr
    calc
      _ = (Real.sqrt t)⁻¹ * (Real.sqrt t) ^ 2 :=
        congrArg ((Real.sqrt t)⁻¹ * ·) (Real.sq_sqrt ht₀.le).symm
      _ = _ := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 ht₀).ne', one_mul]
  change t ^ (-(1 / 2) : ℝ) * Real.exp (-a * v) * P.eval v = k * G v / t
  rw [hf, hs]
  dsimp only [k, G]
  rw [show (b - v) / 2 = b / 2 - v / 2 by ring, Real.exp_sub]
  rw [show -(a + 1 / 2) * v = -a * v - v / 2 by ring, Real.exp_sub]
  ring

/-- Specialize the main charge to the entire physical support. -/
theorem gaussian_compensation_main_integral (P : Polynomial ℝ) {X b a : ℝ} (hX : 0 < X)
    (hb : 0 ≤ b) :
    (∫ t in X..X * Real.exp b, gaussianCompensationWeight P X b a t) =
      (Real.sqrt X * Real.exp (b / 2)) * ∫ v in 0..b, Real.exp (-(a + 1 / 2) * v) * P.eval v := by
  simpa only [sub_self, Real.exp_zero, mul_one, sub_zero] using
    gaussian_compensation_main_cell P (b := b) (a := a) hX hb

/-- The smooth polynomial version of H16. The two analytic charges are
written in the log coordinate, and the endpoint zeros remove the Abel terms. -/
theorem gaussian_polynomial_compensation (hRH : RiemannHypothesis) (P : Polynomial ℝ) {X b a : ℝ}
    (hX : 1000000 ≤ X) (hb : 0 ≤ b) (h0 : P.eval 0 = 0) (hbP : P.eval b = 0)
    (hi :
      MeasureTheory.IntegrableOn (deriv (gaussianCompensationWeight P X b a))
        (Set.Icc X (X * Real.exp b))) :
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp b⌋₊,
        ArithmeticFunction.vonMangoldt n * gaussianCompensationWeight P X b a n) ≤
      Real.sqrt X * Real.exp (b / 2) * (∫ v in 0..b, Real.exp (-(a + 1 / 2) * v) * P.eval v) +
        (Real.log (X * Real.exp b)) ^ 2 / 24 *
          (∫ v in 0..b, Real.exp (-a * v) * |(a - 1 / 2) * P.eval v - P.derivative.eval v|) := by
  have hp := (by norm_num only : (0 : ℝ) < 1000000).trans_le hX
  have hXY : X ≤ X * Real.exp b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp hb) hp.le
  have hleft : gaussianCompensationWeight P X b a X = 0 := by
    simp only [gaussianCompensationWeight, div_self hp.ne', Real.log_one, sub_zero, hbP, mul_zero]
  have hright : gaussianCompensationWeight P X b a (X * Real.exp b) = 0 := by
    simp only [gaussianCompensationWeight, mul_div_cancel_left₀ _ hp.ne', Real.log_exp, sub_self,
      h0, mul_zero]
  have h :=
    gaussian_compensation_interval hRH hX hXY
      (fun t ht ↦ (gaussian_compensation_hasDerivAt P hp (hp.trans_le ht.1)).differentiableAt) hi
      hleft hright
  rw [gaussian_compensation_main_integral P hp hb,
    gaussian_compensation_variation_integral P hp hb] at h
  exact h

/-- Sum the centered Abel estimates along an increasing chain of smooth
pieces. Matching weights at each shared endpoint cancel its Chebyshev term. -/
theorem gaussian_compensation_chain (hRH : RiemannHypothesis) (k : ℕ) (x : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hx : ∀ j < k, 1000000 ≤ x j ∧ x j ≤ x (j + 1))
    (hd : ∀ j < k, ∀ t ∈ Set.Icc (x j) (x (j + 1)), DifferentiableAt ℝ (f j) t)
    (hi : ∀ j < k, MeasureTheory.IntegrableOn (deriv (f j)) (Set.Icc (x j) (x (j + 1))))
    (hj : ∀ j, j + 1 < k → f j (x (j + 1)) = f (j + 1) (x (j + 1))) :
    (∑ j ∈ Finset.range k,
        ∑ n ∈ Finset.Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊, ArithmeticFunction.vonMangoldt n * f j n) ≤
      (∑ j ∈ Finset.range k,
          ((∫ t in x j..x (j + 1), f j t) +
            Real.log (x (j + 1)) ^ 2 / 24 *
              (∫ t in x j..x (j + 1), Real.sqrt t * |deriv (f j) t|))) +
        (if k = 0 then 0
        else
          (Chebyshev.psi (x k) - x k) * f (k - 1) (x k) -
            (Chebyshev.psi (x 0) - x 0) * f 0 (x 0)) := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, ite_true, add_zero, le_refl]
  | succ k
    ih =>
    have hpiece :=
      gaussian_compensation_piece hRH (hx k (Nat.lt_succ_self k)).1 (hx k (Nat.lt_succ_self k)).2
        (hd k (Nat.lt_succ_self k)) (hi k (Nat.lt_succ_self k))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ite_eq_right (Nat.succ_ne_zero k),
      Nat.add_sub_cancel]
    by_cases hk : k = 0
    · subst k
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      linarith only [hpiece]
    have hold :=
      ih (fun j h ↦ hx j (h.trans (Nat.lt_succ_self k)))
        (fun j h ↦ hd j (h.trans (Nat.lt_succ_self k)))
        (fun j h ↦ hi j (h.trans (Nat.lt_succ_self k)))
        (fun j h ↦ hj j (h.trans (Nat.lt_succ_self k)))
    have hidx : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)
    have hmatch := hj (k - 1) (hidx ▸ Nat.lt_succ_self k)
    rw [hidx] at hmatch
    rw [ite_eq_right hk, hmatch] at hold
    linarith only [hold, hpiece]

private theorem mangoldt_partition_sum (k : ℕ) (x : ℕ → ℝ) (hx : Monotone x) (F : ℝ → ℝ) :
    (∑ j ∈ Finset.range k,
        ∑ n ∈ Finset.Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊, ArithmeticFunction.vonMangoldt n * F n) =
      ∑ n ∈ Finset.Ioc ⌊x 0⌋₊ ⌊x k⌋₊, ArithmeticFunction.vonMangoldt n * F n := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.Ioc_self, Finset.sum_empty]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h0 := Nat.floor_mono (hx (Nat.zero_le k))
    have h1 := Nat.floor_mono (hx (Nat.le_succ k))
    have hdis : Disjoint (Finset.Ioc ⌊x 0⌋₊ ⌊x k⌋₊) (Finset.Ioc ⌊x k⌋₊ ⌊x (k + 1)⌋₊) := by
      rw [Finset.disjoint_left]
      exact fun n h h' ↦ (not_lt_of_ge (Finset.mem_Ioc.mp h).2) (Finset.mem_Ioc.mp h').1
    rw [← Finset.sum_union hdis, Finset.Ioc_union_Ioc_eq_Ioc h0 h1]

/-- Bound a continuous piecewise-smooth compensation weight by summing the
main and variation charges of its pieces. The endpoints of the whole support vanish. -/
theorem gaussian_compensation_partition (hRH : RiemannHypothesis) (k : ℕ) (x : ℕ → ℝ)
    (hx : Monotone x) (ha : 1000000 ≤ x 0) (F : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hm : ∀ j < k, ∀ t ∈ Set.Icc (x j) (x (j + 1)), f j t = F t)
    (hd : ∀ j < k, ∀ t ∈ Set.Icc (x j) (x (j + 1)), DifferentiableAt ℝ (f j) t)
    (hi : ∀ j < k, MeasureTheory.IntegrableOn (deriv (f j)) (Set.Icc (x j) (x (j + 1))))
    (h0 : F (x 0) = 0) (hk : F (x k) = 0) :
    (∑ n ∈ Finset.Ioc ⌊x 0⌋₊ ⌊x k⌋₊, ArithmeticFunction.vonMangoldt n * F n) ≤
      ∑ j ∈ Finset.range k,
        ((∫ t in x j..x (j + 1), f j t) +
          Real.log (x (j + 1)) ^ 2 / 24 *
            (∫ t in x j..x (j + 1), Real.sqrt t * |deriv (f j) t|)) := by
  by_cases hpos : k = 0
  · subst k
    simp only [Finset.Ioc_self, Finset.range_zero, Finset.sum_empty, le_refl]
  have hstep (j : ℕ) : x j ≤ x (j + 1) := hx (Nat.le_succ j)
  have hmatch (j : ℕ) (hj : j + 1 < k) : f j (x (j + 1)) = f (j + 1) (x (j + 1)) :=
    (hm j ((Nat.lt_succ_self j).trans hj) _ ⟨hstep j, le_rfl⟩).trans
      (hm (j + 1) hj _ ⟨le_rfl, hstep (j + 1)⟩).symm
  have h :=
    gaussian_compensation_chain hRH k x f (fun j _ ↦ ⟨ha.trans (hx (Nat.zero_le j)), hstep j⟩) hd hi
      hmatch
  have hj : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.pos_of_ne_zero hpos)
  have hbmem : x k ∈ Set.Icc (x (k - 1)) (x (k - 1 + 1)) := by
    rw [hj]
    exact ⟨hx (Nat.sub_le k 1), le_rfl⟩
  have hlast : f (k - 1) (x k) = 0 :=
    (hm _ (Nat.sub_lt (Nat.pos_of_ne_zero hpos) Nat.one_pos) _ hbmem).trans hk
  have hfirst : f 0 (x 0) = 0 := (hm 0 (Nat.pos_of_ne_zero hpos) _ ⟨le_rfl, hstep 0⟩).trans h0
  rw [ite_eq_right hpos, hlast, hfirst, mul_zero, mul_zero, sub_self, add_zero] at h
  rw [← mangoldt_partition_sum k x hx F]
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro j hj'
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Ioc.mp hn
  have hnL := (Nat.lt_of_floor_lt hn'.1).le
  have hnU : (n : ℝ) ≤ x (j + 1) :=
    (Nat.cast_le.mpr hn'.2).trans
      (Nat.floor_le
        ((by norm_num only : (0 : ℝ) ≤ 1000000).trans (ha.trans (hx (Nat.zero_le (j + 1))))))
  rw [hm j (Finset.mem_range.mp hj') _ ⟨hnL, hnU⟩]

/-- Change variables from the physical interval to any logarithmic compensation cell. -/
theorem gaussian_compensation_variation_cell (P : Polynomial ℝ) {X b a l r : ℝ} (hX : 0 < X)
    (hlr : l ≤ r) :
    (∫ t in X * Real.exp (b - r)..X * Real.exp (b - l),
        Real.sqrt t * |deriv (gaussianCompensationWeight P X b a) t|) =
      ∫ v in l..r, Real.exp (-a * v) * |(a - 1 / 2) * P.eval v - P.derivative.eval v| := by
  let G := fun v : ℝ ↦ Real.exp (-a * v) * |(a - 1 / 2) * P.eval v - P.derivative.eval v|
  have hc : Continuous G :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_const.mul P.continuous).sub P.derivative.continuous).abs
  rw [← gaussian_log_cell_integral (b := b) (G := G) hX hlr hc]
  apply intervalIntegral.integral_congr
  intro t ht
  have hAB := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hlr b)) hX.le
  exact
    gaussian_compensation_variation P hX
      ((mul_pos hX (Real.exp_pos _)).trans_le (Set.uIcc_of_le hAB ▸ ht).1)

/-- Under RH, bound the Mangoldt sum on a logarithmic polynomial cell, retaining
the two boundary terms for cancellation when adjoining cells are joined. -/
theorem gaussian_compensation_log_piece (hRH : RiemannHypothesis) (P : Polynomial ℝ) {X b a l r : ℝ}
    (hX : 0 < X) (hlr : l ≤ r) (hA : 1000000 ≤ X * Real.exp (b - r)) :
    let A := X * Real.exp (b - r)
    let B := X * Real.exp (b - l)
    let f := gaussianCompensationWeight P X b a
    (∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * f m) ≤
      (Real.sqrt X * Real.exp (b / 2)) * (∫ v in l..r, Real.exp (-(a + 1 / 2) * v) * P.eval v) +
            (Chebyshev.psi B - B) * f B -
          (Chebyshev.psi A - A) * f A +
        Real.log B ^ 2 / 24 *
          (∫ v in l..r, Real.exp (-a * v) * |(a - 1 / 2) * P.eval v - P.derivative.eval v|) := by
  intro A B f
  have hAB : A ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hlr b)) hX.le
  have hp : 0 < A := mul_pos hX (Real.exp_pos _)
  have h :=
    gaussian_compensation_piece hRH hA hAB
      (fun t ht ↦
        (gaussian_compensation_hasDerivAt P (b := b) (a := a) hX
            (hp.trans_le ht.1)).differentiableAt)
      (gaussian_compensation_deriv_integrable P hX hp)
  rw [gaussian_compensation_main_cell P hX hlr, gaussian_compensation_variation_cell P hX hlr] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
