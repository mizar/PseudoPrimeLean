/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleCells
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Direct middle residual and its signed curvature -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The polynomial left after differentiating a term weighted by `exp(-r*x)`. -/
@[expose]
public noncomputable def gaussianDecayDeriv (r : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P.derivative - Polynomial.C r * P

/-- Differentiate one polynomial-exponential term without losing its sign. -/
private theorem gaussian_decay_hasDerivAt (r : ℝ) (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun t ↦ Real.exp (-r * t) * P.eval t)
      (Real.exp (-r * x) * (gaussianDecayDeriv r P).eval x) x := by
  have he := ((hasDerivAt_id x).const_mul (-r)).exp
  have h := he.mul (P.hasDerivAt x)
  convert h using 1
  · rfl
  · simp only [gaussianDecayDeriv, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      id_eq, mul_one]
    ring

/-- A finite sum of exponential terms with fixed rates and polynomial profiles. -/
@[expose]
public noncomputable def gaussianDecaySum {m : ℕ} (r : Fin m → ℝ) (P : Fin m → Polynomial ℝ)
    (x : ℝ) : ℝ :=
  ∑ i, Real.exp (-r i * x) * (P i).eval x

/-- Differentiate every term of the finite sum once. -/
private theorem gaussian_decay_sum_deriv {m : ℕ} (r : Fin m → ℝ) (P : Fin m → Polynomial ℝ)
    (x : ℝ) :
    HasDerivAt (gaussianDecaySum r P)
      (gaussianDecaySum r (fun i ↦ gaussianDecayDeriv (r i) (P i)) x) x := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ ↦ gaussian_decay_hasDerivAt (r i) (P i) x)
  convert h using 1
  · funext t
    simp only [gaussianDecaySum, Finset.sum_apply]
  · rfl

/-- The middle residual at a fixed scale. The slope already includes the
linear conductor cost and the sum contains the signed decay profiles. -/
@[expose]
public noncomputable def gaussianMidResidual {m : ℕ} (s b β : ℝ) (r : Fin m → ℝ)
    (P : Fin m → Polynomial ℝ) (x : ℝ) : ℝ :=
  s * Real.exp (x / 2) + b - (β / 4) * x ^ 2 - gaussianDecaySum r P x

/-- The first derivative of the direct middle residual. -/
@[expose]
public noncomputable def gaussianMidResidualDeriv {m : ℕ} (s β : ℝ) (r : Fin m → ℝ)
    (P : Fin m → Polynomial ℝ) (x : ℝ) : ℝ :=
  (s / 2) * Real.exp (x / 2) - (β / 2) * x -
    gaussianDecaySum r (fun i ↦ gaussianDecayDeriv (r i) (P i)) x

/-- In the curvature estimate, the conductor and quadratic pieces retain
their signs, and each decay profile is differentiated twice. -/
@[expose]
public noncomputable def gaussianMidResidualCurv {m : ℕ} (s β : ℝ) (r : Fin m → ℝ)
    (P : Fin m → Polynomial ℝ) (x : ℝ) : ℝ :=
  (s / 4) * Real.exp (x / 2) - β / 2 -
    gaussianDecaySum r (fun i ↦ gaussianDecayDeriv (r i) (gaussianDecayDeriv (r i) (P i))) x

/-- The real residual is differentiable with the explicit first derivative. -/
public theorem gaussian_mid_residual_deriv {m : ℕ} (s b β : ℝ) (r : Fin m → ℝ)
    (P : Fin m → Polynomial ℝ) (x : ℝ) :
    HasDerivAt (gaussianMidResidual s b β r P) (gaussianMidResidualDeriv s β r P x) x := by
  have he := ((hasDerivAt_id x).div_const (2 : ℝ)).exp.const_mul s
  have hq := ((hasDerivAt_id x).pow 2).const_mul (β / 4)
  have h := (((he.add_const b).sub hq).sub (gaussian_decay_sum_deriv r P x))
  convert h using 1
  · rfl
  · simp only [gaussianMidResidualDeriv, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

/-- Differentiating the first derivative yields the signed curvature formula. -/
public theorem gaussian_mid_residual_curv {m : ℕ} (s β : ℝ) (r : Fin m → ℝ)
    (P : Fin m → Polynomial ℝ) (x : ℝ) :
    HasDerivAt (gaussianMidResidualDeriv s β r P) (gaussianMidResidualCurv s β r P x) x := by
  have he := ((hasDerivAt_id x).div_const (2 : ℝ)).exp.const_mul (s / 2)
  have hq := (hasDerivAt_id x).const_mul (β / 2)
  have h := (he.sub hq).sub (gaussian_decay_sum_deriv r (fun i ↦ gaussianDecayDeriv (r i) (P i)) x)
  convert h using 1
  · rfl
  · simp only [gaussianMidResidualCurv, id_eq, mul_one]
    ring

/-- The explicit second derivative of the polynomial part of a weighted term. -/
public theorem gaussian_decay_deriv_twice (r : ℝ) (P : Polynomial ℝ) :
    gaussianDecayDeriv r (gaussianDecayDeriv r P) =
      P.derivative.derivative - Polynomial.C (2 * r) * P.derivative + Polynomial.C (r ^ 2) * P := by
  simp only [gaussianDecayDeriv, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, Polynomial.C_mul, Polynomial.C_ofNat,
    Polynomial.C_pow]
  ring

/-- A nonpositive conductor slope and nonnegative quadratic coefficient
allow both curvature contributions to be dropped. -/
public theorem gaussian_mid_curv_le_decay {m : ℕ} {s β : ℝ} (hs : s ≤ 0) (hβ : 0 ≤ β)
    (r : Fin m → ℝ) (P : Fin m → Polynomial ℝ) (x : ℝ) :
    gaussianMidResidualCurv s β r P x ≤
      -gaussianDecaySum r (fun i ↦ gaussianDecayDeriv (r i) (gaussianDecayDeriv (r i) (P i)))
          x := by
  have h :=
    mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg hs (by norm_num only : (0 : ℝ) ≤ 4)) (Real.exp_pos (x / 2)).le
  dsimp only [gaussianMidResidualCurv]
  linarith only [h, hβ]

/-- For the explicit residual, a cell only needs numerical endpoint
bounds and an upper bound for the signed curvature. -/
public theorem gaussian_mid_cell_bounds {m : ℕ} (c : GaussianResidualCell) (s b β : ℝ)
    (r : Fin m → ℝ) (P : Fin m → Polynomial ℝ)
    (hl : (c.lowerLeft : ℝ) ≤ gaussianMidResidual s b β r P c.left)
    (hr : (c.lowerRight : ℝ) ≤ gaussianMidResidual s b β r P c.right)
    (hc :
      ∀ x ∈ Set.Ioo (c.left : ℝ) (c.right : ℝ),
        gaussianMidResidualCurv s β r P x ≤ (c.upperCurvature : ℝ)) :
    c.AnalyticBounds (gaussianMidResidual s b β r P) (gaussianMidResidualDeriv s β r P)
      (gaussianMidResidualCurv s β r P) := by
  exact
    ⟨fun x _ ↦ (gaussian_mid_residual_deriv s b β r P x).continuousAt.continuousWithinAt, fun x _ ↦
      gaussian_mid_residual_deriv s b β r P x, fun x _ ↦ gaussian_mid_residual_curv s β r P x, hc,
      hl, hr⟩

/-- The sum of absolute translated coefficients, weighted by powers of the cell width. -/
@[expose]
public noncomputable def gaussianShiftedAbsSum (Q : Polynomial ℝ) (a b : ℝ) : ℝ :=
  let P := Q.comp (Polynomial.X + Polynomial.C a)
  ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| * (b - a) ^ j

/-- Bound a polynomial on a closed cell by the absolute coefficient sum
after translating the origin to the cell's left endpoint. -/
private theorem shifted_abs_poly_le (Q : Polynomial ℝ) {a b t : ℝ} (ht : t ∈ Set.Icc a b) :
    |Q.eval t| ≤ gaussianShiftedAbsSum Q a b := by
  let P := Q.comp (Polynomial.X + Polynomial.C a)
  change |Q.eval t| ≤ ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| * (b - a) ^ j
  have he : P.eval (t - a) = Q.eval t := by
    simp only [P, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      sub_add_cancel]
  rw [← he, Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.1) j)]
  exact
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr ht.1) (sub_le_sub_right ht.2 _) j)
      (abs_nonneg _)

/-- Bound the signed contribution of one decay term by an exponential cap
at the left endpoint and an absolute bound for the translated polynomial. -/
private theorem neg_decay_le_cell (Q : Polynomial ℝ) {r o a b x E B : ℝ} (hr : 0 ≤ r) (ho : o ≤ a)
    (hx : x ∈ Set.Icc a b) (hE : Real.exp (-r * a) ≤ E) (hB : gaussianShiftedAbsSum Q o b ≤ B) :
    -(Real.exp (-r * x) * Q.eval x) ≤ E * B := by
  have he := (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx.1 (neg_nonpos.mpr hr))).trans hE
  have hp := (shifted_abs_poly_le Q ⟨ho.trans hx.1, hx.2⟩).trans hB
  calc
    _ = Real.exp (-r * x) * (-Q.eval x) := (mul_neg _ _).symm
    _ ≤ Real.exp (-r * x) * |Q.eval x| :=
      mul_le_mul_of_nonneg_left (neg_le_abs _) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul he hp (abs_nonneg _) ((Real.exp_pos _).le.trans he)

/-- The signed middle curvature is bounded by a sum of independent
left-endpoint exponential caps and polynomial caps about a shared origin. -/
public theorem gaussian_mid_curvature_le {m : ℕ} {s β o a b x : ℝ} (hs : s ≤ 0) (hβ : 0 ≤ β)
    (r : Fin m → ℝ) (P : Fin m → Polynomial ℝ) (E B : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (ho : o ≤ a)
    (hx : x ∈ Set.Icc a b) (hE : ∀ i, Real.exp (-r i * a) ≤ E i)
    (hB :
      ∀ i,
        gaussianShiftedAbsSum (gaussianDecayDeriv (r i) (gaussianDecayDeriv (r i) (P i))) o b ≤
          B i) :
    gaussianMidResidualCurv s β r P x ≤ ∑ i, E i * B i := by
  refine (gaussian_mid_curv_le_decay hs hβ r P x).trans ?_
  rw [gaussianDecaySum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun i _ ↦ neg_decay_le_cell _ (hr i) ho hx (hE i) (hB i)

/-- At an endpoint use the lower exponential bound for a negative
polynomial upper bound and the upper exponential bound for a nonnegative one. -/
public theorem gaussian_mid_endpoint_ge {m : ℕ} {s b β x Y : ℝ} (hs : s ≤ 0) (r : Fin m → ℝ)
    (P : Fin m → Polynomial ℝ) (lo hi U : Fin m → ℝ) (hY : Real.exp (x / 2) ≤ Y)
    (hlo : ∀ i, lo i ≤ Real.exp (-r i * x)) (hhi : ∀ i, Real.exp (-r i * x) ≤ hi i)
    (hU : ∀ i, (P i).eval x ≤ U i) :
    s * Y + b - (β / 4) * x ^ 2 - (∑ i, U i * (if 0 ≤ U i then hi i else lo i)) ≤
      gaussianMidResidual s b β r P x := by
  have hmain := mul_le_mul_of_nonpos_left hY hs
  have hcost : gaussianDecaySum r P x ≤ ∑ i, U i * (if 0 ≤ U i then hi i else lo i) := by
    unfold gaussianDecaySum
    apply Finset.sum_le_sum
    intro i _
    have hu := mul_le_mul_of_nonneg_left (hU i) (Real.exp_pos (-r i * x)).le
    refine hu.trans ?_
    by_cases h : 0 ≤ U i
    · rw [ite_eq_left h, mul_comm (U i)]
      exact mul_le_mul_of_nonneg_right (hhi i) h
    · rw [ite_eq_right h, mul_comm (U i)]
      exact mul_le_mul_of_nonpos_right (hlo i) (le_of_not_ge h)
  dsimp only [gaussianMidResidual]
  linarith only [hmain, hcost]

end PseudoPrime.PrimeTestBounds.MillerRabin
