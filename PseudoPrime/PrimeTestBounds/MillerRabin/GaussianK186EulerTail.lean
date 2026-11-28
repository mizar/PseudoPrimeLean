/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianEulerPolyRH
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassRational
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighZeroUpper
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleCharacters
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighEulerSign
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Tactic.Linarith

/-! # Evaluation of the K186 Euler tail -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real polynomial in the inverse Fourier mass profile for K186. -/
@[expose]
public noncomputable def k186MassPoly : Polynomial ℝ :=
  (highGaussianMassPolynomial .k186).map (Rat.castHom ℝ)

/-- The scalar H18 bound for one quarter of the unknown K186 Euler tail. -/
@[expose]
public noncomputable def k186TailCost (X : ℝ) : ℝ :=
  let z := Real.log X
  let Q := Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * k186MassPoly - k186MassPoly.derivative)
  X ^ (-(9 / 4 : ℝ)) * eulerPolyMoment k186MassPoly z (9 / 4) +
    X ^ (-(11 / 4 : ℝ)) * (z ^ 2 * k186MassPoly.eval z + eulerPolyMoment Q z (11 / 4)) / 24

/-- Logarithmic cutoffs of at least 30 fall in the Lee–Nosal range. -/
private theorem k186_cutoff_ge {X : ℝ} (hX : 0 < X) (hl : 30 ≤ Real.log X) : 101 ≤ X := by
  have h := Real.add_one_le_exp (15 : ℝ)
  have hm : (101 : ℝ) ≤ Real.exp 15 * Real.exp 15 :=
    calc
      _ ≤ (15 + 1) * (15 + 1) := by norm_num only
      _ ≤ _ := mul_le_mul h h (by norm_num only) (Real.exp_pos _).le
  rw [← Real.exp_add, show (15 : ℝ) + 15 = 30 by norm_num only] at hm
  exact hm.trans ((Real.le_log_iff_exp_le hX).mp hl)

/-- The three pair characters give a trace deficit in the interval `[0, 4]`. -/
private theorem pair_deficit_mem {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (m : ℕ) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    3 - ((a m).re + (b m).re + (c m).re) ∈ Set.Icc (0 : ℝ) 4 := by
  intro a b c
  have ha := (Complex.re_le_norm (a m)).trans (a.norm_le_one _)
  have hb := (Complex.re_le_norm (b m)).trans (b.norm_le_one _)
  have hc := (Complex.re_le_norm (c m)).trans (c.norm_le_one _)
  have ht : -1 ≤ (a m).re + (b m).re + (c m).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (m : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  exact ⟨by linarith only [ha, hb, hc], by linarith only [ht]⟩

/-- Map the two rational mass polynomials to the real polynomials used by H18. -/
private theorem k186_mass_real_signs {z : ℝ}
    (h :
      let P := highGaussianMassPolynomial .k186
      0 ≤ P.eval₂ (Rat.castHom ℝ) z ∧
        0 ≤ (Polynomial.C (13 / 4) * P - P.derivative).eval₂ (Rat.castHom ℝ) z) :
    0 ≤ k186MassPoly.eval z ∧
      0 ≤ (Polynomial.C (13 / 4) * k186MassPoly - k186MassPoly.derivative).eval z := by
  let P := highGaussianMassPolynomial .k186
  have hmap :
    (Polynomial.C (13 / 4 : ℚ) * P - P.derivative).map (Rat.castHom ℝ) =
      Polynomial.C (13 / 4) * k186MassPoly - k186MassPoly.derivative := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.derivative_map,
      Rat.coe_castHom, Rat.cast_div, Rat.cast_ofNat, P, k186MassPoly]
  constructor
  · simpa only [k186MassPoly, Polynomial.eval_map] using h.1
  · rw [← hmap, Polynomial.eval_map]
    exact h.2

/-- H18 bounds the K186 signed Euler tail on the logarithmic half-line starting at 30.
Both mass polynomials have nonnegative coefficients after translation by 30. -/
public theorem k186_euler_tail_rh {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (hl : 30 ≤ Real.log X) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    (∑' m : { m : ℕ // ⌊X⌋₊ < m },
        ArithmeticFunction.vonMangoldt m.val * (3 - ((a m.val).re + (b m.val).re + (c m.val).re)) *
          (m.val : ℝ) ^ (-(HighGaussianKernel.k186.pole : ℝ) - 1 / 2) *
          (highGaussianMassPolynomial .k186).eval₂ (Rat.castHom ℝ) (Real.log m.val)) ≤
      4 * k186TailCost X := by
  intro a b c
  have hs : (2 : ℝ) < 13 / 4 := by norm_num only
  have h₁ : 1 ≤ Real.log X := (by norm_num only : (1 : ℝ) ≤ 30).trans hl
  have h :=
    euler_trace_tail_rh k186MassPoly hs hRH (k186_cutoff_ge hX hl) h₁
      (fun z hz ↦ (k186_mass_real_signs (k186_mass_poly_signs (hl.trans hz))).1)
      (fun z hz ↦ (k186_mass_real_signs (k186_mass_poly_signs (hl.trans hz))).2)
      (fun m ↦ 3 - ((a m).re + (b m).re + (c m).re)) (pair_deficit_mem hp hq hr)
  have he : -(HighGaussianKernel.k186.pole : ℝ) - 1 / 2 = -(13 / 4 : ℝ) := by
    norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  have hd : (13 / 4 : ℝ) - 1 = 9 / 4 := by norm_num only
  have hh : (13 / 4 : ℝ) - 1 / 2 = 11 / 4 := by norm_num only
  simp only [hd, hh, k186MassPoly, Polynomial.eval_map, mul_assoc] at h
  simp only [he, k186TailCost, k186MassPoly, Polynomial.eval_map, mul_assoc]
  simpa only [mul_left_comm] using h

/-- For a passing uniform triple, the K186 zero upper bound retains the H18 tail
charge and uses the rational lower bound for its pole mass. -/
public theorem k186_zero_upper {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ}
    (hX : 0 < X) (hl : 30 ≤ Real.log X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr);
    -(∑' ρ : ℂ, HighGaussianKernel.k186.zeroTerm a X ρ).re -
        (∑' ρ : ℂ, HighGaussianKernel.k186.zeroTerm b X ρ).re -
        (∑' ρ : ℂ, HighGaussianKernel.k186.zeroTerm c X ρ).re ≤
      3 / 8 * Real.log n - 94173 / 1250 + 3 * HighGaussianKernel.k186.xiMass.re +
        4 * k186TailCost X := by
  intro a b c
  have h := high_gaussian_zero_upper_of_pass .k186 hn ho hu hprod hp hq hr hg hX hpass
  have ht := k186_euler_tail_rh hp hq hr hg.riemann hX hl
  have hw : ((125564 / 10000 : ℚ) : ℝ) < (HighGaussianKernel.k186.massPole : ℝ) :=
    Rat.cast_lt.mpr gaussian_k186_mass_pole_bounds.1
  simp only [Rat.cast_div, Rat.cast_ofNat] at hw
  dsimp only at h ht
  linarith only [h, ht, hw]

/-- The polynomial in the cutoff logarithm for a fixed Euler moment rate. -/
public noncomputable def eulerMomentPoly (P : Polynomial ℝ) (s : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    Polynomial.hasseDeriv k P * Polynomial.C ((k.factorial : ℝ) / s ^ (k + 1))

/-- Evaluating the Euler moment polynomial gives the finite translated moment. -/
public theorem euler_moment_poly_eval (P : Polynomial ℝ) (s z : ℝ) :
    (eulerMomentPoly P s).eval z = eulerPolyMoment P z s := by
  simp only [eulerMomentPoly, eulerPolyMoment, ← Polynomial.taylor_apply,
    Polynomial.natDegree_taylor, Polynomial.taylor_coeff, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]

/-- Each negative power of the Euler cutoff dominates a polynomial in its logarithm. -/
private theorem k186_poly_decay (P : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun X : ℝ ↦ X ^ (-b) * P.eval (Real.log X)) Filter.atTop (nhds 0) := by
  let Q := P.comp (Polynomial.C b⁻¹ * Polynomial.X)
  have h := Q.tendsto_div_exp_atTop.comp (Real.tendsto_log_atTop.const_mul_atTop hb)
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
  have he : b⁻¹ * (b * Real.log X) = Real.log X := by
    rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
  simp only [Function.comp_apply, Q, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, he, Real.rpow_def_of_pos hX]
  rw [mul_neg, Real.exp_neg, div_eq_mul_inv, mul_comm b]
  exact mul_comm _ _

/-- At sufficiently large cutoffs, the existing RH Euler-tail formula for
K186 tends to zero. The conclusion uses no numerical coefficient checks. -/
public theorem k186_tail_cost_tendsto : Filter.Tendsto k186TailCost Filter.atTop (nhds 0) := by
  let P := k186MassPoly
  let Q := Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * P - P.derivative)
  let U := eulerMomentPoly P (9 / 4)
  let V := eulerMomentPoly Q (11 / 4)
  have hU (z : ℝ) : eulerPolyMoment P z (9 / 4) = U.eval z := (euler_moment_poly_eval P _ z).symm
  have hV (z : ℝ) : eulerPolyMoment Q z (11 / 4) = V.eval z := (euler_moment_poly_eval Q _ z).symm
  have h₁ := k186_poly_decay U (by norm_num only : (0 : ℝ) < 9 / 4)
  have h₂ := k186_poly_decay (Polynomial.X ^ 2 * P + V) (by norm_num only : (0 : ℝ) < 11 / 4)
  have h := h₁.add (h₂.div_const (24 : ℝ))
  change
    Filter.Tendsto
      (fun X : ℝ ↦
        X ^ (-(9 / 4 : ℝ)) * eulerPolyMoment P (Real.log X) (9 / 4) +
          X ^ (-(11 / 4 : ℝ)) *
              (Real.log X ^ 2 * P.eval (Real.log X) + eulerPolyMoment Q (Real.log X) (11 / 4)) /
            24)
      Filter.atTop (nhds 0)
  simpa only [hU, hV, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, zero_div, add_zero] using h

/-- At any fixed positive linear scale, the K186 Euler contribution
is smaller than any prescribed positive budget on a half-line. -/
public theorem k186_euler_eventual_budget {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, 4 * k186TailCost ((ρ * L) ^ 2) ≤ ε := by
  have hscale :=
    (Filter.tendsto_pow_atTop (by norm_num only : (2 : ℕ) ≠ 0)).comp
      (Filter.tendsto_id.const_mul_atTop hρ)
  have h := (k186_tail_cost_tendsto.comp hscale).const_mul (4 : ℝ)
  have h' : Filter.Tendsto (fun L : ℝ ↦ 4 * k186TailCost ((ρ * L) ^ 2)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, id_eq, mul_zero] using h
  exact Filter.eventually_atTop.mp (h'.eventually_le_const hε)

/-- Once the entrance height times the exponential rate is at least the
exponent, an exponentially weighted monomial is bounded by its entrance value. -/
private theorem exp_monomial_le_anchor {b z₀ z : ℝ} {i : ℕ} (h₀ : 0 < z₀) (hz : z₀ ≤ z)
    (hi : (i : ℝ) ≤ b * z₀) : Real.exp (-b * z) * z ^ i ≤ Real.exp (-b * z₀) * z₀ ^ i := by
  have hq := div_pos (h₀.trans_le hz) h₀
  have hl := Real.log_le_sub_one_of_pos hq
  rw [← div_self h₀.ne', ← sub_div] at hl
  have hmul := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg i)
  have hi' : (i : ℝ) / z₀ ≤ b := (div_le_iff₀ h₀).mpr hi
  have h : (i : ℝ) * Real.log (z / z₀) ≤ b * (z - z₀) := by
    refine hmul.trans ?_
    rw [← mul_div_assoc, mul_comm (i : ℝ), mul_div_assoc, mul_comm b]
    exact mul_le_mul_of_nonneg_left hi' (sub_nonneg.mpr hz)
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_natCast_mul, Real.exp_log hq, div_pow] at he
  have hp := (div_le_iff₀ (pow_pos h₀ i)).mp he
  calc
    _ ≤ Real.exp (-b * z) * (Real.exp (b * (z - z₀)) * z₀ ^ i) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- One entrance evaluation of the absolute coefficients bounds an
exponentially weighted polynomial throughout the far half-line. -/
public theorem exp_poly_abs_le_anchor (P : Polynomial ℝ) {b z₀ z : ℝ} (h₀ : 0 < z₀) (hz : z₀ ≤ z)
    (hd : (P.natDegree : ℝ) ≤ b * z₀) :
    Real.exp (-b * z) * |P.eval z| ≤
      Real.exp (-b * z₀) * ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * z₀ ^ i := by
  have ha : |P.eval z| ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * z ^ i := by
    rw [Polynomial.eval_eq_sum_range]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul, abs_of_nonneg (pow_nonneg (h₀.trans_le hz).le i)]
  refine (mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : (i : ℝ) ≤ b * z₀ :=
    (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).trans hd
  calc
    _ = |P.coeff i| * (Real.exp (-b * z) * z ^ i) := by ring
    _ ≤ |P.coeff i| * (Real.exp (-b * z₀) * z₀ ^ i) :=
      mul_le_mul_of_nonneg_left (exp_monomial_le_anchor h₀ hz hi') (abs_nonneg _)
    _ = _ := by ring

/-- The two Euler-tail polynomials are evaluated at log X, with
exponential rates 9/4 and 11/4 respectively. -/
public noncomputable def k186EulerSecondPoly : Polynomial ℝ :=
  Polynomial.X ^ 2 * k186MassPoly +
    eulerMomentPoly
      (Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * k186MassPoly - k186MassPoly.derivative)) (11 / 4)

/-- The absolute-coefficient evaluation gives a single endpoint majorant. -/
public noncomputable def eulerExpPolyAnchor (P : Polynomial ℝ) (b z : ℝ) : ℝ :=
  Real.exp (-b * z) * ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * z ^ i

/-- Apply the entrance bound after writing the negative power as an exponential. -/
private theorem euler_rpow_poly_bound (P : Polynomial ℝ) {b X z : ℝ} (hX : 0 < X) (hz : 0 < z)
    (hlog : z ≤ Real.log X) (hd : (P.natDegree : ℝ) ≤ b * z) :
    X ^ (-b) * P.eval (Real.log X) ≤ eulerExpPolyAnchor P b z := by
  rw [Real.rpow_def_of_pos hX, mul_comm (Real.log X)]
  exact
    (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le).trans
      (exp_poly_abs_le_anchor P hz hlog hd)

/-- A single entrance evaluation for each polynomial bounds the K186 Euler
tail at every positive cutoff with logarithm beyond that entrance. -/
public theorem k186_euler_le_anchor {X z : ℝ} (hX : 0 < X) (hz : 0 < z) (hlog : z ≤ Real.log X)
    (h₁ : ((eulerMomentPoly k186MassPoly (9 / 4)).natDegree : ℝ) ≤ (9 / 4) * z)
    (h₂ : (k186EulerSecondPoly.natDegree : ℝ) ≤ (11 / 4) * z) :
    k186TailCost X ≤
      eulerExpPolyAnchor (eulerMomentPoly k186MassPoly (9 / 4)) (9 / 4) z +
        eulerExpPolyAnchor k186EulerSecondPoly (11 / 4) z / 24 := by
  have ha := euler_rpow_poly_bound _ hX hz hlog h₁
  have hb := euler_rpow_poly_bound _ hX hz hlog h₂
  simpa only [euler_moment_poly_eval, k186EulerSecondPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, k186TailCost] using
    (add_le_add ha (div_le_div_of_nonneg_right hb (by norm_num only : (0 : ℝ) ≤ 24)))

/-- The reciprocal of a single positive Taylor term bounds the negative exponential. -/
private theorem exp_neg_le_single_term {y : ℝ} (hy : 0 < y) (k : ℕ) :
    Real.exp (-y) ≤ (k.factorial : ℝ) / y ^ k := by
  have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  rw [Real.exp_neg, ← inv_div]
  exact
    (inv_le_inv₀ (Real.exp_pos y) (div_pos (pow_pos hy k) hf)).mpr
      (Real.pow_div_factorial_le_exp y hy.le k)

/-- Taking the Euler moment does not raise the degree of the input polynomial. -/
private theorem euler_moment_degree (P : Polynomial ℝ) (s : ℝ) :
    (eulerMomentPoly P s).natDegree ≤ P.natDegree := by
  unfold eulerMomentPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_hasseDeriv_le _ _).trans (Nat.sub_le _ _))

/-- The K186 rational mass has degree at most 41, also after casting to the reals. -/
private theorem k186_mass_degree : k186MassPoly.natDegree ≤ 41 := by
  have h := high_mass_shifted_degree .k186 0
  simp only [Polynomial.C_0, add_zero, Polynomial.comp_X, HighGaussianKernel.degree] at h
  exact Polynomial.natDegree_map_le.trans h

/-- The two K186 Euler polynomials have degrees at most 41 and 43. -/
private theorem k186_euler_degrees :
    (eulerMomentPoly k186MassPoly (9 / 4)).natDegree ≤ 41 ∧ k186EulerSecondPoly.natDegree ≤ 43 := by
  let P := k186MassPoly
  have hp : P.natDegree ≤ 41 := k186_mass_degree
  have hd := (Polynomial.natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hp)
  have hq :=
    Polynomial.natDegree_sub_le_of_le ((Polynomial.natDegree_C_mul_le (13 / 4 : ℝ) P).trans hp) hd
  refine ⟨(euler_moment_degree P _).trans hp, ?_⟩
  unfold k186EulerSecondPoly
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_X_pow_le 2) hp
  · exact
      (euler_moment_degree _ _).trans
        (Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_X_pow_le 2)
          (hq.trans (max_le le_rfl le_rfl)))

/-- A fixed-size table may pad the absolute coefficient sum with zero coefficients. -/
private theorem euler_coeff_sum_extend (P : Polynomial ℝ) (z : ℝ) {N : ℕ} (hd : P.natDegree < N) :
    (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * z ^ i) =
      ∑ i ∈ Finset.range N, |P.coeff i| * z ^ i := by
  apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_of_lt hd))
  intro i _ hi
  have hid : P.natDegree < i :=
    Nat.lt_of_succ_le (Nat.le_of_not_lt fun h ↦ hi (Finset.mem_range.mpr h))
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hid, abs_zero, zero_mul]

/-- For the K186 Euler tail at log cutoff at least 50, two coarse absolute
coefficient bounds suffice for a budget of one. Only one Taylor term per rate is used. -/
public theorem k186_euler_budget_at_log50 {X : ℝ} (hX : 0 < X) (hlog : 50 ≤ Real.log X)
    (h₁ :
      (∑ i ∈ Finset.range 42, |(eulerMomentPoly k186MassPoly (9 / 4)).coeff i| * (50 : ℝ) ^ i) ≤
        3 * 10 ^ 45)
    (h₂ : (∑ i ∈ Finset.range 44, |k186EulerSecondPoly.coeff i| * (50 : ℝ) ^ i) ≤ 4 * 10 ^ 49) :
    4 * k186TailCost X ≤ 1 := by
  obtain ⟨hd₁, hd₂⟩ := k186_euler_degrees
  have h₁ := (euler_coeff_sum_extend _ 50 (Nat.lt_succ_of_le hd₁)).trans_le h₁
  have h₂ := (euler_coeff_sum_extend _ 50 (Nat.lt_succ_of_le hd₂)).trans_le h₂
  have ha :=
    k186_euler_le_anchor hX (by norm_num only) hlog ((Nat.cast_le.mpr hd₁).trans (by norm_num only))
      ((Nat.cast_le.mpr hd₂).trans (by norm_num only))
  have hb₁ := exp_neg_le_single_term (show (0 : ℝ) < 9 / 4 * 50 by norm_num only) 96
  have hb₂ := exp_neg_le_single_term (show (0 : ℝ) < 11 / 4 * 50 by norm_num only) 96
  have hc₁ := mul_le_mul h₁ hb₁ (Real.exp_pos _).le (by norm_num only : (0 : ℝ) ≤ 3 * 10 ^ 45)
  have hc₂ := mul_le_mul h₂ hb₂ (Real.exp_pos _).le (by norm_num only : (0 : ℝ) ≤ 4 * 10 ^ 49)
  simp only [eulerExpPolyAnchor, neg_mul] at ha
  rw [mul_comm (Real.exp _), mul_comm (Real.exp _)] at ha
  norm_num only at hc₁ hc₂
  linarith only [ha, hc₁, hc₂]

end PseudoPrime.PrimeTestBounds.MillerRabin
