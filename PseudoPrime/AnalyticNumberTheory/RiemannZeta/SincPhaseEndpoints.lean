/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinateInterpolation
import PseudoPrime.Analysis.SecondDerivativeInterpolation

/-! # Centered Taylor bounds for phase endpoints -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A centered value and slope enclosure bound the true ordinate contribution throughout
a bracket of radius r. The quadratic remainder uses the lower endpoint of the bracket. -/
theorem ordinateTerm_le_center {v V a c r g U D : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hac : a ≤ c - r)
    (hg : |g - c| ≤ r) (hv : |v| ≤ V) (hu : ordinateTerm v c ≤ U)
    (hd : |ordinateTermFirst v c| ≤ D) :
    ordinateTerm v g ≤ U + r * D + r ^ 2 * (V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3) := by
  let K := V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3
  have hV := (abs_nonneg v).trans hv
  have hk : 0 ≤ K := by
    exact
      add_nonneg
        (add_nonneg (div_nonneg (sq_nonneg _) ha.le)
          (div_nonneg (mul_nonneg (by norm_num only) hV) (sq_nonneg _)))
        (div_nonneg (by norm_num only) (pow_nonneg ha.le 3))
  have hcg : g ∈ Set.Icc (c - r) (c + r) :=
    ⟨by linarith only [(abs_le.mp hg).1], by linarith only [(abs_le.mp hg).2]⟩
  have h :=
    Analysis.le_tangent_add_quadratic (fun t _ ↦ hasDerivAt_ordinateTerm v t)
      (fun t _ ↦ hasDerivAt_ordinateTermFirst v t)
      (fun t ht ↦ (le_abs_self _).trans (abs_ordinateTermSecond_le v t a V ha (hac.trans ht.1) hv))
      (show c ∈ Set.Icc (c - r) (c + r) from ⟨by linarith only [hr], by linarith only [hr]⟩) hcg
  have hlin := mul_le_mul hd hg (abs_nonneg (g - c)) ((abs_nonneg _).trans hd)
  rw [← abs_mul] at hlin
  have hprod := (le_abs_self _).trans hlin
  have hsq := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hg 2) hk
  rw [sq_abs] at hsq
  dsimp only [K] at hsq
  nlinarith only [hu, h, hprod, hsq]

/-- Sum centered Taylor enclosures over the ordinate boxes to bound the true phase
at a logarithmic endpoint. Each center and slope is evaluated only once. -/
theorem phase_le_center_sum {n : ℕ} (g a c U D : Fin n → ℝ) {v V r : ℝ} (hr : 0 ≤ r) (hv : |v| ≤ V)
    (ha : ∀ i, 0 < a i) (hc : ∀ i, a i ≤ c i - r) (hg : ∀ i, |g i - c i| ≤ r)
    (hu : ∀ i, ordinateTerm v (c i) ≤ U i) (hd : ∀ i, |ordinateTermFirst v (c i)| ≤ D i) :
    zeroHeadPhase g v ≤
      ∑ i, (U i + r * D i + r ^ 2 * (V ^ 2 / a i + 2 * V / a i ^ 2 + 2 / a i ^ 3)) := by
  rw [zeroHeadPhase_eq_sum_terms]
  exact Finset.sum_le_sum fun i _ ↦ ordinateTerm_le_center (ha i) hr (hc i) (hg i) hv (hu i) (hd i)

/-- Express the signed ordinate contribution using the sine and cosine of one real phase. -/
theorem ordinateTerm_eq_trig (v g : ℝ) :
    ordinateTerm v g = (Real.cos (g * v) + 2 * g * Real.sin (g * v)) / (1 / 4 + g ^ 2) := by
  have he : Complex.I * (v : ℂ) * (g : ℂ) = ((g * v : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_mul]
    ring
  simp only [ordinateTerm, ordinatePhase, he, Complex.div_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add, add_zero, Complex.normSq_apply,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_one]
  ring_nf

/-- The ordinate derivative uses the same two trigonometric samples as the signed value.
The coefficients are rational at rational phase and ordinate inputs. -/
theorem ordinateTermFirst_eq_trig (v g : ℝ) :
    let d := 1 / 4 + g ^ 2
    ordinateTermFirst v g =
      2 * g * (v / d - 1 / d ^ 2) * Real.cos (g * v) +
        (-v / d + 2 * (1 / 4 - g ^ 2) / d ^ 2) * Real.sin (g * v) := by
  dsimp only
  have hp := (hasDerivAt_id g).mul_const v
  have hn := hp.cos.add (((hasDerivAt_id g).const_mul 2).mul hp.sin)
  have hd := (hasDerivAt_const g (1 / 4 : ℝ)).add ((hasDerivAt_id g).pow 2)
  have hz : 1 / 4 + g ^ 2 ≠ 0 := ne_of_gt (by linarith only [sq_nonneg g])
  have h := (hn.div hd hz).deriv
  have he := (hasDerivAt_ordinateTerm v g).deriv
  rw [funext (ordinateTerm_eq_trig v)] at he
  refine he.symm.trans (h.trans ?_)
  simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, id_eq]
  field_simp [hz]
  ring

/-- Linear combinations use a common pair of component intervals. The larger endpoint
product bounds each term for either sign of its coefficient. -/
private theorem mul_le_max_products {c x l u : ℝ} (hl : l ≤ x) (hu : x ≤ u) :
    c * x ≤ max (c * l) (c * u) := by
  rcases le_total 0 c with h | h
  · exact (mul_le_mul_of_nonneg_left hu h).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hl h).trans (le_max_left _ _)

/-- Two trigonometric enclosures give a signed upper bound for the value and an
absolute bound for the slope at the same center. The latter checks both signs. -/
theorem ordinate_center_bounds {v g l u s t U D : ℝ} (hcos : Real.cos (g * v) ∈ Set.Icc l u)
    (hsin : Real.sin (g * v) ∈ Set.Icc s t)
    (hbudget :
      let d := 1 / 4 + g ^ 2
      let p := 2 * g * (v / d - 1 / d ^ 2)
      let q := -v / d + 2 * (1 / 4 - g ^ 2) / d ^ 2
      let box := fun a b : ℝ ↦ max (a * l) (a * u) + max (b * s) (b * t)
      box (1 / d) (2 * g / d) ≤ U ∧ box p q ≤ D ∧ box (-p) (-q) ≤ D) :
    ordinateTerm v g ≤ U ∧ |ordinateTermFirst v g| ≤ D := by
  have h (a b : ℝ) :=
    add_le_add (mul_le_max_products (c := a) hcos.1 hcos.2)
      (mul_le_max_products (c := b) hsin.1 hsin.2)
  dsimp only at hbudget
  rw [ordinateTerm_eq_trig, ordinateTermFirst_eq_trig]
  constructor
  · have hh := (h (1 / (1 / 4 + g ^ 2)) (2 * g / (1 / 4 + g ^ 2))).trans hbudget.1
    convert hh using 1
    ring
  · apply abs_le.mpr
    constructor
    · have hh := (h _ _).trans hbudget.2.2
      linarith only [hh]
    · exact (h _ _).trans hbudget.2.1

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
