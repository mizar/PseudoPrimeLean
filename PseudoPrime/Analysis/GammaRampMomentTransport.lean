/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteRampRows
public import PseudoPrime.Analysis.GammaSignedRampCellBounds

/-! # Transporting finite ramp certificates by their first moments -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For u at most v, the exponential part of the ramp can be transported
exactly while its relative linear factor increases. Check the joined branches.
This preserves more growth than plain monotonicity of the ramp weight. -/
theorem gamma_ramp_exp_transport {u v : ℝ} (huv : u ≤ v) :
    exponentialRampWeight v * Real.exp (v - u) ≤ exponentialRampWeight u := by
  have he : Real.exp (-v) * Real.exp (v - u) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  by_cases hv : v ≤ 247 / 100
  · rw [exponentialRampWeight_eq_exp_of_le_left hv,
      exponentialRampWeight_eq_exp_of_le_left (huv.trans hv), he]
  by_cases hu : u ≤ 247 / 100
  · rw [exponentialRampWeight_eq_exp_of_le_left hu]
    exact
      (mul_le_mul_of_nonneg_right (exponentialRampWeight_bounds v).2
            (Real.exp_pos (v - u)).le).trans
        he.le
  by_cases hvr : v ≤ 99 / 40
  · rw [exponentialRampWeight_eq_middle (le_of_not_ge hv) hvr,
      exponentialRampWeight_eq_middle (le_of_not_ge hu) (huv.trans hvr)]
    calc
      Real.exp (-v) * (99 / 40 - v) / (1 / 200) * Real.exp (v - u) =
          (Real.exp (-v) * Real.exp (v - u)) * (99 / 40 - v) / (1 / 200) :=
        by ring
      _ = Real.exp (-u) * (99 / 40 - v) / (1 / 200) := by rw [he]
      _ ≤ Real.exp (-u) * (99 / 40 - u) / (1 / 200) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_sub_left huv (99 / 40)) (Real.exp_pos (-u)).le)
          (by norm_num only)
  · rw [exponentialRampWeight_eq_zero (le_of_not_ge hvr), zero_mul]
    exact (exponentialRampWeight_bounds u).1

/-- The ramp at u dominates the ramp at v times the first exponential
Taylor term when u is at most v. Use exp(t) at least 1+t and ramp nonnegativity.
This supplies the pointwise first-moment improvement. -/
theorem gamma_ramp_linear_transport {u v : ℝ} (huv : u ≤ v) :
    exponentialRampWeight v * (1 + (v - u)) ≤ exponentialRampWeight u := by
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by linarith only [Real.add_one_le_exp (v - u)]
  exact
    (mul_le_mul_of_nonneg_left he (exponentialRampWeight_bounds v).1).trans
      (gamma_ramp_exp_transport huv)

/-- At positive scales b at most x, each ramp atom gains at least
m times the reciprocal-scale difference times its old weight.
Expand the first Taylor term after the pointwise transport inequality. -/
theorem gamma_ramp_scale_atom_transport {b x : ℝ} (hb : 0 < b) (hbx : b ≤ x) (m : ℕ) :
    exponentialRampWeight ((m : ℝ) / b) +
        (1 / b - 1 / x) * ((m : ℝ) * exponentialRampWeight ((m : ℝ) / b)) ≤
      exponentialRampWeight ((m : ℝ) / x) := by
  have h := gamma_ramp_linear_transport (div_le_div₀ (Nat.cast_nonneg m) le_rfl hb hbx)
  calc
    exponentialRampWeight ((m : ℝ) / b) +
          (1 / b - 1 / x) * ((m : ℝ) * exponentialRampWeight ((m : ℝ) / b)) =
        exponentialRampWeight ((m : ℝ) / b) * (1 + ((m : ℝ) / b - (m : ℝ) / x)) :=
      by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ exponentialRampWeight ((m : ℝ) / x) := h

/-- The finite first moment of the actual ramp Mangoldt sum at scale b.
Weight each nonnegative Mangoldt-ramp atom by its natural index.
This moment allows an existing finite certificate to move to larger scales. -/
noncomputable def gammaRampFirstMoment (b : ℝ) : ℝ :=
  ∑ m ∈ Finset.Ioc 0 ⌊b * (99 / 40 : ℝ)⌋₊,
    (m : ℝ) * (ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / b))

/-- Increasing a positive scale transports the full finite ramp sum
by its first moment times the reciprocal-scale difference.
Sum the pointwise gains on the old support and keep the newly admitted
Mangoldt atoms as nonnegative terms. No fresh prime or transcendental data is needed. -/
theorem gamma_ramp_sum_first_moment_transport {b x : ℝ} (hb : 0 < b) (hbx : b ≤ x) :
    AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum b +
        (1 / b - 1 / x) * gammaRampFirstMoment b ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x := by
  have hs :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b * (99 / 40 : ℝ)⌋₊)
      (fun m hm ↦
        mul_le_mul_of_nonneg_left (gamma_ramp_scale_atom_transport hb hbx m)
          (ArithmeticFunction.vonMangoldt_nonneg (n := m)))
  have hsub : Finset.Ioc 0 ⌊b * (99 / 40 : ℝ)⌋₊ ⊆ Finset.Ioc 0 ⌊x * (99 / 40 : ℝ)⌋₊ :=
    Finset.Ioc_subset_Ioc le_rfl
      (Nat.floor_mono (mul_le_mul_of_nonneg_right hbx (by norm_num only : (0 : ℝ) ≤ 99 / 40)))
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ ↦
        mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
          (exponentialRampWeight_bounds ((m : ℝ) / x)).1)
  have he :
    (∑ m ∈ Finset.Ioc 0 ⌊b * (99 / 40 : ℝ)⌋₊,
          ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / b)) +
        (1 / b - 1 / x) * gammaRampFirstMoment b =
      ∑ m ∈ Finset.Ioc 0 ⌊b * (99 / 40 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt m *
          (exponentialRampWeight ((m : ℝ) / b) +
            (1 / b - 1 / x) * ((m : ℝ) * exponentialRampWeight ((m : ℝ) / b))) := by
    dsimp only [gammaRampFirstMoment]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  exact he.le.trans (hs.trans ht)

/-- An actual ramp lower allowance c on (lo,hi] gives first-moment
allowance (lo+1)c on that same block. All indices are at least lo+1
and every Mangoldt-ramp atom is nonnegative. This reuses certified block sums. -/
theorem gamma_ramp_interval_moment_lower {lo hi : ℕ} {b : ℝ} {c : ℚ}
    (hc :
      (c : ℝ) ≤
        ∑ m ∈ Finset.Ioc lo hi,
          ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / b)) :
    (((lo + 1 : ℕ) : ℝ) * (c : ℝ)) ≤
      ∑ m ∈ Finset.Ioc lo hi,
        (m : ℝ) * (ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / b)) := by
  have hs :=
    Finset.sum_le_sum (s := Finset.Ioc lo hi)
      (fun m hm ↦
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_Ioc.mp hm).1))
          (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
            (exponentialRampWeight_bounds ((m : ℝ) / b)).1))
  apply (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (lo + 1))).trans
  rw [Finset.mul_sum]
  exact hs

/-- Lower first-moment allowances on adjacent natural intervals add.
Split the disjoint index intervals and preserve the two rational casts.
This composes reused block certificates without evaluating any new ramp weights. -/
theorem gamma_ramp_moment_interval_lower_add {lo mid hi : ℕ} {b c d : ℚ} (hl : lo ≤ mid)
    (hh : mid ≤ hi)
    (hc :
      (c : ℝ) ≤
        ∑ m ∈ Finset.Ioc lo mid,
          (m : ℝ) * (ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ))))
    (hd :
      (d : ℝ) ≤
        ∑ m ∈ Finset.Ioc mid hi,
          (m : ℝ) *
            (ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ)))) :
    ((c + d : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc lo hi,
        (m : ℝ) *
          (ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ))) := by
  have hdis : Disjoint (Finset.Ioc lo mid) (Finset.Ioc mid hi) := by
    apply Finset.disjoint_left.mpr
    intro m hm hn
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp hn).1
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hl hh, Finset.sum_union hdis, Rat.cast_add]
  exact add_le_add hc hd

/-- A first-moment lower certificate on a prefix below the actual cutoff
also bounds the full ramp first moment. The omitted terms are nonnegative.
This connects a short balanced certificate to the transport theorem. -/
theorem gamma_ramp_prefix_moment_lower_actual {b q : ℚ} {N : ℕ} (hN : N ≤ ⌊(b : ℝ) * (99 / 40)⌋₊)
    (hc :
      (q : ℝ) ≤
        ∑ m ∈ Finset.Ioc 0 N,
          (m : ℝ) *
            (ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ)))) :
    (q : ℝ) ≤ gammaRampFirstMoment b := by
  apply hc.trans
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl hN)
      (fun m _ _ ↦
        mul_nonneg (Nat.cast_nonneg m)
          (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
            (exponentialRampWeight_bounds ((m : ℝ) / (b : ℝ))).1))

/-- Certified lower values for a ramp sum and its first moment transfer
to every larger positive scale. The reciprocal-scale coefficient is nonnegative.
This consumes numerical certificates without requiring a new prime-power scan. -/
theorem gamma_ramp_transport_of_lower_bounds {b x r q : ℝ} (hb : 0 < b) (hbx : b ≤ x)
    (hr : r ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum b)
    (hq : q ≤ gammaRampFirstMoment b) :
    r + (1 / b - 1 / x) * q ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x := by
  have hd : 0 ≤ 1 / b - 1 / x :=
    sub_nonneg.mpr (div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 1) le_rfl hb hbx)
  exact
    (add_le_add hr (mul_le_mul_of_nonneg_left hq hd)).trans
      (gamma_ramp_sum_first_moment_transport hb hbx)

end PseudoPrime.Analysis
