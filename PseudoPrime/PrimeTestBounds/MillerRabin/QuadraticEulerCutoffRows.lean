/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerSupportSum

/-! # Certified numerical rows below a variable finite cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- All concatenated center rows retain their independently certified checks.
This theorem combines block certificates without repeating root arithmetic. -/
theorem centerRows50000_check : centerRows50000.all eulerCenterRowCheck = true := by
  simp only [centerRows50000, List.all_append, centerRows0_check, centerRows250_check,
    centerRows500_check, centerRows750_check, centerRows1000_check, centerRows1250_check,
    centerRows1500_check, centerRows1750_check, centerRows2000_check, centerRows2250_check,
    centerRows2500_check, centerRows2750_check, centerRows3000_check, centerRows3250_check,
    centerRows3500_check, centerRows3750_check, centerRows4000_check, centerRows4250_check,
    centerRows4500_check, centerRows4750_check, centerRows5000_check, Bool.and_true]

/-- Numerical rows restricted by their prime-power value. The original
cutoff support is exact through 50000; smaller finite sums use this filter. -/
noncomputable def centerRowsBelow (B : ℕ) : List EulerCenterRow :=
  centerRows50000.filter (fun r ↦ r.p ^ (r.k + 1) ≤ B)

/-- Filtering the certified rows preserves every logarithm and root check.
This supplies numerical soundness for each finite Gamma cell prefix. -/
theorem centerRowsBelow_check (B : ℕ) : (centerRowsBelow B).all eulerCenterRowCheck = true := by
  apply List.all_eq_true.mpr
  intro r hr
  exact List.all_eq_true.mp centerRows50000_check r (List.mem_filter.mp hr).1

/-- Below any cutoff at most 50000, the filtered rows give the exact sum
of a real weight supported on prime powers. Restrict the global support
identity by a cutoff indicator and rewrite both filtered sums. -/
theorem centerRowsBelow_sum (f : ℕ → ℝ) (hf : ∀ n, ¬IsPrimePow n → f n = 0) {B : ℕ}
    (hB : B ≤ 50000) :
    (∑ n ∈ Finset.Ioc 0 B, f n) = ((centerRowsBelow B).map (fun r ↦ f (r.p ^ (r.k + 1)))).sum := by
  have hioc : (Finset.Ioc 0 50000).filter (fun n ↦ n ≤ B) = Finset.Ioc 0 B := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp, _⟩, hb⟩
      exact ⟨hp, hb⟩
    · rintro ⟨hp, hb⟩
      exact ⟨⟨hp, hb.trans hB⟩, hb⟩
  have hz : ∀ n, ¬IsPrimePow n → (if n ≤ B then f n else 0) = 0 := by
    intro n hn
    by_cases hb : n ≤ B
    · simp only [hb, ite_true, hf n hn]
    · simp only [hb, ite_false]
  rw [← hioc, Finset.sum_filter, center50000_weight_rows _ hz]
  simp only [centerRowsBelow, List.sum_map_ite, List.map_const', List.sum_replicate, smul_zero,
    add_zero]

/-- A rational lower endpoint sum on the filtered rows bounds the actual
Euler prefix at any cutoff at most 50000. Exact support and inherited row
checks discharge all arithmetic hypotheses of the numerical cell input. -/
theorem centerRowsBelow_euler_lower {B : ℕ} (hB : B ≤ 50000) (L : ℚ)
    (hl :
      L ≤ ((centerRowsBelow B).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum) :
    (L : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 B, Analysis.gammaResolventMangoldtWeight n := by
  have hz : ∀ n, ¬IsPrimePow n → Analysis.gammaResolventMangoldtWeight n = 0 := by
    intro n hn
    rw [Analysis.gammaResolventMangoldtWeight, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn,
      zero_mul]
  rw [centerRowsBelow_sum _ hz hB]
  exact euler_rows_lower_of_rational_sum _ L (centerRowsBelow_check B) hl

end PseudoPrime.PrimeTestBounds.MillerRabin
