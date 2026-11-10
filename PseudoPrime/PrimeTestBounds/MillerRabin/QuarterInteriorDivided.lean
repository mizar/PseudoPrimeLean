/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorComparison

/-! # Divided interior subgroup comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, absence of a rejecting prime gives the joint finite principal
sum an upper bound in terms of the common logarithmic scale and principal costs
divided by the subgroup index. Bound the conductor sum and discard a
nonpositive Gamma correction. -/
theorem quarter_interior_divided {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a X T : ℝ}
    (ha : 0 < a) (hX : 1 ≤ X) (hbound : Real.log X ≤ 2 * a) (hT : 0 ≤ T) (hscale : Real.log n ≤ T)
    (hgamma : -6 * a + (3 / 2 : ℝ) * Real.log X + 18 ≤ 0)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    let H := PrimeTest.fermatSubgroup n
    (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) X m).re) +
        2 * (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 m).re) ≤
      (4 * a - Real.log X) * T +
        ((∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X m).re +
            (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X⁻¹ m).re +
            2 * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re) /
          H.index := by
  let H := PrimeTest.fermatSubgroup n
  have hcard : 1 ≤ H.index := by
    rw [← NumberTheory.card_subgroupAnnihilator H]
    exact Fintype.card_pos
  have hindex : (1 : ℝ) ≤ H.index := by exact_mod_cast hcard
  have hpos : (0 : ℝ) < H.index := by linarith only [hindex]
  have hcond := LLS.PaperStatements.subgroupConductorLogSum_le H
  have hmul := mul_le_mul_of_nonneg_left hscale (sub_nonneg.mpr hindex)
  have hcost : LLS.PaperStatements.subgroupConductorLogSum H ≤ ((H.index : ℝ) - 1) * T :=
    hcond.trans hmul
  have hcoef : 0 ≤ 4 * a - Real.log X := by linarith only [ha, hbound]
  have hc := mul_le_mul_of_nonneg_left hcost hcoef
  have hg := mul_nonpos_of_nonpos_of_nonneg hgamma (sub_nonneg.mpr hindex)
  have hct := mul_nonneg hcoef hT
  have hmain := quarter_interior_comparison hn ho ha hX hbound hGRH hnone
  let K := LLS.PaperStatements.triangularMellinKernel ha
  let Q :=
    (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) X m).re) +
      2 * (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 m).re)
  let S :=
    (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X m).re +
      (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X⁻¹ m).re +
      2 * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re
  change
    (H.index : ℝ) * Q ≤
      S + (4 * a - Real.log X) * LLS.PaperStatements.subgroupConductorLogSum H +
        (-6 * a + (3 / 2 : ℝ) * Real.log X + 18) * ((H.index : ℝ) - 1) at hmain
  change Q ≤ (4 * a - Real.log X) * T + S / (H.index : ℝ)
  have hb : (Q - (4 * a - Real.log X) * T) * (H.index : ℝ) ≤ S := by
    nlinarith only [hmain, hc, hg, hct]
  have hd := (le_div_iff₀ hpos).2 hb
  linarith only [hd]

end PseudoPrime.PrimeTestBounds.MillerRabin
