/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelCharacterBounds
public import PseudoPrime.LLS.MellinKernelTruncatedComparison
public import PseudoPrime.Analysis.LogSqrtErrorAbsorption

/-!
# Uniform subgroup kernel comparison

Finite principal-character upper and integral lower bounds imply Proposition 6.1.
The integral allowance absorbs the errors at large scales; bounded scales are controlled
by a larger logarithmic modulus threshold. The estimate covers every positive prime cutoff.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Under GRH, a fixed kernel, subgroup index greater than one, positive cutoff ratio and
positive allowance give a modulus threshold for the scaled kernel comparison at every
positive scale. For large scales combine the finite upper and integral lower bounds,
then absorb the remainders. For bounded scales enlarge the logarithmic modulus threshold.
If the main coefficient is nonpositive, positivity of the right side suffices.
This supplies the uniform-in-cutoff estimate required by Proposition 6.1. -/
private theorem exists_scaled_kernel_comparison
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (K : MellinKernel) {h : ℕ}
    (hh : 1 < h) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∃ Q : ℕ,
      3 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              H.index = h →
                ∀ x : ℝ,
                  0 < x →
                    (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ b * x → residueInSubgroup q H p) →
                    ((h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) -
                          (K.function (1 / 2)).re) *
                        Real.sqrt x ≤
                      (1 + ε) * ((h : ℝ) - 1) * K.mass * Real.log q := by
  let I := ∫ u in 0..b, (K.transform u).re / Real.sqrt u
  let A := (h : ℝ) * I - (K.function (1 / 2)).re
  let B := ((h : ℝ) - 1) * K.mass
  have hhR : (1 : ℝ) < h := by exact_mod_cast hh
  have hhpos : (0 : ℝ) < h := zero_lt_one.trans hhR
  have hB : 0 < B := mul_pos (sub_pos.mpr hhR) (mass_pos K)
  have he : 0 < 1 + ε := by linarith only [hε]
  by_cases hA : 0 < A
  · obtain ⟨Cu, hCu, hu⟩ := exists_principal_sum_le hGRH K
    obtain ⟨Cl, hCl, hl⟩ := exists_eventually_principal_sum_ge_integral K hGRH.riemann
    let C := Cu + Cl
    have hC : 0 < C := add_pos hCu hCl
    obtain ⟨δ, hδ, hcoef⟩ := Analysis.exists_coefficient_allowance hA hhpos hε
    obtain ⟨Qu, hQu, hupper⟩ := hu (ε / 2) (half_pos hε)
    obtain ⟨Tn, hTn, hn⟩ := Analysis.exists_error_absorption_scale hhpos hC hB hε
    obtain ⟨Tl, hTl⟩ := Filter.eventually_atTop.mp (hl hb hδ)
    let T := max Tl Tn
    have hT : 2 ≤ T := hTn.trans (le_max_right _ _)
    have hlog : Filter.Tendsto (fun q : ℕ ↦ Real.log q) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hqev :=
      (hlog.eventually_ge_atTop
            (max (8 * (h : ℝ) * C / (ε * B)) (A * Real.sqrt T / ((1 + ε) * B)))).and
        (Filter.eventually_ge_atTop Qu)
    obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp hqev
    refine ⟨max Q Qu, hQu.trans (le_max_right _ _), ?_⟩
    intro q _ hq H hi x hx hpr
    have hq' := hQ q ((le_max_left Q Qu).trans hq)
    have hL := (le_max_left _ _).trans hq'.1
    have hLs := (le_max_right _ _).trans hq'.1
    have hxbound : A * Real.sqrt x ≤ (1 + ε) * B * Real.log q := by
      by_cases hxT : T ≤ x
      · have hx2 := hT.trans hxT
        have hntop : H ≠ ⊤ := by
          intro heq
          have hidx : h = 1 := by rw [← hi, heq, Subgroup.index_top]
          exact (ne_of_gt hh) hidx
        have hupper' := hupper q hq'.2 H hntop x hx2 (b * x) hpr
        have hlower' := hTl x ((le_max_left Tl Tn).trans hxT) q
        have hlowermul := mul_le_mul_of_nonneg_left hlower' hhpos.le
        rw [hi] at hupper'
        have hClpos := mul_nonneg hhpos.le hCl.le
        have hraw :
          (A - (h : ℝ) * δ) * Real.sqrt x ≤
            (1 + ε / 2) * B * Real.log q +
              (h : ℝ) * C * (1 + Real.log q * Real.log x / Real.sqrt x) := by
          dsimp only [A, B, C, I]
          simp only [mul_div_assoc] at hupper' hlowermul ⊢
          nlinarith only [hupper', hlowermul, hClpos]
        have herr := hn x ((le_max_right Tl Tn).trans hxT) (Real.log q) hL
        have hsmall : (A - (h : ℝ) * δ) * Real.sqrt x ≤ (1 + 3 * ε / 4) * B * Real.log q := by
          linarith only [hraw, herr]
        exact Analysis.coefficient_le_of_allowance hε hcoef hsmall
      · have hxt := le_of_lt (lt_of_not_ge hxT)
        have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxt) hA.le
        have hsmall := (div_le_iff₀ (mul_pos he hB)).mp hLs
        nlinarith only [hroot, hsmall]
    change A * Real.sqrt x ≤ (1 + ε) * ((h : ℝ) - 1) * K.mass * Real.log q
    simpa only [B, mul_assoc] using hxbound
  · refine ⟨3, le_refl _, ?_⟩
    intro q _ hq H hi x hx hpr
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 1 ≤ q)
    have hl : A * Real.sqrt x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hA) (Real.sqrt_nonneg x)
    have hr : 0 ≤ (1 + ε) * B * Real.log q :=
      mul_nonneg (mul_nonneg he.le hB.le) (Real.log_nonneg hqR)
    change A * Real.sqrt x ≤ (1 + ε) * ((h : ℝ) - 1) * K.mass * Real.log q
    simpa only [B, mul_assoc] using hl.trans hr

end PseudoPrime.LLS.PaperStatements.MellinKernel

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Proposition 6.1 holds under GRH for every admissible kernel, fixed subgroup index greater
than one and positive cutoff ratio. Apply the scaled comparison at `x = X / lambda`
and multiply by `sqrt(lambda)`. The modulus threshold covers all positive cutoffs
and all subgroups of the fixed index. This is the input to Sections 6.2 and 6.3. -/
theorem proposition61 : lls_proposition61 := by
  intro hGRH K h hh b hb ε hε
  obtain ⟨Q, hQ, hbound⟩ := exists_scaled_kernel_comparison hGRH K hh hb hε
  refine ⟨Q, ?_⟩
  intro q _ hq H hi X hX hpr
  let x := X / b
  have hx : 0 < x := div_pos hX hb
  have hscale : b * x = X := by
    dsimp only [x]
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hb)]
  have hs := hbound q hq H hi x hx (by simpa only [hscale] using hpr)
  have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg b)
  have hroot : Real.sqrt x * Real.sqrt b = Real.sqrt X := by
    rw [← Real.sqrt_mul hx.le]
    congr 1
    dsimp only [x]
    exact div_mul_cancel₀ _ (ne_of_gt hb)
  calc
    _ =
        (((h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re) *
            Real.sqrt x) *
          Real.sqrt b :=
      by rw [mul_assoc, hroot]
    _ ≤ ((1 + ε) * ((h : ℝ) - 1) * K.mass * Real.log q) * Real.sqrt b := hm
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements.MellinKernel
