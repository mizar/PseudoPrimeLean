/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyExceptionalConductors
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyWeightedGap

/-! # Weighted zero sums after removing a bounded exceptional conductor set -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- Every family occurrence has absolute ordinate at most its ledger height.
Extract the recorded zero and read the imaginary interval of the closed rectangle.
This is the geometric input when excluding bad conductors from a weighted packet. -/
theorem occurrence_height_le {Q H : ℕ} {σ : ℝ} {o : FamilyZeroOccurrence Q}
    (ho : o ∈ occurrenceLedger Q σ H) : |(occurrenceValue o).im| ≤ H := by
  obtain ⟨q, χ, ρ, i, hne, heq, hp, hρ⟩ := ledger_mem_extract ho
  subst o
  have hb := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [completedRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm] at hb
  have him := hb.2
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_one, zero_sub, Complex.add_im, Complex.one_im, zero_add, add_zero,
    Complex.ofReal_re] at him
  rw [Set.uIcc_of_le (by linarith only [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)] : -(H : ℝ) ≤ H)] at him
  exact abs_le.mpr him

/-- For a primitive nonprincipal character of conductor different from four,
avoiding the reduced exceptional set gives a strict zero gap below the cutoff.
Its conductor would otherwise belong to the raw exceptional set and survive erasure.
The separate exclusion of conductor four is explicit. -/
theorem zero_re_lt_off_except {R : ℕ} {q : Fin R} {χ : DirichletCharacter ℂ (q.val + 1)}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) {σ : ℝ} (hq4 : q.val + 1 ≠ 4)
    (hq : q.val + 1 ∉ exceptionalExceptFour R σ) {ρ : ℂ} (hz : χ.completedLFunction ρ = 0)
    (hh : |ρ.im| ≤ R) : ρ.re < σ := by
  apply zero_re_lt_of_not_mem hp hne ?_ hz hh
  intro hraw
  exact hq (Finset.mem_erase.mpr ⟨hq4, hraw⟩)

/-- There are positive absolute constants such that, for each fixed positive
width parameter, one natural bound works for every sufficiently large cutoff.
The reduced exception set has at most that many elements, all greater than one
and none dividing four. Choose the ceiling bound before the cutoff and erase four.
No zero-free claim for conductor four is made. -/
theorem exists_exceptFourCap :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ (c : ℝ),
          0 < c →
            ∃ D : ℕ,
              ∀ R : ℕ,
                2 ≤ R →
                  2 * c ≤ Real.log R →
                  (exceptionalExceptFour R (1 - c / Real.log R)).card ≤ D ∧
                    (∀ e ∈ exceptionalExceptFour R (1 - c / Real.log R), 1 < e ∧ ¬e ∣ 4) := by
  obtain ⟨A, C, hA, hC, hcard⟩ := exists_exceptionalCap
  refine ⟨A, C, hA, hC, ?_⟩
  intro c hc
  refine ⟨⌈C * Real.exp (A * c)⌉₊, ?_⟩
  intro R hR hlog
  exact ⟨(Finset.card_erase_le).trans (hcard c hc R hR hlog), fun _ he ↦ exceptFour_not_dvd he⟩

/-- There are positive absolute constants giving an exponentially decaying
power-weighted zero sum outside the reduced exceptional conductors, for packets
whose conductors differ from four. The near-one strip and conductor-scale conditions
remain explicit. Extract each actual zero, derive its gap from exception avoidance,
and apply the unconditional weighted family density. The bad-conductor selection
is now concrete; conductor four must still be handled separately. -/
theorem family_inverseOff_le :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ (c : ℝ),
          0 < c →
            ∀ (R : ℕ),
              2 ≤ R →
                ∀ (x σ₀ : ℝ),
                  1 < x →
                    (1 / 2 : ℝ) ≤ σ₀ →
                    σ₀ ≤ 1 →
                    A * (1 - σ₀) ≤ 1 / 2 →
                    2 * A * Real.log ((R + 1 : ℕ) : ℝ) ≤ Real.log x →
                    ∀ S : Finset (FamilyZeroOccurrence R),
                      S ⊆ occurrenceLedger R (1 / 2) R →
                        (∀ o ∈ S, σ₀ ≤ (occurrenceValue o).re) →
                        (∀ o ∈ S, o.1.val + 1 ≠ 4) →
                        (∀ o ∈ S, o.1.val + 1 ∉ exceptionalExceptFour R (1 - c / Real.log R)) →
                        ∑ o ∈ S, x ^ (occurrenceValue o).re / (1 + (occurrenceValue o).im ^ 2) ≤
                          C * x * Real.exp (-(c / Real.log R) * Real.log x / 2) := by
  obtain ⟨A, C, hA, hC, hbound⟩ := family_inverseGap_le
  refine ⟨A, C, hA, hC, ?_⟩
  intro c hc R hR x σ₀ hx hσ₀lo hσ₀hi hδ hscale S hS hβlo hfour havoid
  have hRreal : (1 : ℝ) < R := by
    have hh : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith only [hh]
  apply
    hbound R R x σ₀ (c / Real.log R) hx hσ₀lo hσ₀hi hδ (div_nonneg hc.le (Real.log_pos hRreal).le)
      hscale S hS hβlo
  intro o ho
  have hh := occurrence_height_le (hS ho)
  have h4 := hfour o ho
  have hav := havoid o ho
  obtain ⟨q, χ, ρ, i, hne, heq, hp, hρ⟩ := ledger_mem_extract (hS ho)
  subst o
  have hz := (mem_completedZerosInRectangle_iff.mp hρ).2
  exact (zero_re_lt_off_except hp hne h4 hav hz hh).le

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
