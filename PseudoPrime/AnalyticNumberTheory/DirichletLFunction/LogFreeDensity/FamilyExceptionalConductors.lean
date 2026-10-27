/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyWeightedZeros

/-! # Uniformly bounded exceptional conductors from unconditional family density -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- Collect the conductors occurring in the primitive-family zero ledger at the
same conductor and height cutoff. The real-part threshold is explicit. This finite
image selects all conductors with bad zeros and retains actual analytic multiplicity
in the source ledger used to bound its cardinality. -/
noncomputable def exceptionalFamilyConductors (R : ℕ) (σ : ℝ) : Finset ℕ :=
  (primitiveCharacterFamilyZeroOccurrenceLedger R σ R).image (fun o ↦ o.1.val + 1)

/-- Every selected exceptional conductor is greater than one. The source ledger
contains a nonprincipal primitive character, so its modulus cannot be one.
This supplies the lower-conductor condition in the theta-supply exception contract. -/
theorem exceptionalFamilyConductors_one_lt {R : ℕ} {σ : ℝ} {e : ℕ}
    (he : e ∈ exceptionalFamilyConductors R σ) : 1 < e := by
  obtain ⟨o, ho, heq⟩ := Finset.mem_image.mp he
  obtain ⟨q, χ, hne, hp, hq, ρ, i, heo, _⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_positive_count ho
  subst o
  exact heq ▸ hq

/-- A primitive nonprincipal completed zero above the selected real-part threshold
and below the cutoff forces its conductor into the exceptional set. Use the positive
analytic order to select an occurrence index. This covers every bad zero, including
multiple zeros, rather than choosing one zero per character. -/
theorem conductor_mem_exceptionalFamilyConductors_of_zero {R : ℕ} {q : Fin R}
    {χ : DirichletCharacter ℂ (q.val + 1)} (hp : χ.IsPrimitive) (hne : χ ≠ 1) {σ : ℝ} {ρ : ℂ}
    (hz : χ.completedLFunction ρ = 0) (hre : σ ≤ ρ.re) (hh : |ρ.im| ≤ R) :
    q.val + 1 ∈ exceptionalFamilyConductors R σ := by
  let i : Fin (analyticOrderNatAt χ.completedLFunction ρ) :=
    ⟨0, analyticOrderNatAt_pos_of_completedLFunction_zero χ hne hz⟩
  have ho :=
    familyZeroOccurrence_mem_of_coordinates i hne hp hz hre
      (completedLFunction_zero_re_lt_one hne hz).le hh
  exact Finset.mem_image.mpr ⟨⟨q, χ, ρ, i⟩, ho, rfl⟩

/-- For a primitive nonprincipal character outside the exceptional conductor set,
every completed zero below the height cutoff lies strictly left of the selected
threshold. This is the contrapositive of the bad-zero occurrence construction. -/
theorem completed_zero_re_lt_of_conductor_not_exceptional {R : ℕ} {q : Fin R}
    {χ : DirichletCharacter ℂ (q.val + 1)} (hp : χ.IsPrimitive) (hne : χ ≠ 1) {σ : ℝ}
    (hq : q.val + 1 ∉ exceptionalFamilyConductors R σ) {ρ : ℂ} (hz : χ.completedLFunction ρ = 0)
    (hh : |ρ.im| ≤ R) : ρ.re < σ := by
  by_contra hre
  exact hq (conductor_mem_exceptionalFamilyConductors_of_zero hp hne hz (le_of_not_gt hre) hh)

/-- The proved log-free density gives a uniform exceptional-conductor bound at
threshold `1-c/log R`, for positive `c` and `log R ≥ 2c`. The bound is the natural
ceiling of `C exp(Ac)`, independent of the cutoff. Compare the finite image with
the occurrence count and cancel the logarithm in the density exponent. -/
theorem exists_uniform_exceptionalFamilyConductors_card_bound :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ (c : ℝ),
          0 < c →
            ∀ (R : ℕ),
              2 ≤ R →
                2 * c ≤ Real.log R →
                (exceptionalFamilyConductors R (1 - c / Real.log R)).card ≤
                  ⌈C * Real.exp (A * c)⌉₊ := by
  obtain ⟨A, C, hA, hC, hdensity⟩ := exists_primitiveCharacterFamily_log_free_density
  refine ⟨A, C, hA, hC, ?_⟩
  intro c hc R hR hlog
  have hRreal : (1 : ℝ) < R := by
    have hh : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith only [hh]
  have hY : 0 < Real.log R := Real.log_pos hRreal
  have hratio : c / Real.log R ≤ 1 / 2 := (div_le_iff₀ hY).mpr (by linarith only [hlog])
  have hσlo : (1 / 2 : ℝ) ≤ 1 - c / Real.log R := by linarith only [hratio]
  have hσhi : 1 - c / Real.log R ≤ 1 := sub_le_self _ (div_nonneg hc.le hY.le)
  have hcard :=
    Finset.card_image_le (s :=
      primitiveCharacterFamilyZeroOccurrenceLedger R (1 - c / Real.log R) R) (f := fun o ↦
      o.1.val + 1)
  have hreal :
    ((exceptionalFamilyConductors R (1 - c / Real.log R)).card : ℝ) ≤
      primitiveCharacterFamilyZeroCount R (1 - c / Real.log R) := by
    have hh :
      ((exceptionalFamilyConductors R (1 - c / Real.log R)).card : ℝ) ≤
        ((primitiveCharacterFamilyZeroOccurrenceLedger R (1 - c / Real.log R) R).card : ℝ) := by
      exact_mod_cast hcard
    rw [← primitiveCharacterFamilyZeroCountAtNatHeight_eq_occurrenceLedger_card,
      primitiveCharacterFamilyZeroCountAtNatHeight_eq] at hh
    exact hh
  have hp : Real.rpow (R : ℝ) (A * (1 - (1 - c / Real.log R))) = Real.exp (A * c) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (zero_lt_one.trans hRreal)]
    congr 1
    calc
      _ = A * ((c / Real.log R) * Real.log R) := by ring
      _ = A * c := by rw [div_mul_cancel₀ _ hY.ne']
  have hb := (hreal.trans (hdensity R hR _ hσlo hσhi))
  rw [hp] at hb
  exact_mod_cast hb.trans (Nat.le_ceil (C * Real.exp (A * c)))

/-- Every complex Dirichlet character modulo two is principal. Its character type
has cardinality one by the totient formula. This excludes conductor two from the
nonprincipal primitive-family exception set. -/
theorem dirichletCharacter_mod_two_eq_one (χ : DirichletCharacter ℂ 2) : χ = 1 := by
  have hcard : Fintype.card (DirichletCharacter ℂ 2) ≤ 1 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    norm_num only [Nat.totient_two]
  have hsub := Fintype.card_le_one_iff.mp hcard
  exact hsub χ 1

/-- Conductor two never occurs in the exceptional set, since every character
modulo two is principal. Extract the recorded nonprincipal character and transport
its modulus to two. This helps isolate the fixed conductor four. -/
theorem two_notMem_exceptionalFamilyConductors (R : ℕ) (σ : ℝ) :
    2 ∉ exceptionalFamilyConductors R σ := by
  intro hmem
  obtain ⟨o, ho, hqeq⟩ := Finset.mem_image.mp hmem
  obtain ⟨q, χ, ρ, i, hne, he, hp, hz⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_extract ho
  subst o
  change q.val + 1 = 2 at hqeq
  have hprincipal : ∀ χ : DirichletCharacter ℂ (q.val + 1), χ = 1 := by
    rw [hqeq]
    exact dirichletCharacter_mod_two_eq_one
  exact hne (hprincipal χ)

/-- Remove conductor four from the exceptional conductor set. Moduli one and two
are already absent, so every remaining conductor fails to divide four. Conductor
four is handled separately in the arithmetic error, rather than declared zero-free. -/
noncomputable def exceptionalFamilyConductorsAwayFromFour (R : ℕ) (σ : ℝ) : Finset ℕ :=
  (exceptionalFamilyConductors R σ).erase 4

/-- Every selected exceptional conductor after erasing four is greater than one
and does not divide four. Enumerate the divisors of four and exclude one, two,
and four individually. This discharges the exact divisibility condition on exceptions. -/
theorem exceptionalFamilyConductorsAwayFromFour_not_dvd_four {R : ℕ} {σ : ℝ} {e : ℕ}
    (he : e ∈ exceptionalFamilyConductorsAwayFromFour R σ) : 1 < e ∧ ¬e ∣ 4 := by
  have hraw := (Finset.mem_erase.mp he).2
  have he4 := (Finset.mem_erase.mp he).1
  have he1 := exceptionalFamilyConductors_one_lt hraw
  refine ⟨he1, ?_⟩
  intro hd
  have hdiv := Nat.mem_divisors.mpr ⟨hd, (by norm_num only : (4 : ℕ) ≠ 0)⟩
  have hset : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [hset, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hdiv
  rcases hdiv with h1 | h2 | h4
  · exact (ne_of_gt he1) h1
  · exact two_notMem_exceptionalFamilyConductors R σ (h2 ▸ hraw)
  · exact he4 h4

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
