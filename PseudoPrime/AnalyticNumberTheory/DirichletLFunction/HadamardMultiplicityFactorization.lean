/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.General.FinsetNeighborhood

/-!
# Finite multiplicity-aware Hadamard factorization for Dirichlet `L`-functions

Define the finite genus-one product over a nontrivial character's completed zeros in a rectangle.
For primitive characters, completed nonvanishing at zero permits nonzero zero-locations in
these factors; matching multiplicities give local analytic units and an entire patched quotient.
The logarithmic derivative splits into a finite zero sum and the quotient's logarithmic derivative.
The final declarations give ordinary `L` multiplicities and local factorizations for nontrivial
characters, without requiring primitivity. All constructions are independent of contour kernels.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Definition: the genus-one Hadamard factor attached to a nonzero completed Dirichlet `L` zero.
Input: complex variable `s` and zero location `ρ`.
Output: `(1 - s / ρ) exp(s / ρ)`.
Role: finite products of these factors form the multiplicity-aware completed-`L` Hadamard ledger.
-/
noncomputable def dirichletCompletedHadamardFactor (s ρ : ℂ) : ℂ :=
  (1 - s / ρ) * Complex.exp (s / ρ)

/-- Each completed-`L` genus-one factor is entire in its variable. -/
theorem differentiable_dirichletCompletedHadamardFactor (ρ : ℂ) :
    Differentiable ℂ (fun s ↦ dirichletCompletedHadamardFactor s ρ) := by
  intro s
  unfold dirichletCompletedHadamardFactor
  fun_prop

/-- The derivative of the completed-`L` genus-one factor has the expected cancellation. -/
theorem deriv_dirichletCompletedHadamardFactor (s ρ : ℂ) :
    deriv (fun z ↦ dirichletCompletedHadamardFactor z ρ) s =
      -(s / ρ ^ 2) * Complex.exp (s / ρ) := by
  have hdiv : HasDerivAt (fun z : ℂ ↦ z / ρ) (1 / ρ) s := (hasDerivAt_id s).div_const ρ
  have hlinear : HasDerivAt (fun z : ℂ ↦ 1 - z / ρ) (-(1 / ρ)) s := hdiv.const_sub 1
  have hexp : HasDerivAt (fun z : ℂ ↦ Complex.exp (z / ρ)) (Complex.exp (s / ρ) * (1 / ρ)) s :=
    (Complex.hasDerivAt_exp (s / ρ)).comp s hdiv
  unfold dirichletCompletedHadamardFactor
  change deriv ((fun z : ℂ ↦ 1 - z / ρ) * fun z ↦ Complex.exp (z / ρ)) s = _
  rw [hlinear.mul hexp |>.deriv]
  simp only [div_eq_mul_inv, pow_two]
  ring

/-- A completed-`L` genus-one factor is nonzero away from its nonzero attached zero. -/
theorem dirichletCompletedHadamardFactor_ne_zero {s ρ : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    dirichletCompletedHadamardFactor s ρ ≠ 0 := by
  unfold dirichletCompletedHadamardFactor
  apply mul_ne_zero
  · intro hlinear
    apply hs
    have hdiv : s / ρ = 1 := sub_eq_zero.mp hlinear |>.symm
    have hmul : s = 1 * ρ := (div_eq_iff hρ).mp hdiv
    simpa only [one_mul] using hmul
  · exact Complex.exp_ne_zero _

/-- The completed-`L` genus-one factor has logarithmic derivative `1 / (s - ρ) + 1 / ρ`. -/
theorem logDeriv_dirichletCompletedHadamardFactor {s ρ : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    logDeriv (fun z ↦ dirichletCompletedHadamardFactor z ρ) s = 1 / (s - ρ) + 1 / ρ := by
  rw [logDeriv_apply, deriv_dirichletCompletedHadamardFactor]
  unfold dirichletCompletedHadamardFactor
  have hlinear : 1 - s / ρ ≠ 0 := by
    intro h
    apply hs
    have hdiv : s / ρ = 1 := sub_eq_zero.mp h |>.symm
    simpa only [one_mul] using (div_eq_iff hρ).mp hdiv
  field_simp [hlinear]
  ring

/--
Input/assumptions: a primitive nontrivial character and an entry of a completed-zero ledger.
Conclusion: the ledger zero is nonzero.
Content: a primitive nontrivial completed `L`-function does not vanish at the origin.
Role: permits genus-one factors indexed by the completed-zero ledger.
-/
theorem dirichletCompletedLFunction_zero_ne_zero_of_mem_ledger {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    ρ ≠ 0 := by
  intro hzero
  subst ρ
  exact
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
      (mem_dirichletCompletedLFunctionZerosInRectangle_iff.mp
          hρ).2

/--
Definition: the multiplicity-aware genus-one factor attached to a completed Dirichlet `L` zero.
Input: a character, complex variable, and a zero location.
Output: the genus-one factor raised to its completed analytic multiplicity.
Role: records the exact local zero order in the finite completed-Hadamard product.
-/
noncomputable def dirichletCompletedMultiplicityHadamardFactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s ρ : ℂ) : ℂ :=
  dirichletCompletedHadamardFactor s ρ ^
    dirichletCompletedLFunctionZeroMultiplicity
      χ ρ

/--
Definition: the multiplicity-aware finite completed-`L` Hadamard product on a rectangle ledger.
Input: a nontrivial character and two rectangle corners.
Output: the finite product of all ledger factors with analytic multiplicity.
Role: is the denominator for the local completed-Hadamard quotient.
-/
noncomputable def dirichletCompletedMultiplicityHadamardProduct {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) (s : ℂ) : ℂ :=
  ∏
    ρ ∈
      dirichletCompletedLFunctionZerosInRectangle
        χ hχ z w,
    dirichletCompletedMultiplicityHadamardFactor χ s ρ

/-- The finite multiplicity-aware completed-`L` Hadamard product is entire. -/
theorem differentiable_dirichletCompletedMultiplicityHadamardProduct {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) :
    Differentiable ℂ (dirichletCompletedMultiplicityHadamardProduct χ hχ z w) := by
  intro s
  unfold dirichletCompletedMultiplicityHadamardProduct dirichletCompletedMultiplicityHadamardFactor
  apply DifferentiableAt.fun_finsetProd
  intro ρ _
  exact ((differentiable_dirichletCompletedHadamardFactor ρ).differentiableAt).pow _

/--
Input/assumptions: a primitive nontrivial character and a point outside its rectangle zero ledger.
Conclusion: the finite multiplicity-aware completed-Hadamard product is nonzero at that point.
Content: every genus-one factor avoids both its origin singularity and its attached zero.
Role: supplies the denominator condition for finite-product logarithmic derivatives.
-/
theorem dirichletCompletedMultiplicityHadamardProduct_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w s : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hs :
      ∀
        ρ ∈
          dirichletCompletedLFunctionZerosInRectangle
            χ hne z w,
        s ≠ ρ) :
    dirichletCompletedMultiplicityHadamardProduct χ hne z w s ≠ 0 := by
  unfold dirichletCompletedMultiplicityHadamardProduct dirichletCompletedMultiplicityHadamardFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  exact
    pow_ne_zero _
      (dirichletCompletedHadamardFactor_ne_zero
        (dirichletCompletedLFunction_zero_ne_zero_of_mem_ledger hprimitive hne hρ) (hs ρ hρ))

/--
Input/assumptions: a primitive nontrivial character and a point outside its rectangle zero ledger.
Conclusion: the finite product logarithmic derivative is the multiplicity-weighted ledger sum.
Content: apply the logarithmic derivative product rule and the genus-one factor identity.
Role: is the finite-sum interface for the local completed-Hadamard quotient.
-/
theorem logDeriv_dirichletCompletedMultiplicityHadamardProduct_eq_sum {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w s : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hs :
      ∀
        ρ ∈
          dirichletCompletedLFunctionZerosInRectangle
            χ hne z w,
        s ≠ ρ) :
    logDeriv (dirichletCompletedMultiplicityHadamardProduct χ hne z w) s =
      ∑
        ρ ∈
          dirichletCompletedLFunctionZerosInRectangle
            χ hne z w,
        dirichletCompletedLFunctionZeroMultiplicity
            χ ρ *
          (1 / (s - ρ) + 1 / ρ) := by
  unfold dirichletCompletedMultiplicityHadamardProduct dirichletCompletedMultiplicityHadamardFactor
  have hprod :
    (fun s ↦
        ∏
          ρ ∈
            dirichletCompletedLFunctionZerosInRectangle
              χ hne z w,
          dirichletCompletedHadamardFactor s ρ ^
            dirichletCompletedLFunctionZeroMultiplicity
              χ ρ) =
      ∏
        ρ ∈
          dirichletCompletedLFunctionZerosInRectangle
            χ hne z w,
        (fun s ↦
          dirichletCompletedHadamardFactor s ρ ^
            dirichletCompletedLFunctionZeroMultiplicity
              χ ρ) := by
    funext s
    simp only [Finset.prod_apply]
  rw [hprod]
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (differentiable_dirichletCompletedHadamardFactor ρ).differentiableAt]
    rw [logDeriv_dirichletCompletedHadamardFactor
        (dirichletCompletedLFunction_zero_ne_zero_of_mem_ledger hprimitive hne hρ) (hs ρ hρ)]
  · intro ρ hρ
    exact
      pow_ne_zero _
        (dirichletCompletedHadamardFactor_ne_zero
          (dirichletCompletedLFunction_zero_ne_zero_of_mem_ledger hprimitive hne hρ) (hs ρ hρ))
  · intro ρ _
    exact ((differentiable_dirichletCompletedHadamardFactor ρ).differentiableAt).pow _

/--
Definition: the pointwise quotient of completed `L` by its finite rectangle Hadamard product.
Input: a nontrivial character, rectangle ledger, and complex point.
Output: the totalized quotient by the finite multiplicity-aware product.
Role: away from the ledger this is the analytic residual factor whose removable values at ledger
zeros are filled by
`dirichletCompletedMultiplicityHadamardEntireQuotient` below.
-/
noncomputable def dirichletCompletedMultiplicityHadamardQuotient {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w s : ℂ) : ℂ :=
  DirichletCharacter.completedLFunction χ s /
    dirichletCompletedMultiplicityHadamardProduct χ hχ z w s

/--
Input/assumptions: a primitive nontrivial character and a point outside its rectangle zero ledger.
Conclusion: the finite completed-Hadamard quotient is analytic at that point.
Content: divide the entire completed function by the nonvanishing finite product.
Role: establishes the off-ledger branch of the removable-quotient construction.
-/
theorem analyticAt_dirichletCompletedMultiplicityHadamardQuotient_of_not_mem {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w s : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hs :
      s ∉
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    AnalyticAt ℂ (dirichletCompletedMultiplicityHadamardQuotient χ hne z w) s := by
  unfold dirichletCompletedMultiplicityHadamardQuotient
  apply ((DirichletCharacter.differentiable_completedLFunction hne).analyticAt s).div
  · exact (differentiable_dirichletCompletedMultiplicityHadamardProduct χ hne z w).analyticAt s
  · apply dirichletCompletedMultiplicityHadamardProduct_ne_zero hprimitive hne
    intro ρ hρ hsr
    exact hs (hsr ▸ hρ)

/-- The finite completed-Hadamard product with one designated ledger factor removed. -/
noncomputable def dirichletCompletedMultiplicityHadamardCofactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w ρ s : ℂ) : ℂ :=
  ∏
    σ ∈
      (dirichletCompletedLFunctionZerosInRectangle
            χ hχ z w).erase
        ρ,
    dirichletCompletedMultiplicityHadamardFactor χ s σ

/-- A designated completed-zero ledger factor splits off from its finite product. -/
theorem dirichletCompletedMultiplicityHadamardProduct_eq_factor_mul_cofactor {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hχ : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hχ z w)
    (s : ℂ) :
    dirichletCompletedMultiplicityHadamardProduct χ hχ z w s =
      dirichletCompletedMultiplicityHadamardFactor χ s ρ *
        dirichletCompletedMultiplicityHadamardCofactor χ hχ z w ρ s := by
  unfold dirichletCompletedMultiplicityHadamardProduct
    dirichletCompletedMultiplicityHadamardCofactor
  exact (Finset.mul_prod_erase _ _ hρ).symm

/-- The removed-factor completed-Hadamard cofactor is entire. -/
theorem differentiable_dirichletCompletedMultiplicityHadamardCofactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w ρ : ℂ) :
    Differentiable ℂ (dirichletCompletedMultiplicityHadamardCofactor χ hχ z w ρ) := by
  intro s
  unfold dirichletCompletedMultiplicityHadamardCofactor dirichletCompletedMultiplicityHadamardFactor
  apply DifferentiableAt.fun_finsetProd
  intro σ _
  exact ((differentiable_dirichletCompletedHadamardFactor σ).differentiableAt).pow _

/-- At a designated ledger zero, its removed-factor completed-Hadamard cofactor is nonzero. -/
theorem dirichletCompletedMultiplicityHadamardCofactor_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) :
    dirichletCompletedMultiplicityHadamardCofactor χ hne z w ρ ρ ≠ 0 := by
  unfold dirichletCompletedMultiplicityHadamardCofactor dirichletCompletedMultiplicityHadamardFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro σ hσ
  have hσledger :
    σ ∈
      dirichletCompletedLFunctionZerosInRectangle
        χ hne z w :=
    Finset.mem_erase.mp hσ |>.2
  have hne' : ρ ≠ σ := (Finset.mem_erase.mp hσ |>.1).symm
  exact
    pow_ne_zero _
      (dirichletCompletedHadamardFactor_ne_zero
        (dirichletCompletedLFunction_zero_ne_zero_of_mem_ledger hprimitive hne hσledger) hne')

/-- The nonvanishing analytic unit in a completed multiplicity-aware genus-one factor. -/
noncomputable def dirichletCompletedMultiplicityHadamardUnit {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s ρ : ℂ) : ℂ :=
  ((-1 / ρ) * Complex.exp (s / ρ)) ^
    dirichletCompletedLFunctionZeroMultiplicity
      χ ρ

/-- A completed multiplicity-aware factor is its zero power times a nonvanishing analytic unit. -/
theorem dirichletCompletedMultiplicityHadamardFactor_eq_sub_pow_mul_unit {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {s ρ : ℂ} (hρ : ρ ≠ 0) :
    dirichletCompletedMultiplicityHadamardFactor χ s ρ =
      (s - ρ) ^
          dirichletCompletedLFunctionZeroMultiplicity
            χ ρ *
        dirichletCompletedMultiplicityHadamardUnit χ s ρ := by
  unfold dirichletCompletedMultiplicityHadamardFactor dirichletCompletedMultiplicityHadamardUnit
  rw [← mul_pow]
  congr 1
  unfold dirichletCompletedHadamardFactor
  field_simp
  ring

/-- The analytic unit in a completed multiplicity-aware factor is nonzero at its attached zero. -/
theorem dirichletCompletedMultiplicityHadamardUnit_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {ρ : ℂ} (hρ : ρ ≠ 0) :
    dirichletCompletedMultiplicityHadamardUnit χ ρ ρ ≠ 0 := by
  unfold dirichletCompletedMultiplicityHadamardUnit
  exact
    pow_ne_zero _
      (mul_ne_zero (div_ne_zero (neg_ne_zero.mpr one_ne_zero) hρ) (Complex.exp_ne_zero _))

/-- The analytic unit left after removing one completed-Hadamard zero power from the product. -/
noncomputable def dirichletCompletedMultiplicityHadamardProductUnit {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w ρ s : ℂ) : ℂ :=
  dirichletCompletedMultiplicityHadamardUnit χ s ρ *
    dirichletCompletedMultiplicityHadamardCofactor χ hχ z w ρ s

/-- A finite completed-Hadamard product has the exact local zero-power factorization. -/
theorem dirichletCompletedMultiplicityHadamardProduct_eq_sub_pow_mul_unit {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w)
    (s : ℂ) :
    dirichletCompletedMultiplicityHadamardProduct χ hne z w s =
      (s - ρ) ^
          dirichletCompletedLFunctionZeroMultiplicity
            χ ρ *
        dirichletCompletedMultiplicityHadamardProductUnit χ hne z w ρ s := by
  rw [dirichletCompletedMultiplicityHadamardProduct_eq_factor_mul_cofactor hne hρ]
  rw [dirichletCompletedMultiplicityHadamardFactor_eq_sub_pow_mul_unit
      (dirichletCompletedLFunction_zero_ne_zero_of_mem_ledger hprimitive hne hρ)]
  simp only [dirichletCompletedMultiplicityHadamardProductUnit]
  ring

/-- The finite-product local unit is entire in its variable. -/
theorem differentiable_dirichletCompletedMultiplicityHadamardProductUnit {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w ρ : ℂ) :
    Differentiable ℂ (dirichletCompletedMultiplicityHadamardProductUnit χ hχ z w ρ) := by
  intro s
  unfold dirichletCompletedMultiplicityHadamardProductUnit
    dirichletCompletedMultiplicityHadamardUnit
  apply DifferentiableAt.mul
  · fun_prop
  · exact (differentiable_dirichletCompletedMultiplicityHadamardCofactor χ hχ z w ρ) s

/-- At a ledger zero, the finite-product local unit is nonzero. -/
theorem dirichletCompletedMultiplicityHadamardProductUnit_ne_zero_of_mem_ledger {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    dirichletCompletedMultiplicityHadamardProductUnit χ hne z w ρ ρ ≠ 0 := by
  unfold dirichletCompletedMultiplicityHadamardProductUnit
  apply mul_ne_zero
  · exact
      dirichletCompletedMultiplicityHadamardUnit_ne_zero
        (dirichletCompletedLFunction_zero_ne_zero_of_mem_ledger hprimitive hne hρ)
  · exact dirichletCompletedMultiplicityHadamardCofactor_ne_zero hprimitive hne

/--
Input/assumptions: a primitive nontrivial character and one completed-zero ledger entry.
Conclusion: its pointwise finite Hadamard quotient has a nonvanishing analytic local extension.
Content: cancel the matching completed-`L` and finite-product zero powers on a punctured
neighborhood, leaving a quotient of analytic units.
Role: supplies the ledger-zero branch needed to glue the local completed-Hadamard quotient.
-/
theorem exists_dirichletCompletedMultiplicityHadamardQuotient_localFactor {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ))
          (dirichletCompletedMultiplicityHadamardQuotient χ hne z w) g := by
  obtain ⟨h, hanalytic, hnezero, hfactor⟩ :=
    exists_dirichletCompletedLFunction_localFactor
      hne ρ
  let u := dirichletCompletedMultiplicityHadamardProductUnit χ hne z w ρ
  have huDifferentiable :=
    differentiable_dirichletCompletedMultiplicityHadamardProductUnit χ hne z w ρ
  refine ⟨fun s ↦ h s / u s, ?_, ?_, ?_⟩
  · apply hanalytic.div
    · change AnalyticAt ℂ (dirichletCompletedMultiplicityHadamardProductUnit χ hne z w ρ) ρ
      exact huDifferentiable.analyticAt ρ
    · exact
        dirichletCompletedMultiplicityHadamardProductUnit_ne_zero_of_mem_ledger hprimitive hne hρ
  · exact
      div_ne_zero hnezero
        (dirichletCompletedMultiplicityHadamardProductUnit_ne_zero_of_mem_ledger hprimitive hne hρ)
  · have huAnalytic : AnalyticAt ℂ u ρ := by
      change AnalyticAt ℂ (dirichletCompletedMultiplicityHadamardProductUnit χ hne z w ρ) ρ
      exact huDifferentiable.analyticAt ρ
    have hu : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), u s ≠ 0 :=
      ((huAnalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp
            (dirichletCompletedMultiplicityHadamardProductUnit_ne_zero_of_mem_ledger hprimitive hne
              hρ)).filter_mono
        nhdsWithin_le_nhds
    have hproduct :
      ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ),
        dirichletCompletedMultiplicityHadamardProduct χ hne z w s =
          (s - ρ) ^
              dirichletCompletedLFunctionZeroMultiplicity
                χ ρ *
            u s := by
      filter_upwards with s
      exact dirichletCompletedMultiplicityHadamardProduct_eq_sub_pow_mul_unit hprimitive hne hρ s
    filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds, hu, hproduct,
      eventually_mem_nhdsWithin] with s hscompleted hunit hsproduct hs
    unfold dirichletCompletedMultiplicityHadamardQuotient
    simp only [smul_eq_mul] at hscompleted
    rw [hscompleted, hsproduct]
    have hsne : s - ρ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs)
    field_simp

/-- A selected analytic local extension of the completed finite Hadamard quotient. -/
noncomputable def dirichletCompletedMultiplicityHadamardQuotientLocalExtension {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w ρ : ℂ) (hprimitive : χ.IsPrimitive)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hχ z w) :
    ℂ → ℂ :=
  (exists_dirichletCompletedMultiplicityHadamardQuotient_localFactor hprimitive hχ hρ).choose

/-- The selected local quotient extension is analytic at its completed-zero ledger entry. -/
theorem analyticAt_dirichletCompletedMultiplicityHadamardQuotientLocalExtension {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    AnalyticAt ℂ
      (dirichletCompletedMultiplicityHadamardQuotientLocalExtension χ hne z w ρ hprimitive hρ) ρ :=
  let hlocal := exists_dirichletCompletedMultiplicityHadamardQuotient_localFactor hprimitive hne hρ
  hlocal.choose_spec.1

/-- The selected local quotient extension is nonzero at its completed-zero ledger entry. -/
theorem dirichletCompletedMultiplicityHadamardQuotientLocalExtension_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    dirichletCompletedMultiplicityHadamardQuotientLocalExtension χ hne z w ρ hprimitive hρ ρ ≠ 0 :=
  let hlocal := exists_dirichletCompletedMultiplicityHadamardQuotient_localFactor hprimitive hne hρ
  hlocal.choose_spec.2.1

/-- On its punctured neighborhood, the selected local extension equals the pointwise quotient. -/
theorem dirichletCompletedMultiplicityHadamardQuotient_eventuallyEq_localExtension {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    dirichletCompletedMultiplicityHadamardQuotient χ hne z w =ᶠ[nhdsWithin ρ {ρ}ᶜ]
      dirichletCompletedMultiplicityHadamardQuotientLocalExtension χ hne z w ρ hprimitive hρ :=
  let hlocal := exists_dirichletCompletedMultiplicityHadamardQuotient_localFactor hprimitive hne hρ
  hlocal.choose_spec.2.2

/-- The completed finite quotient with its removable ledger values filled by local extensions. -/
noncomputable def dirichletCompletedMultiplicityHadamardEntireQuotient {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) (hprimitive : χ.IsPrimitive) (s : ℂ) : ℂ :=
  if hs :
      s ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hχ z w then
    dirichletCompletedMultiplicityHadamardQuotientLocalExtension χ hχ z w s hprimitive hs s
  else dirichletCompletedMultiplicityHadamardQuotient χ hχ z w s

/-- Off the completed-zero ledger, the patched quotient is the pointwise quotient. -/
theorem dirichletCompletedMultiplicityHadamardEntireQuotient_eq_quotient_of_not_mem {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {z w s : ℂ} (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (hs :
      s ∉
        dirichletCompletedLFunctionZerosInRectangle
          χ hχ z w) :
    dirichletCompletedMultiplicityHadamardEntireQuotient χ hχ z w hprimitive s =
      dirichletCompletedMultiplicityHadamardQuotient χ hχ z w s := by
  simp only [dirichletCompletedMultiplicityHadamardEntireQuotient, dite_eq_right hs]

/-- Near a completed-zero ledger entry, the patched quotient agrees with its local extension. -/
theorem dirichletCompletedMultiplicityHadamardEntireQuotient_eventuallyEq_localExtension {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive =ᶠ[nhds ρ]
      dirichletCompletedMultiplicityHadamardQuotientLocalExtension χ hne z w ρ hprimitive hρ := by
  let S :=
    dirichletCompletedLFunctionZerosInRectangle
      χ hne z w
  have havoid : ∀ᶠ s in nhds ρ, s ∉ S.erase ρ :=
    General.eventually_not_mem_finset_nhds_of_not_mem
      (by simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true])
  have hlocal :
    ∀ᶠ s in nhds ρ,
      s ∈ ({ρ}ᶜ : Set ℂ) →
        dirichletCompletedMultiplicityHadamardQuotient χ hne z w s =
          dirichletCompletedMultiplicityHadamardQuotientLocalExtension χ hne z w ρ hprimitive hρ
            s :=
    eventually_nhdsWithin_iff.mp
      (dirichletCompletedMultiplicityHadamardQuotient_eventuallyEq_localExtension hprimitive hne hρ)
  filter_upwards [havoid, hlocal] with s hsavoid hs
  by_cases hmem : s ∈ S
  · have hsρ : s = ρ := by
      by_contra hsne
      exact hsavoid (Finset.mem_erase.mpr ⟨hsne, hmem⟩)
    subst s
    simp only [dirichletCompletedMultiplicityHadamardEntireQuotient, dite_eq_left hρ]
  · have hsne : s ∈ ({ρ}ᶜ : Set ℂ) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show s ≠ ρ from fun h => hmem (h ▸ hρ))
    rw [dirichletCompletedMultiplicityHadamardEntireQuotient_eq_quotient_of_not_mem hne hprimitive
        hmem]
    exact hs hsne

/-- The globally patched completed finite quotient is analytic at every ledger zero. -/
theorem analyticAt_dirichletCompletedMultiplicityHadamardEntireQuotient_of_mem {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w ρ : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hρ :
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    AnalyticAt ℂ (dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive) ρ :=
  (analyticAt_dirichletCompletedMultiplicityHadamardQuotientLocalExtension hprimitive hne hρ).congr
    (dirichletCompletedMultiplicityHadamardEntireQuotient_eventuallyEq_localExtension hprimitive hne
        hρ).symm

/-- The globally patched completed finite quotient is analytic away from its zero ledger. -/
theorem analyticAt_dirichletCompletedMultiplicityHadamardEntireQuotient_of_not_mem {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {z w s : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hs :
      s ∉
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w) :
    AnalyticAt ℂ (dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive) s := by
  apply
    (analyticAt_dirichletCompletedMultiplicityHadamardQuotient_of_not_mem hprimitive hne hs).congr
  filter_upwards [General.eventually_not_mem_finset_nhds_of_not_mem
      hs] with
    t ht
  exact
    (dirichletCompletedMultiplicityHadamardEntireQuotient_eq_quotient_of_not_mem hne hprimitive
        ht).symm

/-- The patched finite completed-Hadamard quotient is analytic at every complex point. -/
theorem analyticAt_dirichletCompletedMultiplicityHadamardEntireQuotient {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) (hprimitive : χ.IsPrimitive) (s : ℂ) :
    AnalyticAt ℂ (dirichletCompletedMultiplicityHadamardEntireQuotient χ hχ z w hprimitive) s := by
  by_cases hs :
    s ∈
      dirichletCompletedLFunctionZerosInRectangle
        χ hχ z w
  · exact analyticAt_dirichletCompletedMultiplicityHadamardEntireQuotient_of_mem hprimitive hχ hs
  · exact
      analyticAt_dirichletCompletedMultiplicityHadamardEntireQuotient_of_not_mem hprimitive hχ hs

/-- The completed `L`-function factors through its finite patched Hadamard quotient. -/
theorem dirichletCompletedLFunction_eq_multiplicityHadamardProduct_mul_entireQuotient {N : ℕ}
    [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w s : ℂ) (hprimitive : χ.IsPrimitive) :
    DirichletCharacter.completedLFunction χ s =
      dirichletCompletedMultiplicityHadamardProduct χ hχ z w s *
        dirichletCompletedMultiplicityHadamardEntireQuotient χ hχ z w hprimitive s := by
  by_cases hs :
    s ∈
      dirichletCompletedLFunctionZerosInRectangle
        χ hχ z w
  · have hzero : DirichletCharacter.completedLFunction χ s = 0 :=
      (mem_dirichletCompletedLFunctionZerosInRectangle_iff.mp
          hs).2
    rw [hzero]
    rw [dirichletCompletedMultiplicityHadamardProduct_eq_factor_mul_cofactor hχ hs]
    unfold dirichletCompletedMultiplicityHadamardFactor
    have hfactor : dirichletCompletedHadamardFactor s s = 0 := by
      unfold dirichletCompletedHadamardFactor
      have hsne := dirichletCompletedLFunction_zero_ne_zero_of_mem_ledger hprimitive hχ hs
      apply mul_eq_zero_of_left
      field_simp
      ring
    rw [hfactor]
    have hmult :
      0 <
        dirichletCompletedLFunctionZeroMultiplicity
          χ s :=
      dirichletCompletedLFunctionZeroMultiplicity_pos
        hχ hzero
    rw [zero_pow (Nat.ne_of_gt hmult)]
    ring
  · rw [dirichletCompletedMultiplicityHadamardEntireQuotient_eq_quotient_of_not_mem hχ hprimitive
        hs]
    unfold dirichletCompletedMultiplicityHadamardQuotient
    have hproduct :=
      dirichletCompletedMultiplicityHadamardProduct_ne_zero hprimitive hχ (z := z) (w := w) (s := s)
        (fun ρ hρ hsr => hs (hsr ▸ hρ))
    field_simp

/-- Away from completed `L`-zeros, its logarithmic derivative is the finite zero sum plus the
logarithmic derivative of the patched finite Hadamard quotient. -/
theorem logDeriv_dirichletCompletedLFunction_eq_finite_sum_add_logDeriv_entireQuotient {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {z w s : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      (∑
          ρ ∈
            dirichletCompletedLFunctionZerosInRectangle
              χ hne z w,
          dirichletCompletedLFunctionZeroMultiplicity
              χ ρ *
            (1 / (s - ρ) + 1 / ρ)) +
        logDeriv (dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive) s := by
  have hfactor :=
    dirichletCompletedLFunction_eq_multiplicityHadamardProduct_mul_entireQuotient χ hne z w s
      hprimitive
  have heq :
    DirichletCharacter.completedLFunction χ = fun t ↦
      dirichletCompletedMultiplicityHadamardProduct χ hne z w t *
        dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive t := by
    funext t
    exact
      dirichletCompletedLFunction_eq_multiplicityHadamardProduct_mul_entireQuotient χ hne z w t
        hprimitive
  have hledger :
    ∀
      ρ ∈
        dirichletCompletedLFunctionZerosInRectangle
          χ hne z w,
      s ≠ ρ := by
    intro ρ hρ hsr
    apply hs
    rw [hsr]
    exact
      (mem_dirichletCompletedLFunctionZerosInRectangle_iff.mp
          hρ).2
  have hproduct := dirichletCompletedMultiplicityHadamardProduct_ne_zero hprimitive hne hledger
  have hquotient :
    dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive s ≠ 0 := by
    intro hzero
    apply hs
    rw [hfactor, hzero]
    simp only [mul_zero]
  have hquotientAnalytic :=
    analyticAt_dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive s
  have hmul :
    (fun t ↦
        dirichletCompletedMultiplicityHadamardProduct χ hne z w t *
          dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive t) =
      dirichletCompletedMultiplicityHadamardProduct χ hne z w *
        dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive := by
    funext t
    rfl
  rw [heq, hmul,
    logDeriv_mul s hproduct hquotient
      ((differentiable_dirichletCompletedMultiplicityHadamardProduct χ hne z w) s)
      hquotientAnalytic.differentiableAt]
  rw [logDeriv_dirichletCompletedMultiplicityHadamardProduct_eq_sum hprimitive hne hledger]

/-- The patched finite completed-Hadamard quotient is zero-free on its source rectangle. -/
theorem dirichletCompletedMultiplicityHadamardEntireQuotient_ne_zero_on_rectangle {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z w s : ℂ} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hs :
      s ∈
        dirichletCompletedLFunctionRectangleBox
          z w) :
    dirichletCompletedMultiplicityHadamardEntireQuotient χ hne z w hprimitive s ≠ 0 := by
  by_cases hmem :
    s ∈
      dirichletCompletedLFunctionZerosInRectangle
        χ hne z w
  · simp only [dirichletCompletedMultiplicityHadamardEntireQuotient, dite_eq_left hmem]
    exact dirichletCompletedMultiplicityHadamardQuotientLocalExtension_ne_zero hprimitive hne hmem
  · intro hzero
    have hcompleted : DirichletCharacter.completedLFunction χ s = 0 := by
      rw [dirichletCompletedLFunction_eq_multiplicityHadamardProduct_mul_entireQuotient χ hne z w s
          hprimitive,
        hzero]
      simp only [mul_zero]
    exact
      hmem
        (mem_dirichletCompletedLFunctionZerosInRectangle_iff.mpr
          ⟨hs, hcompleted⟩)

/-- For a character at a positive level and a complex point, define the natural-valued analytic
order of its ordinary `L`-function using `analyticOrderNatAt`. The definition is total, including
at infinite analytic order. For nontrivial characters the order is finite, and at zeros it is
positive; the following theorems use it in local factorizations and logarithmic residues. -/
noncomputable def dirichletLFunctionZeroMultiplicity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/--
Input/assumptions: a nontrivial character and one zero of its continued `L`-function.
Conclusion: the associated analytic multiplicity is positive.
Content: a zero has nonzero analytic order, while global nontriviality makes that order finite.
Role: records the positive integer coefficient of a primitive zero residue.
-/
theorem dirichletLFunctionZeroMultiplicity_pos {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {ρ : ℂ} (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    0 < dirichletLFunctionZeroMultiplicity χ ρ := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have horder : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    hanalytic.analyticOrderAt_ne_zero.mpr hzero
  have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hmero := hanalytic.meromorphicOrderAt_eq
    rw [htop] at hmero
    exact
      meromorphicOrderAt_dirichletLFunction_ne_top
        χ hχ ρ (by simpa only [ENat.map_top] using hmero)
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  apply Nat.pos_of_ne_zero
  intro hmult
  apply horder
  rw [← hcast, show analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 0 from hmult]
  simp only [CharP.cast_eq_zero]

/--
Input/assumptions: a nontrivial character and a complex point.
Conclusion: a local analytic factorization of its continued `L`-function at that point.
Content: finite analytic order extracts a nonvanishing analytic factor after the vanishing power.
Role: this is the local input for proving the logarithmic-derivative residue formula at a zero.
-/
theorem exists_dirichletLFunction_localFactor {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (ρ : ℂ) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        DirichletCharacter.LFunction χ =ᶠ[nhds ρ] fun s ↦
          (s - ρ) ^ dirichletLFunctionZeroMultiplicity χ ρ • g s := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hmero := hanalytic.meromorphicOrderAt_eq
    rw [htop] at hmero
    exact
      meromorphicOrderAt_dirichletLFunction_ne_top
        χ hχ ρ (by simpa only [ENat.map_top] using hmero)
  simpa only [dirichletLFunctionZeroMultiplicity] using hanalytic.analyticOrderAt_ne_top.mp hfinite

/--
Input/assumptions: a nontrivial character and one zero of its (uncompleted) `L`-function.
Conclusion: near that zero its logarithmic derivative is multiplicity over `s - ρ` plus an
analytic logarithmic derivative.
Content: differentiate the finite-order local factorization and use product logarithmic-derivative
rules away from the center.
Role: the local identity from which a contour kernel's principal part at an `L`-zero is obtained.
-/
theorem exists_eventuallyEq_logDeriv_dirichletLFunction_at_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ g : ℂ → ℂ,
      0 < dirichletLFunctionZeroMultiplicity χ ρ ∧
        AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ))
          (logDeriv (DirichletCharacter.LFunction χ))
          (fun s ↦ (dirichletLFunctionZeroMultiplicity χ ρ : ℂ) / (s - ρ) + logDeriv g s) := by
  obtain ⟨g, hganalytic, hgzero, hfactor⟩ := exists_dirichletLFunction_localFactor hχ ρ
  refine ⟨g, dirichletLFunctionZeroMultiplicity_pos hχ hzero, hganalytic, hgzero, ?_⟩
  have hlog :
    Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) (logDeriv (DirichletCharacter.LFunction χ))
      (logDeriv fun s ↦ (s - ρ) ^ dirichletLFunctionZeroMultiplicity χ ρ • g s) :=
    (logDeriv_congr_nhds hfactor).filter_mono nhdsWithin_le_nhds
  have hganalyticEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), AnalyticAt ℂ g s :=
    hganalytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hgzeroEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), g s ≠ 0 :=
    ((hganalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hgzero).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hlog, hganalyticEventually, hgzeroEventually, eventually_mem_nhdsWithin] with s
    hlogs hsanalytic hgs hsρ
  simp only [smul_eq_mul] at hlogs
  rw [hlogs]
  change logDeriv ((fun s ↦ (s - ρ) ^ dirichletLFunctionZeroMultiplicity χ ρ) * g) s = _
  rw [logDeriv_mul s]
  · rw [logDeriv_fun_pow (by fun_prop)]
    simp only [logDeriv_apply]
    rw [deriv_sub_const]
    simp only [deriv_id'', one_div, add_left_inj]
    ring
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsρ))
  · exact hgs
  · fun_prop
  · exact hsanalytic.differentiableAt

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
