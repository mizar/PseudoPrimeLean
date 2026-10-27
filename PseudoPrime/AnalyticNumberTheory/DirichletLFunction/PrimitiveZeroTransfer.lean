/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting

/-! # Transfer of Dirichlet L-function zeros to primitive characters -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Inputs: a Dirichlet character, a prime, and a complex point with positive real part.

Claim: the local Euler factor at the prime is nonzero.

Proof: the character value has norm at most one, while the prime power has norm strictly below
one when the real part is positive.

Role: excludes zeros contributed by the finite Euler factors when a character is induced to a
larger modulus.
-/
theorem dirichletLFactor_ne_zero_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) : 1 - χ (p : ZMod q) * (p : ℂ) ^ (-s) ≠ 0 := by
  classical
  intro hzero
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [show (p : ℂ) = (p : ℝ) from (Complex.ofReal_natCast p).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hpR), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (neg_neg_of_pos hs)
  have hchi : ‖χ (p : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hprod : ‖χ (p : ZMod q) * (p : ℂ) ^ (-s)‖ < 1 :=
    calc
      ‖χ (p : ZMod q) * (p : ℂ) ^ (-s)‖ ≤ ‖χ (p : ZMod q)‖ * ‖(p : ℂ) ^ (-s)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := mul_le_mul_of_nonneg_right hchi (norm_nonneg _)
      _ < 1 := by simpa only [one_mul] using hpow
  have hval : χ (p : ZMod q) * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm : ‖χ (p : ZMod q) * (p : ℂ) ^ (-s)‖ = 1 := by rw [hval, norm_one]
  exact (ne_of_gt hprod) hnorm.symm

/--
Inputs: a Dirichlet character, a natural-number level whose prime divisors index the correction
factors, and a complex point with positive real part.

Claim: the product of its level correction factors over the prime divisors of the modulus is
nonzero.

Proof: every factor is nonzero by `dirichletLFactor_ne_zero_of_re_pos`; apply the finite-product
nonvanishing criterion.

Role: supplies the nonzero correction factor for the change-of-level formula of Dirichlet
L-functions.
-/
theorem dirichletLFactorProduct_ne_zero_of_re_pos {q N : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : (∏ p ∈ N.primeFactors, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-s))) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact dirichletLFactor_ne_zero_of_re_pos χ (Nat.prime_of_mem_primeFactors hp) hs

/--
Inputs: a nontrivial Dirichlet character at positive level and a point in the right half-plane.

Claim: the ordinary L-function vanishes at that point exactly when the L-function of the
associated primitive character does.

Proof: use the change-of-level Euler factorization and the nonvanishing of each finite correction
factor.

Role: transfers zero counting from characters of arbitrary level to primitive characters.
-/
theorem LFunction_zero_iff_primitive_of_re_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    DirichletCharacter.LFunction χ s = 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  classical
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
        (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
      _ = DirichletCharacter.changeLevel χ.conductor_dvd_level 1 := congrArg _ h
      _ = 1 := (DirichletCharacter.changeLevel_eq_one_iff χ.conductor_dvd_level).mpr rfl
  have heuler :=
    @DirichletCharacter.LFunction_changeLevel χ.conductor q ⟨DirichletCharacter.conductor_ne_zero χ⟩
      (inferInstance : NeZero q) χ.conductor_dvd_level χ.primitiveCharacter (s := s) (Or.inl hprim)
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at heuler
  have hprod := dirichletLFactorProduct_ne_zero_of_re_pos (N := q) χ.primitiveCharacter hs
  constructor
  · intro hzero
    rw [heuler] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right hprod
  · intro hzero
    rw [heuler, hzero, zero_mul]

/--
Inputs: a complex Dirichlet character and a point with positive real part.

Claim: the character's gamma factor is nonzero at the point.

Proof: split by parity; each gamma factor is a real gamma function at an argument with positive
real part.

Role: lets zero counting pass between the completed and ordinary Dirichlet L-functions in the
region used by the density estimate.
-/
theorem dirichletCharacter_gammaFactor_ne_zero_of_pos_re {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [ho.gammaFactor_def]
    exact
      Complex.Gammaℝ_ne_zero_of_re_pos
        (show 0 < (s + 1).re by
          rw [Complex.add_re, Complex.one_re]
          linarith only [hs])

/--
Inputs: a Dirichlet character modulo a positive integer and a complex point with positive real
part.

Claim: the completed and ordinary L-functions vanish at the same points in this region.

Proof: use the completed-to-ordinary identity and the nonzero gamma factor.

Role: converts the ordinary zero transfer under change of level into a completed-zero transfer.
-/
theorem completedLFunction_zero_iff_LFunction_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    exact (ne_of_gt hs) hre
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hgamma := dirichletCharacter_gammaFactor_ne_zero_of_pos_re χ hs
  constructor
  · intro hz
    rw [hdiv, hz, zero_div]
  · intro hz
    rw [hdiv] at hz
    by_contra hne
    exact (div_ne_zero hne hgamma) hz

/--
Inputs: a nontrivial Dirichlet character at positive level and a point with positive real part.

Claim: its completed L-function vanishes exactly when the completed L-function of its primitive
character does.

Proof: transfer zeros between completed and ordinary L-functions using the nonzero gamma factors,
then apply the change-of-level zero equivalence.

Role: reduces completed zero counting for nontrivial characters to the primitive family.
-/
theorem completedLFunction_zero_iff_primitive_of_re_pos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    DirichletCharacter.completedLFunction χ s = 0 ↔
      DirichletCharacter.completedLFunction χ.primitiveCharacter s = 0 := by
  classical
  have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprimCompleted :=
    @completedLFunction_zero_iff_LFunction_of_re_pos χ.conductor hcond χ.primitiveCharacter s hs
  calc
    _ ↔ DirichletCharacter.LFunction χ s = 0 := completedLFunction_zero_iff_LFunction_of_re_pos χ hs
    _ ↔ DirichletCharacter.LFunction χ.primitiveCharacter s = 0 :=
      LFunction_zero_iff_primitive_of_re_pos hχ hs
    _ ↔ DirichletCharacter.completedLFunction χ.primitiveCharacter s = 0 := hprimCompleted.symm

/--
Inputs: a nonprincipal character and a complex point with positive real part.

Claim: the analytic orders of its completed and ordinary Dirichlet L-functions are equal.

Proof: the reciprocal gamma factor is entire and nonzero in this region. The completed-to-ordinary
identity then expresses the ordinary L-function locally as the completed function times this
analytic unit.

Role: reduces completed zero multiplicities to ordinary L-function multiplicities.
-/
theorem completedLFunction_analyticOrderAt_eq_LFunction_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) s =
      analyticOrderAt (DirichletCharacter.LFunction χ) s := by
  classical
  let G : ℂ → ℂ := fun z => (DirichletCharacter.gammaFactor χ z)⁻¹
  have hGdiff : Differentiable ℂ G := by
    rcases χ.even_or_odd with he | ho
    · simpa only [G, he.gammaFactor_def] using Complex.differentiable_Gammaℝ_inv
    · have hshift : Differentiable ℂ (fun z : ℂ => z + 1) := differentiable_id.add_const 1
      have hgammaInv : Differentiable ℂ (fun z : ℂ => (Complex.Gammaℝ (z + 1))⁻¹) :=
        Complex.differentiable_Gammaℝ_inv.comp hshift
      simpa only [G, ho.gammaFactor_def] using hgammaInv
  have hGanalytic : AnalyticAt ℂ G s := hGdiff.analyticAt s
  have hGzero : G s ≠ 0 := inv_ne_zero (dirichletCharacter_gammaFactor_ne_zero_of_pos_re χ hs)
  have hGorder : analyticOrderAt G s = 0 := hGanalytic.analyticOrderAt_eq_zero.mpr hGzero
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    exact (ne_of_gt hs) hre
  have hevent :
    DirichletCharacter.LFunction χ =ᶠ[nhds s] fun z =>
      DirichletCharacter.completedLFunction χ z * G z := by
    filter_upwards [eventually_ne_nhds hs0] with z hz
    have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz)
    rw [hdiv, div_eq_mul_inv]
  have horderProd :
    analyticOrderAt (fun z => DirichletCharacter.completedLFunction χ z * G z) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) s := by
    change
      analyticOrderAt (DirichletCharacter.completedLFunction χ * G) s =
        analyticOrderAt (DirichletCharacter.completedLFunction χ) s
    rw [analyticOrderAt_mul ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s)
        hGanalytic]
    rw [hGorder, add_zero]
  exact ((analyticOrderAt_congr hevent).trans horderProd).symm

/--
Inputs: a nonprincipal character, a nonzero conductor instance, and a complex point.

Claim: the analytic orders of the ordinary L-functions of a character and its primitive character
are equal.

Proof: factor the change-of-level identity into the primitive L-function and the finite Euler
product. In the positive-real-part region, the Euler product is analytic and nonzero, so its
analytic order is zero.

Role: transfers analytic multiplicity, rather than only zero locations, to the primitive family.
-/
theorem LFunction_analyticOrderAt_eq_primitive_of_re_pos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) [NeZero χ.conductor] {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (DirichletCharacter.LFunction χ) s =
      analyticOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) s := by
  classical
  let factor : ℕ → ℂ → ℂ := fun p z =>
    1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z)
  let F : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, factor p z
  have hfactor : ∀ p ∈ q.primeFactors, AnalyticAt ℂ (factor p) s := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpPrime.pos
    have hpSlit : (p : ℂ) ∈ Complex.slitPlane := by
      rw [← Complex.ofReal_natCast]
      exact Complex.ofReal_mem_slitPlane.mpr hpR
    have hpNe : NeZero p := ⟨hpPrime.ne_zero⟩
    dsimp only [factor]
    fun_prop
  have hprod :
    ∀ S : Finset ℕ,
      (∀ p ∈ S, AnalyticAt ℂ (factor p) s) → AnalyticAt ℂ (fun z ↦ ∏ p ∈ S, factor p z) s := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using analyticAt_const (𝕜 := ℂ) (E := ℂ)
    | @insert p S hp
      ih =>
      have heq :
        (fun z ↦ ∏ r ∈ insert p S, factor r z) =
          (fun z ↦ factor p z) * (fun z ↦ ∏ r ∈ S, factor r z) := by
        funext z
        rw [Finset.prod_insert hp]
        rfl
      rw [heq]
      exact
        (hS p (Finset.mem_insert_self p S)).mul (ih (fun r hr ↦ hS r (Finset.mem_insert_of_mem hr)))
  have hFanalytic : AnalyticAt ℂ F s := by
    dsimp only [F]
    exact hprod q.primeFactors hfactor
  have hFzero : F s ≠ 0 := by
    simpa only [F, factor] using
      dirichletLFactorProduct_ne_zero_of_re_pos (N := q) χ.primitiveCharacter hs
  have hForder : analyticOrderAt F s = 0 := hFanalytic.analyticOrderAt_eq_zero.mpr hFzero
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
        (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
      _ = DirichletCharacter.changeLevel χ.conductor_dvd_level 1 := congrArg _ h
      _ = 1 := (DirichletCharacter.changeLevel_eq_one_iff χ.conductor_dvd_level).mpr rfl
  have hfunc :
    DirichletCharacter.LFunction χ = DirichletCharacter.LFunction χ.primitiveCharacter * F := by
    funext z
    change
      DirichletCharacter.LFunction χ z = DirichletCharacter.LFunction χ.primitiveCharacter z * F z
    have heuler :=
      DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (s := z)
        (Or.inl hprim)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at heuler
    simpa only [F, factor] using heuler
  rw [hfunc]
  rw [analyticOrderAt_mul ((DirichletCharacter.differentiable_LFunction hprim).analyticAt s)
      hFanalytic]
  rw [hForder, add_zero]

/--
Inputs: a nonprincipal character, a nonzero conductor instance, and a complex point with positive
real part.

Claim: the completed L-functions of the character and its primitive character have equal analytic
orders at the point.

Proof: first transfer analytic order from each completed function to its ordinary L-function,
then use the nonvanishing analytic Euler product in the change-of-level formula.

Role: preserves multiplicity when reducing the completed zero count to primitive characters.
-/
theorem completedLFunction_analyticOrderAt_eq_primitive_of_re_pos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) [NeZero χ.conductor] {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) s := by
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
        (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
      _ = DirichletCharacter.changeLevel χ.conductor_dvd_level 1 := congrArg _ h
      _ = 1 := (DirichletCharacter.changeLevel_eq_one_iff χ.conductor_dvd_level).mpr rfl
  calc
    _ = analyticOrderAt (DirichletCharacter.LFunction χ) s :=
      completedLFunction_analyticOrderAt_eq_LFunction_of_re_pos χ hχ hs
    _ = analyticOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) s :=
      LFunction_analyticOrderAt_eq_primitive_of_re_pos hχ hs
    _ = analyticOrderAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) s :=
      (completedLFunction_analyticOrderAt_eq_LFunction_of_re_pos χ.primitiveCharacter hprim hs).symm

/--
Inputs: a nonprincipal character, a nonzero conductor instance, and a complex point with positive
real part.

Claim: the completed L-functions of the character and its primitive character have the same
natural-number analytic multiplicity at the point.

Proof: apply `ENat.toNat` to their equality of analytic orders.

Role: provides the exact multiplicity equality used by finite completed-zero counts.
-/
theorem completedLFunction_analyticOrderNatAt_eq_primitive_of_re_pos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) [NeZero χ.conductor] {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) s =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) s := by
  unfold analyticOrderNatAt
  exact congrArg ENat.toNat (completedLFunction_analyticOrderAt_eq_primitive_of_re_pos hχ hs)

/--
Inputs: a nonprincipal character, its primitive character, and parameters for a standard zero
region with positive left boundary and nonnegative height.

Claim: the completed zero counts of the character and its primitive character are equal, with
zeros counted by analytic multiplicity.

Proof: the region's zero ledgers are equal by the pointwise zero equivalence. Every point in the
region has positive real part, where the natural analytic multiplicities are equal.

Role: reduces finite zero counts over arbitrary levels to the corresponding primitive character.
-/
theorem completedZeroCount_eq_primitive_of_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) [NeZero χ.conductor] (hprim : χ.primitiveCharacter ≠ 1) {σ T : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hT : 0 ≤ T) :
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T =
      PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ.primitiveCharacter
        hprim σ T := by
  classical
  let Sχ :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZerosInRectangle χ hχ
      ((σ : ℂ) - T * Complex.I) ((1 : ℂ) + T * Complex.I)
  let Sprim :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZerosInRectangle
      χ.primitiveCharacter hprim ((σ : ℂ) - T * Complex.I) ((1 : ℂ) + T * Complex.I)
  have hsets : Sχ = Sprim := by
    ext ρ
    rw [PseudoPrime.AnalyticNumberTheory.DirichletLFunction.mem_completedZeroCountRegion_iff hσ1 hT,
      PseudoPrime.AnalyticNumberTheory.DirichletLFunction.mem_completedZeroCountRegion_iff hσ1 hT]
    constructor
    · rintro ⟨hlo, hhi, himlo, himhi, hz⟩
      exact
        ⟨hlo, hhi, himlo, himhi,
          (completedLFunction_zero_iff_primitive_of_re_pos hχ (lt_of_lt_of_le hσ hlo)).mp hz⟩
    · rintro ⟨hlo, hhi, himlo, himhi, hz⟩
      exact
        ⟨hlo, hhi, himlo, himhi,
          (completedLFunction_zero_iff_primitive_of_re_pos hχ (lt_of_lt_of_le hσ hlo)).mpr hz⟩
  unfold PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroMultiplicityCountInRectangle
  change
    (∑ ρ ∈ Sχ, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)) =
      ∑ ρ ∈ Sprim,
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ : ℝ)
  rw [hsets]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hm :=
    (PseudoPrime.AnalyticNumberTheory.DirichletLFunction.mem_completedZeroCountRegion_iff hσ1 hT).mp
      hρ
  rw [completedLFunction_analyticOrderNatAt_eq_primitive_of_re_pos hχ (lt_of_lt_of_le hσ hm.1)]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
