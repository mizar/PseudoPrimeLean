/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Primitivity is preserved under inversion

Pure `DirichletCharacter`/`MulChar` algebra, independent of analytic estimates:
`χ.IsPrimitive → χ⁻¹.IsPrimitive`, `χ⁻¹ a = conj (χ a)`, and the resulting parity
invariance `χ⁻¹.Even ↔ χ.Even` / `χ⁻¹.Odd ↔ χ.Odd`. None of this mentions `completedLFunction`
or GRH — it holds for a `DirichletCharacter` valued in any `CommMonoidWithZero` (for the
conductor/primitivity facts) or in `ℂ` (for the conjugation/parity facts).
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: a Dirichlet character `χ` valued in a commutative monoid with zero,
factoring through level `d`.
Conclusion: `χ⁻¹` also factors through level `d`.
Content: `χ.FactorsThrough d` unpacks to `χ = changeLevel h χ₀` for some `χ₀` at level `d`;
`changeLevel h` is a `MonoidHom` between the (commutative-group) `MulChar` types, so it commutes
with `⁻¹` (`map_inv`), giving `χ⁻¹ = changeLevel h χ₀⁻¹`.
Role: the key step for `χ.IsPrimitive → χ⁻¹.IsPrimitive`, needed to state a symmetric
`DirichletLFunction.primitiveBRe`
conclusion for the pair `(χ, χ⁻¹)` without an extra primitivity hypothesis on `χ⁻¹`.
-/
theorem DirichletCharacter.factorsThrough_inv {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    {χ : DirichletCharacter R n} {d : ℕ} (h : χ.FactorsThrough d) : χ⁻¹.FactorsThrough d := by
  obtain ⟨hd, χ₀, hχeq⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχeq, map_inv]⟩

/--
Input/assumptions: a Dirichlet character valued in a commutative monoid with zero.
Conclusion: `χ⁻¹` and `χ` have the same conductor set, hence the same conductor.
Content: `DirichletLFunction.DirichletCharacter.factorsThrough_inv` applied to both `χ` and `χ⁻¹`
(with `inv_inv`)
gives the conductor-set equality termwise; `conductor` is `sInf` of the conductor set.
-/
theorem DirichletCharacter.conductor_inv_eq {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    (χ : DirichletCharacter R n) : χ⁻¹.conductor = χ.conductor := by
  have hset : χ⁻¹.conductorSet = χ.conductorSet := by
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    exact
      ⟨fun h => by
        simpa only [inv_inv] using
          DirichletCharacter.factorsThrough_inv
            h,
        DirichletCharacter.factorsThrough_inv⟩
  unfold DirichletCharacter.conductor
  rw [hset]

/--
Input/assumptions: a primitive Dirichlet character valued in a commutative monoid with zero.
Conclusion: `χ⁻¹` is also primitive.
Content: `IsPrimitive` unfolds to `conductor = n`; `conductor_inv_eq` transports this from `χ` to
`χ⁻¹`.
Role: removes the need for a separate `χ⁻¹.IsPrimitive` hypothesis wherever the pair `(χ, χ⁻¹)`
must both be treated as primitive characters of the same level.
-/
theorem DirichletCharacter.isPrimitive_inv {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    {χ : DirichletCharacter R n} (hprimitive : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def] at hprimitive ⊢
  rwa [DirichletCharacter.conductor_inv_eq]

/--
Input/assumptions: a positive level `N` and a complex Dirichlet character `χ` of level `N`.
Conclusion: `χ⁻¹ a = conj (χ a)` for every `a : ZMod N`.
Content: `MulChar.star_apply'` (`star (χ a) = χ⁻¹ a` for a `MulChar R ℂ` with `Finite Rˣ`)
specialized to `R := ZMod N` (finite units since `NeZero N`), noting `star = starRingEnd ℂ` on `ℂ`.
Role: the algebraic conjugation identity feeding parity invariance and, eventually, the
completed-`L` conjugation symmetry at `s = 0`.
-/
theorem DirichletCharacter.inv_apply_eq_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a : ZMod N) : χ⁻¹ a = starRingEnd ℂ (χ a) :=
  (MulChar.star_apply' χ a).symm

/--
Input/assumptions: a positive level `N` and a complex Dirichlet character `χ` of level `N`.
Conclusion: `χ⁻¹.Even ↔ χ.Even`.
Content: `χ.Even` unfolds to `χ (-1) = 1`; applying `inv_apply_eq_conj` at `a := -1` turns
`χ⁻¹ (-1) = 1` into `conj (χ (-1)) = 1`, equivalent to `χ (-1) = 1` since `conj` is injective and
fixes `1`.
Role: feeds `gammaFactor_inv_eq` (the conjugation step), since `gammaFactor` depends on `χ` only
through parity.
-/
theorem DirichletCharacter.even_inv_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} :
    χ⁻¹.Even ↔ χ.Even := by
  unfold DirichletCharacter.Even
  rw [DirichletCharacter.inv_apply_eq_conj]
  constructor
  · intro h
    have := congrArg (starRingEnd ℂ) h
    simpa only [RingHomCompTriple.comp_apply, RingHom.id_apply, map_one] using this
  · intro h
    rw [h]
    simp only [map_one]

/--
Input/assumptions: a positive level `N` and a complex Dirichlet character `χ` of level `N`.
Conclusion: `χ⁻¹.Odd ↔ χ.Odd`.
Content: identical to `even_inv_iff`, using `χ (-1) = -1` instead of `= 1`.
-/
theorem DirichletCharacter.odd_inv_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} :
    χ⁻¹.Odd ↔ χ.Odd := by
  unfold DirichletCharacter.Odd
  rw [DirichletCharacter.inv_apply_eq_conj]
  constructor
  · intro h
    have := congrArg (starRingEnd ℂ) h
    simpa only [RingHomCompTriple.comp_apply, RingHom.id_apply, map_neg, map_one] using this
  · intro h
    rw [h]
    simp only [map_neg, map_one]

/--
Input/assumptions: a complex Dirichlet character of a nonzero level.
Conclusion: quadraticity is invariant under inversion.
Content: `MulChar.IsQuadratic.inv` identifies a quadratic character with its inverse, and the
same identity applied to the inverse gives the converse transport.
Role: supplies the general self-duality API used by quadratic specializations of the functional
equation without importing an application-specific character construction.
-/
theorem DirichletCharacter.isQuadratic_inv_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} :
    χ⁻¹.IsQuadratic ↔ χ.IsQuadratic := by
  constructor
  · intro h
    have hi' : χ = χ⁻¹ := by simpa only [inv_inv] using h.inv
    have hi : χ⁻¹ = χ := hi'.symm
    rw [← hi]
    exact h
  · intro h
    have hi : χ⁻¹ = χ := by simpa only [inv_inv] using h.inv
    rw [hi]
    exact h

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
