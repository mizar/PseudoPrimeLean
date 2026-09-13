import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Agreement of a character and its primitive source under equal prime support -/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The level and conductor have the same prime support. -/
def ConductorPrimeSupport {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ q → p ∣ χ.conductor

/-- Equal prime support makes an induced character agree everywhere with its primitive source. -/
theorem apply_eq_primitiveCharacter_of_conductorPrimeSupport {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hsupport : ConductorPrimeSupport χ) : χ n = χ.primitiveCharacter n := by
  by_cases hconductor : Nat.Coprime n χ.conductor
  · apply
      apply_eq_primitiveCharacter_of_coprime_quotient
    by_contra hquotient
    obtain ⟨p, hp, hpn, hpquotient⟩ := Nat.Prime.not_coprime_iff_dvd.mp hquotient
    have hpq : p ∣ q := hpquotient.trans (Nat.div_dvd_of_dvd χ.conductor_dvd_level)
    have hpconductor : p ∣ χ.conductor := hsupport p hp hpq
    exact (hp.coprime_iff_not_dvd.mp (hconductor.of_dvd_left hpn)) hpconductor
  · have hlevel : ¬Nat.Coprime n q := by
      intro hnq
      exact hconductor (hnq.of_dvd_right χ.conductor_dvd_level)
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hlevel)
    have hprimitiveZero : χ.primitiveCharacter n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ.primitiveCharacter (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hconductor)
    rw [hχzero, hprimitiveZero]

/-- Equal prime support removes the conductor-quotient error from the reciprocal sum. -/
theorem characterReciprocalWeightedSum_eq_primitive_of_conductorPrimeSupport {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hsupport : ConductorPrimeSupport χ) :
    characterReciprocalWeightedSum x χ =
      characterReciprocalWeightedSum x
        χ.primitiveCharacter := by
  rw [characterReciprocalWeightedSum,
    characterReciprocalWeightedSum]
  apply Finset.sum_congr rfl
  intro n _
  rw [characterReciprocalWeightedTerm,
    characterReciprocalWeightedTerm,
    apply_eq_primitiveCharacter_of_conductorPrimeSupport χ hsupport]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
