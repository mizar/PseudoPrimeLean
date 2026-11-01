/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.AffineConductorLogBounds
public import PseudoPrime.LLS.Theorem11S1Subgroup
public import PseudoPrime.Analysis.SignedHalfPowerBudget
public import PseudoPrime.LLS.PaperStatements.SignedHalfPowerWitnessBounds

/-! # Signed half-scale comparisons and conditional power-bound transfers -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and the fixed power-parameter inequalities, one eventual range
of L works for all levels and characters whose original-level cost is at most
CₘL. A signed-window input for the primitive character gives an original-level
unit-prime non-one witness. Transfer the primitive value on coprime primes. -/
theorem eventually_unit_prime_of_signed_window_RH {a δ C θ C₁ C₂ Cₘ : ℝ} (ha : 1 < a)
    (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ L : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (∑ p ∈ q.primeFactors, Real.log p) ≤ Cₘ * L →
          PaperStatements.SignedHalfPowerWindow χ.primitiveCharacter q L a δ C θ C₁ C₂ →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * L ^ a ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  have h := PaperStatements.eventually_prime_neOne_signedHalf_RH (Cₘ := Cₘ) ha hδ hC hθ hC₁ hC₂ hRH
  filter_upwards [h] with L hL
  intro q _ χ hE hw
  obtain ⟨p, hp, hb, hd, hv⟩ := hL χ.conductor q χ.primitiveCharacter (NeZero.ne q) hE hw
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under RH and fixed power parameters, the primitive signed-window input
and E(q)≤CₘL give a unit-prime outside any subgroup on which χ is trivial.
Transfer the character non-one value to nonmembership; the start is uniform. -/
theorem eventually_prime_outside_of_signed_window_RH {a δ C θ C₁ C₂ Cₘ : ℝ} (ha : 1 < a)
    (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ L : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q),
        (∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1) →
          (∑ p ∈ q.primeFactors, Real.log p) ≤ Cₘ * L →
          PaperStatements.SignedHalfPowerWindow χ.primitiveCharacter q L a δ C θ C₁ C₂ →
          ∃ p : ℕ,
            p.Prime ∧
              (p : ℝ) ≤ C * L ^ a ∧
              ¬p ∣ q ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  have h := eventually_unit_prime_of_signed_window_RH (Cₘ := Cₘ) ha hδ hC hθ hC₁ hC₂ hRH
  filter_upwards [h] with L hL
  intro q _ H χ ht hE hw
  obtain ⟨p, hp, hb, hd, hv⟩ := hL q χ hE hw
  refine ⟨p, hp, hb, hd, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

/-- Under RH and fixed power parameters, all sufficiently large levels q have
a unit-prime non-one witness through C(log q)^a whenever their primitive character
satisfies the explicit signed-window hypothesis. Use E(q)≤log(q) and the uniform
L theorem. This isolates the remaining phase estimate from the completed transfer. -/
theorem eventually_unit_prime_log_pow_signed_window_RH {a δ C θ C₁ C₂ : ℝ} (ha : 1 < a)
    (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
        PaperStatements.SignedHalfPowerWindow χ.primitiveCharacter q (Real.log q) a δ C θ C₁ C₂ →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * (Real.log q) ^ a ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  have h := eventually_unit_prime_of_signed_window_RH (Cₘ := 1) ha hδ hC hθ hC₁ hC₂ hRH
  have hlog : Filter.Tendsto (fun q : ℕ ↦ Real.log q) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually h] with q hq
  intro _ χ hw
  have hE := AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log (NeZero.ne q)
  exact hq q χ (by simpa only [one_mul] using hE) hw

/-- Under RH and fixed power parameters, for every sufficiently large q the
primitive signed-window hypothesis gives a prime outside a subgroup on which
χ is trivial, through C(log q)^a and coprime to q. Transfer the unit-prime theorem. -/
theorem eventually_prime_outside_log_pow_window_RH {a δ C θ C₁ C₂ : ℝ} (ha : 1 < a)
    (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ [NeZero q] (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q),
        (∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1) →
          PaperStatements.SignedHalfPowerWindow χ.primitiveCharacter q (Real.log q) a δ C θ C₁ C₂ →
          ∃ p : ℕ,
            p.Prime ∧
              (p : ℝ) ≤ C * (Real.log q) ^ a ∧
              ¬p ∣ q ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  have h := eventually_unit_prime_log_pow_signed_window_RH ha hδ hC hθ hC₁ hC₂ hRH
  filter_upwards [h] with q hq
  intro _ H χ ht hw
  obtain ⟨p, hp, hb, hd, hv⟩ := hq χ hw
  refine ⟨p, hp, hb, hd, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

/-- Under RH and fixed power parameters, a uniform signed-window input for
all nonprincipal characters yields a prime outside every proper subgroup at
all sufficiently large levels. Choose a nontrivial quotient character, pull it
back, and apply the completed character transfer. The phase input remains explicit. -/
theorem eventually_prime_outside_proper_of_windows_RH {a δ C θ C₁ C₂ : ℝ} (ha : 1 < a)
    (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ [NeZero q] (H : Subgroup (ZMod q)ˣ),
        H ≠ ⊤ →
          (∀ χ : DirichletCharacter ℂ q,
            χ ≠ 1 →
              PaperStatements.SignedHalfPowerWindow χ.primitiveCharacter q (Real.log q) a δ C θ C₁
                C₂) →
          ∃ p : ℕ,
            p.Prime ∧
              (p : ℝ) ≤ C * (Real.log q) ^ a ∧
              ¬p ∣ q ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  have h := eventually_prime_outside_log_pow_window_RH ha hδ hC hθ hC₁ hC₂ hRH
  filter_upwards [h] with q hq
  intro _ H hH hphase
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  exact
    hq H (pullbackCharacter χ') (fun _ hu ↦ pullbackCharacter_eq_one_of_mem χ' hu)
      (hphase (pullbackCharacter χ') (pullbackCharacter_ne_one_of_ne_one χ' hχ))

end PseudoPrime.LLS
