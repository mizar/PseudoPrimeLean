/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AffineConductorLogBounds
public import PseudoPrime.LLS.Theorem11S1Subgroup
public import PseudoPrime.Analysis.SignedHalfPowerBudget

/-! # Signed half-scale comparisons and conditional power-bound transfers -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a character χ, excluded integer m and scale parameters, assume that
absence of a non-one prime through Y=CL^a yields some X in [θY,Y] with signed
half-difference at most C₁sqrt(X)L^(1-δ)+C₂sqrt(X). This is an explicit analytic
input proposition, not a consequence of RH or GRH proved in this file. -/
def SignedHalfPowerWindow {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) (L a δ C θ C₁ C₂ : ℝ) :
    Prop :=
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ C * L ^ a → ¬p ∣ m → χ p = 1) →
    ∃ X : ℝ,
      θ * (C * L ^ a) ≤ X ∧
        X ≤ C * L ^ a ∧
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X χ -
              AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (X / 2) χ).re ≤
          C₁ * Real.sqrt X * L ^ (1 - δ) + C₂ * Real.sqrt X

/-- Under RH and X≥200, absence of a non-one prime outside m≠0 forces the
signed half-scale comparison with bounded prime exclusion cost 2log(2)E(m).
Combine the principal lower bound and the 18sqrt(X) prime-power tail, retaining
the actual real character difference. No character GRH or norm cap is assumed. -/
theorem log_half_no_witness_signed_comparison {q m : ℕ} (χ : DirichletCharacter ℂ q)
    (hRH : RiemannHypothesis) (hm : m ≠ 0) {X : ℝ} (hX : 200 ≤ X)
    (hno : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → ¬p ∣ m → χ p = 1) :
    X / 2 ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X χ -
            AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (X / 2) χ).re +
        ((1 / 2 : ℝ) + 36 * Real.log 2) * Real.sqrt X +
        2 * Real.log 2 * (∑ p ∈ m.primeFactors, Real.log p) := by
  have hX0 : 0 < X := by linarith only [hX]
  have hb :=
    AnalyticNumberTheory.Arithmetic.log_difference_prime_exclusion χ hm
      (div_pos hX0 (by norm_num only : (0 : ℝ) < 2)) (show X / 2 ≤ X by linarith only [hX0]) hno
  have hr : X / (X / 2) = 2 := by field_simp [hX0.ne']
  rw [hr] at hb
  have hP := principal_log_half_difference_lower_half_sqrt hRH hX
  have ht := psi_sub_theta_le_eighteen_sqrt (show 1 ≤ X by linarith only [hX])
  have hs :=
    mul_le_mul_of_nonneg_left ht
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)))
  nlinarith only [hb, hP, hs]

/-- Under RH, a strict signed half-scale gap at X≥200 yields a non-one prime
outside m≠0 through X. Contradict the no-witness signed comparison.
This extracts actual primes without discarding phase information. -/
theorem exists_prime_ne_one_of_signed_half_gap {q m : ℕ} (χ : DirichletCharacter ℂ q)
    (hRH : RiemannHypothesis) (hm : m ≠ 0) {X : ℝ} (hX : 200 ≤ X)
    (hgap :
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X χ -
              AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (X / 2) χ).re +
          ((1 / 2 : ℝ) + 36 * Real.log 2) * Real.sqrt X +
          2 * Real.log 2 * (∑ p ∈ m.primeFactors, Real.log p) <
        X / 2) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ X) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hv
    exact hnone ⟨p, hp, hb, hd, hv⟩
  exact (log_half_no_witness_signed_comparison χ hRH hm hX hno).not_gt hgap

/-- Under RH, if no witness through Y forces a strict gap at a scale in
[θY,Y] with θY≥200, a non-one prime outside m≠0 exists through Y.
Use the lower endpoint for validity and the upper endpoint for the final bound. -/
theorem exists_prime_ne_one_le_of_signed_half_window {q m : ℕ} (χ : DirichletCharacter ℂ q)
    (hRH : RiemannHypothesis) (hm : m ≠ 0) {Y θ : ℝ} (hsmall : 200 ≤ θ * Y)
    (hwindow :
      (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → ¬p ∣ m → χ p = 1) →
        ∃ X : ℝ,
          θ * Y ≤ X ∧
            X ≤ Y ∧
            (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X χ -
                    AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (X / 2) χ).re +
                ((1 / 2 : ℝ) + 36 * Real.log 2) * Real.sqrt X +
                2 * Real.log 2 * (∑ p ∈ m.primeFactors, Real.log p) <
              X / 2) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ Y ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ Y) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hv
    exact hnone ⟨p, hp, hb, hd, hv⟩
  obtain ⟨X, hlow, hupp, hgap⟩ := hwindow hno
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    exists_prime_ne_one_of_signed_half_gap χ hRH hm (hsmall.trans hlow) hgap
  exact hnone ⟨p, hp, hb.trans hupp, hd, hv⟩

/-- Under RH, nonnegative L,C₁,C₂, a bounded exclusion cost and the strict
power budget, the signed power-window hypothesis yields a prime outside m≠0
through CL^a. Increase square roots only after keeping the signed upper bound.
This is the finite-scale transfer of the proposed analytic estimate. -/
theorem exists_prime_ne_one_le_of_signed_half_power_window {q m : ℕ} (χ : DirichletCharacter ℂ q)
    (hRH : RiemannHypothesis) (hm : m ≠ 0) {L a δ C θ C₁ C₂ Cₘ : ℝ} (hL : 0 ≤ L) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hsmall : 200 ≤ θ * (C * L ^ a))
    (hE : (∑ p ∈ m.primeFactors, Real.log p) ≤ Cₘ * L)
    (hbudget :
      C₁ * Real.sqrt (C * L ^ a) * L ^ (1 - δ) +
          (C₂ + ((1 / 2 : ℝ) + 36 * Real.log 2)) * Real.sqrt (C * L ^ a) +
          2 * Real.log 2 * Cₘ * L <
        θ * (C * L ^ a) / 2)
    (hwindow :
      (∀ p : ℕ, p.Prime → (p : ℝ) ≤ C * L ^ a → ¬p ∣ m → χ p = 1) →
        ∃ X : ℝ,
          θ * (C * L ^ a) ≤ X ∧
            X ≤ C * L ^ a ∧
            (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X χ -
                  AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (X / 2) χ).re ≤
              C₁ * Real.sqrt X * L ^ (1 - δ) + C₂ * Real.sqrt X) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * L ^ a ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  apply exists_prime_ne_one_le_of_signed_half_window χ hRH hm hsmall
  intro hno
  obtain ⟨X, hlow, hupp, hphase⟩ := hwindow hno
  have hs := Real.sqrt_le_sqrt hupp
  have hcoef : 0 ≤ C₁ * L ^ (1 - δ) + C₂ + ((1 / 2 : ℝ) + 36 * Real.log 2) := by
    have hp := Real.rpow_nonneg hL (1 - δ)
    nlinarith only [hC₁, hC₂, hp, Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)]
  have hmS := mul_le_mul_of_nonneg_left hs hcoef
  have hmE :=
    mul_le_mul_of_nonneg_left hE
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)))
  refine ⟨X, hlow, hupp, ?_⟩
  nlinarith only [hphase, hmS, hmE, hbudget, hlow]

/-- Fix a>1, 1-δ<a/2, C,θ>0 and C₁,C₂≥0. Under RH, one eventual range of L
works for every character, level and nonzero exclusion m with E(m)≤CₘL:
the explicit signed-window hypothesis gives a non-one prime through CL^a.
Combine the scalar eventual budget and the finite transfer; the phase hypothesis remains. -/
theorem eventually_exists_prime_ne_one_of_signed_half_power_window {a δ C θ C₁ C₂ Cₘ : ℝ}
    (ha : 1 < a) (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ L : ℝ in Filter.atTop,
      ∀ (q m : ℕ) (χ : DirichletCharacter ℂ q),
        m ≠ 0 →
          (∑ p ∈ m.primeFactors, Real.log p) ≤ Cₘ * L →
          ((∀ p : ℕ, p.Prime → (p : ℝ) ≤ C * L ^ a → ¬p ∣ m → χ p = 1) →
            ∃ X : ℝ,
              θ * (C * L ^ a) ≤ X ∧
                X ≤ C * L ^ a ∧
                (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X χ -
                      AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (X / 2) χ).re ≤
                  C₁ * Real.sqrt X * L ^ (1 - δ) + C₂ * Real.sqrt X) →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * L ^ a ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  have hb :=
    Analysis.eventually_signed_half_power_budget (C₁ := C₁) (C₂ := C₂) (Cₘ := Cₘ) ha hδ hC hθ
  filter_upwards [hb, Filter.eventually_ge_atTop (0 : ℝ)] with L hbudget hL
  intro q m χ hm hE hwindow
  exact
    exists_prime_ne_one_le_of_signed_half_power_window χ hRH hm hL hC₁ hC₂ hbudget.1 hE hbudget.2
      hwindow

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under RH and the fixed power-parameter inequalities, one eventual range
of L works for all levels and characters whose original-level cost is at most
CₘL. A signed-window input for the primitive character gives an original-level
unit-prime non-one witness. Transfer the primitive value on coprime primes. -/
theorem eventually_exists_unit_prime_of_signed_half_power_window {a δ C θ C₁ C₂ Cₘ : ℝ} (ha : 1 < a)
    (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ L : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (∑ p ∈ q.primeFactors, Real.log p) ≤ Cₘ * L →
          PaperStatements.SignedHalfPowerWindow χ.primitiveCharacter q L a δ C θ C₁ C₂ →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * L ^ a ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  have h :=
    PaperStatements.eventually_exists_prime_ne_one_of_signed_half_power_window (Cₘ := Cₘ) ha hδ hC
      hθ hC₁ hC₂ hRH
  filter_upwards [h] with L hL
  intro q _ χ hE hw
  obtain ⟨p, hp, hb, hd, hv⟩ := hL χ.conductor q χ.primitiveCharacter (NeZero.ne q) hE hw
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under RH and fixed power parameters, the primitive signed-window input
and E(q)≤CₘL give a unit-prime outside any subgroup on which χ is trivial.
Transfer the character non-one value to nonmembership; the start is uniform. -/
theorem eventually_exists_prime_outside_of_signed_half_power_window {a δ C θ C₁ C₂ Cₘ : ℝ}
    (ha : 1 < a) (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
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
  have h :=
    eventually_exists_unit_prime_of_signed_half_power_window (Cₘ := Cₘ) ha hδ hC hθ hC₁ hC₂ hRH
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
theorem eventually_exists_unit_prime_log_power_of_signed_half_window {a δ C θ C₁ C₂ : ℝ}
    (ha : 1 < a) (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
        PaperStatements.SignedHalfPowerWindow χ.primitiveCharacter q (Real.log q) a δ C θ C₁ C₂ →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * (Real.log q) ^ a ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  have h :=
    eventually_exists_unit_prime_of_signed_half_power_window (Cₘ := 1) ha hδ hC hθ hC₁ hC₂ hRH
  have hlog : Filter.Tendsto (fun q : ℕ ↦ Real.log q) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually h] with q hq
  intro _ χ hw
  have hE := AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log (NeZero.ne q)
  exact hq q χ (by simpa only [one_mul] using hE) hw

/-- Under RH and fixed power parameters, for every sufficiently large q the
primitive signed-window hypothesis gives a prime outside a subgroup on which
χ is trivial, through C(log q)^a and coprime to q. Transfer the unit-prime theorem. -/
theorem eventually_exists_prime_outside_log_power_of_signed_half_window {a δ C θ C₁ C₂ : ℝ}
    (ha : 1 < a) (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ [NeZero q] (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q),
        (∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1) →
          PaperStatements.SignedHalfPowerWindow χ.primitiveCharacter q (Real.log q) a δ C θ C₁ C₂ →
          ∃ p : ℕ,
            p.Prime ∧
              (p : ℝ) ≤ C * (Real.log q) ^ a ∧
              ¬p ∣ q ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  have h := eventually_exists_unit_prime_log_power_of_signed_half_window ha hδ hC hθ hC₁ hC₂ hRH
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
theorem eventually_exists_prime_outside_proper_subgroup_of_signed_half_windows {a δ C θ C₁ C₂ : ℝ}
    (ha : 1 < a) (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
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
  have h := eventually_exists_prime_outside_log_power_of_signed_half_window ha hδ hC hθ hC₁ hC₂ hRH
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
