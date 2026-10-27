/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CorrelationTail
public import PseudoPrime.Analysis.CubicTailMoments

/-! # A 5/2 Heilbronn additive energy bound from correlation tails -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Map a residue parameter and a nonzero residue to the unit xi(tau)*T(g).
For prime p this parametrizes all units modulo p^2 and separates
principal and Teichmuller factors. -/
noncomputable def unitParameterMap {p : ℕ} [Fact p.Prime] (z : ZMod p × { g : ZMod p // g ≠ 0 }) :
    { c : ZMod (p ^ 2) // IsUnit c } :=
  ⟨principalShift p z.1 * teichLift p z.2.val,
    (principalShift_isUnit z.1).mul (teichLift_isUnit z.2.val z.2.property)⟩

/-- For prime p the principal-times-Teichmuller parameter map is bijective.
Reduction recovers g, cancellation and additive-lift injectivity recover tau;
the previously proved unit decomposition gives surjectivity. -/
theorem unitParameterMap_bijective {p : ℕ} [Fact p.Prime] :
    Function.Bijective (unitParameterMap (p := p)) := by
  constructor
  · rintro ⟨i, g, hg⟩ ⟨j, h, hh⟩ he
    have hv := congrArg Subtype.val he
    have hr := congrArg (squareReduction p) hv
    change
      squareReduction p (principalShift p i * teichLift p g) =
        squareReduction p (principalShift p j * teichLift p h) at hr
    rw [reduction_shifted_teichLift, reduction_shifted_teichLift] at hr
    subst h
    have hi : principalShift p i = principalShift p j := (teichLift_isUnit g hg).mul_right_cancel hv
    have hij : i = j := by
      apply primeLift_injective
      exact add_left_cancel hi
    subst j
    rfl
  · intro c
    have hc := (isUnit_iff_reduction_ne_zero c.val).mp c.property
    obtain ⟨τ, hτ⟩ := exists_principalShift_mul_teichLift c.val hc
    exact ⟨(τ, ⟨squareReduction p c.val, hc⟩), Subtype.ext hτ.symm⟩

/-- For prime p, the squared correlations at all unit differences sum to
(p-1) times the squared normalized moment. Parametrize units and use scaling invariance. -/
theorem sum_unit_correlations_sq {p : ℕ} [Fact p.Prime] :
    (∑ c : { c : ZMod (p ^ 2) // IsUnit c }, Nat.card (cosetDifferenceAt p 0 0 c.val) ^ 2) =
      (p - 1) * ∑ τ : ZMod p, normalizedCorrelation p τ ^ 2 := by
  classical
  have he :=
    Fintype.sum_bijective (unitParameterMap (p := p)) unitParameterMap_bijective
      (fun z : ZMod p × { g : ZMod p // g ≠ 0 } ↦ normalizedCorrelation p z.1 ^ 2)
      (fun c : { c : ZMod (p ^ 2) // IsUnit c } ↦ Nat.card (cosetDifferenceAt p 0 0 c.val) ^ 2)
      (fun z ↦
        congrArg (fun n : ℕ ↦ n ^ 2)
          (card_cosetDifferenceAt_mul_teichLift 0 0 _ z.2.val z.2.property).symm)
  rw [← he, Fintype.sum_prod_type]
  have hc : Fintype.card { g : ZMod p // g ≠ 0 } = p - 1 := by
    rw [Fintype.card_subtype_compl (fun g : ZMod p ↦ g = 0), ZMod.card, Fintype.card_subtype_eq]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.cast_id, hc]
  rw [Finset.mul_sum]

/-- For prime p, E=(p-1)^2+(p-1)*sum(normalizedCorrelation^2).
Parametrize the unit differences, isolate the zero difference, and discard nonzero nonunits. -/
theorem heilbronnEnergy_eq_normalized_moment {p : ℕ} [Fact p.Prime] :
    heilbronnEnergy p = (p - 1) ^ 2 + (p - 1) * ∑ τ : ZMod p, normalizedCorrelation p τ ^ 2 := by
  classical
  let : Nontrivial (ZMod (p ^ 2)) := (squareReduction p).domain_nontrivial
  have hz : ¬IsUnit (0 : ZMod (p ^ 2)) := not_isUnit_zero
  have hn :
    (∑ c : { c : ZMod (p ^ 2) // ¬IsUnit c }, Nat.card (cosetDifferenceAt p 0 0 c.val) ^ 2) =
      (p - 1) ^ 2 := by
    rw [Finset.sum_eq_single (⟨0, hz⟩ : { c : ZMod (p ^ 2) // ¬IsUnit c })]
    · rw [card_cosetDifferenceAt_zero]
    · intro c hc hne
      have hc0 : c.val ≠ 0 := fun he ↦ hne (Subtype.ext he)
      rw [cosetDifferenceAt_nonunit_empty 0 c.val hc0 c.property, Nat.card_of_isEmpty,
        zero_pow (by decide : 2 ≠ 0)]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have he :=
    Fintype.sum_subtype_add_sum_subtype (IsUnit : ZMod (p ^ 2) → Prop)
      (fun c ↦ Nat.card (cosetDifferenceAt p 0 0 c) ^ 2)
  rw [sum_unit_correlations_sq, hn] at he
  exact he.symm.trans (Nat.add_comm _ _)

/-- For odd prime p, positive K<=p and K^2>=64p, prove
K*sum(normalizedCorrelation^2)<=K^2*p+524288p^2. Feed the proved cubic tail bound into
the generic finite second-moment lemma and apply the total mass bound. -/
theorem normalized_moment_scaled {p K : ℕ} [Fact p.Prime] (hodd : Odd p) (hK : 0 < K) (hKP : K ≤ p)
    (hlarge : 64 * p ≤ K ^ 2) :
    K * (∑ τ : ZMod p, normalizedCorrelation p τ ^ 2) ≤ K ^ 2 * p + 524288 * p ^ 2 := by
  classical
  have hN : ∀ τ : ZMod p, normalizedCorrelation p τ ≤ p := by
    intro τ
    exact (card_cosetDifferenceAt_le 0 0 (principalShift p τ)).trans (Nat.sub_le p 1)
  have ht :=
    Analysis.sum_squares_le_of_cubic_tail (normalizedCorrelation p) p K (262144 * p ^ 2) hN hK hKP
      (fun k hk ↦
        card_mul_cube_le_of_normalizedCorrelation_ge hodd
          (Finset.univ.filter (fun τ ↦ k + 1 ≤ normalizedCorrelation p τ))
          (fun τ hτ ↦ (Finset.mem_filter.mp hτ).2)
          (hlarge.trans (Nat.pow_le_pow_left ((Finset.mem_Ico.mp hk).1.trans (Nat.le_succ k)) 2)))
  have hm : (∑ τ : ZMod p, (normalizedCorrelation p τ : ℚ)) ≤ (p : ℚ) := by
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr (sum_normalizedCorrelation_le hodd)
  have he := ht.trans (add_le_add (mul_le_mul_of_nonneg_left hm (sq_nonneg (K : ℚ))) le_rfl)
  have hc :
    ((K * (∑ τ : ZMod p, normalizedCorrelation p τ ^ 2) : ℕ) : ℚ) ≤
      ((K ^ 2 * p + 524288 * p ^ 2 : ℕ) : ℚ) := by
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at he
    nlinarith only [he]
  exact Nat.cast_le.mp hc

/-- For p>=262144 choose K=256*(sqrt(p)+1), with positive K<=p and
65536p<=K^2<=262144p. Prove the interval by integer square-root bounds, without enumeration. -/
theorem exists_square_root_scale {p : ℕ} (hp : 262144 ≤ p) :
    ∃ K : ℕ, 0 < K ∧ K ≤ p ∧ 65536 * p ≤ K ^ 2 ∧ K ^ 2 ≤ 262144 * p := by
  let s := Nat.sqrt p
  let K := 256 * (s + 1)
  have hs : 512 ≤ s := Nat.le_sqrt.mpr hp
  have hlo : s * s ≤ p := Nat.sqrt_le p
  have hhi : p < (s + 1) ^ 2 := Nat.lt_succ_sqrt' p
  have hKp : K ≤ p := by
    have hm := Nat.mul_le_mul_left s hs
    dsimp only [K]
    nlinarith only [hm, hlo, hs]
  have hKlo : 65536 * p ≤ K ^ 2 := by
    have hm := Nat.mul_le_mul_left 65536 hhi.le
    convert hm using 1
    ring
  have ht : s + 1 ≤ 2 * s := by linarith only [hs]
  have hKhi : K ^ 2 ≤ 262144 * p := by
    have hm := Nat.mul_le_mul_left 65536 (Nat.pow_le_pow_left ht 2)
    have hn := Nat.mul_le_mul_left 262144 hlo
    dsimp only [K]
    nlinarith only [hm, hn]
  exact ⟨K, mul_pos (by decide : 0 < 256) (Nat.succ_pos s), hKp, hKlo, hKhi⟩

/-- For odd prime p>=262144 the squared normalized second moment is at most
9437184p^3. Choose the square-root scale, square the scaled moment inequality and cancel p. -/
theorem normalized_moment_square_le {p : ℕ} [Fact p.Prime] (hodd : Odd p) (hp : 262144 ≤ p) :
    (∑ τ : ZMod p, normalizedCorrelation p τ ^ 2) ^ 2 ≤ 9437184 * p ^ 3 := by
  obtain ⟨K, hK, hKp, hKlo, hKhi⟩ := exists_square_root_scale hp
  let M := ∑ τ : ZMod p, normalizedCorrelation p τ ^ 2
  have h64 : 64 * p ≤ K ^ 2 := (Nat.mul_le_mul_right p (by decide : 64 ≤ 65536)).trans hKlo
  have hb := normalized_moment_scaled hodd hK hKp h64
  change K * M ≤ K ^ 2 * p + 524288 * p ^ 2 at hb
  have hKM : K * M ≤ 786432 * p ^ 2 := by
    have hm := Nat.mul_le_mul_right p hKhi
    nlinarith only [hb, hm]
  have hsq := Nat.pow_le_pow_left hKM 2
  have hlo := Nat.mul_le_mul_left (M ^ 2) hKlo
  have hf : (M ^ 2 * p) * 65536 ≤ (9437184 * p ^ 4) * 65536 := by nlinarith only [hsq, hlo]
  have hg := Nat.le_of_mul_le_mul_right hf (by decide : 0 < 65536)
  have hh : M ^ 2 * p ≤ (9437184 * p ^ 3) * p := by
    convert hg using 1
    ring
  exact Nat.le_of_mul_le_mul_right hh (Nat.Prime.pos Fact.out)

/-- For odd prime p>=262144 the energy satisfies E^2<=18874370p^5.
Use the exact normalized moment formula, its squared bound and
the elementary cross-term inequality. -/
theorem heilbronnEnergy_square_le_large {p : ℕ} [Fact p.Prime] (hodd : Odd p) (hp : 262144 ≤ p) :
    heilbronnEnergy p ^ 2 ≤ 18874370 * p ^ 5 := by
  let M := ∑ τ : ZMod p, normalizedCorrelation p τ ^ 2
  have hM : M ^ 2 ≤ 9437184 * p ^ 3 := normalized_moment_square_le hodd hp
  have hE : heilbronnEnergy p ≤ p ^ 2 + p * M := by
    rw [heilbronnEnergy_eq_normalized_moment]
    exact
      Nat.add_le_add (Nat.pow_le_pow_left (Nat.sub_le p 1) 2)
        (Nat.mul_le_mul_right M (Nat.sub_le p 1))
  have hsq := Nat.pow_le_pow_left hE 2
  have hcross := two_mul_le_add_sq (p ^ 2) (p * M)
  have hprod := Nat.mul_le_mul_left (2 * p ^ 2) hM
  have hp1 : 1 ≤ p := (Nat.Prime.pos Fact.out)
  have hp4 : p ^ 4 ≤ p ^ 5 := by
    have he := Nat.mul_le_mul_left (p ^ 4) hp1
    simpa only [mul_one, ← pow_succ] using he
  nlinarith only [hsq, hcross, hprod, hp4]

/-- For every odd prime p, E^2<=18874370p^5, giving an unconditional 5/2 exponent.
Use the normalized moment estimate above 262144 and the general cubic energy bound below;
no finite prime enumeration or unproved energy estimate is required. -/
theorem heilbronnEnergy_square_le_uniform {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    heilbronnEnergy p ^ 2 ≤ 18874370 * p ^ 5 := by
  by_cases hp : 262144 ≤ p
  · exact heilbronnEnergy_square_le_large hodd hp
  · have hsmall : p ≤ 262144 := (Nat.lt_of_not_ge hp).le
    have he : heilbronnEnergy p ≤ p ^ 3 :=
      heilbronnEnergy_le_cube.trans (Nat.pow_le_pow_left (Nat.sub_le p 1) 3)
    have he2 := Nat.pow_le_pow_left he 2
    calc
      _ ≤ (p ^ 3) ^ 2 := he2
      _ = p ^ 5 * p := by ring
      _ ≤ p ^ 5 * 262144 := Nat.mul_le_mul_left _ hsmall
      _ ≤ _ := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right _ (by decide : 262144 ≤ 18874370)

end PseudoPrime.NumberTheory.Heilbronn
