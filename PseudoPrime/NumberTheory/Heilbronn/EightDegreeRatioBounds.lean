/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalFiberRatioBands

/-! # Eight-degree uniform rational counts with prime loss 1/84 -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The eight reciprocal degrees cover [1/84,5/28] with radius 1/84.
This exact rational interval computation selects a fixed product degree for
any admissible height exponent; no prime-dependent degree set is introduced. -/
theorem eight_degree_exponent_cover {alpha : ℝ} (hlo : (1 / 84 : ℝ) ≤ alpha)
    (hhi : alpha ≤ (5 / 28 : ℝ)) :
    ∃ m : ℕ,
      m ∈ ({6, 7, 8, 9, 11, 14, 21, 42} : Finset ℕ) ∧
        1 / (m : ℝ) - 1 / 84 ≤ alpha ∧ alpha ≤ 1 / (m : ℝ) + 1 / 84 := by
  by_cases h42 : alpha ≤ 1 / (42 : ℝ) + 1 / 84
  · exact
      ⟨42, by decide, by
        norm_num only [Nat.cast_ofNat]; linarith only [hlo], h42⟩
  by_cases h21 : alpha ≤ 1 / (21 : ℝ) + 1 / 84
  · exact
      ⟨21, by decide, by
        norm_num only [Nat.cast_ofNat]; linarith only [h42], h21⟩
  by_cases h14 : alpha ≤ 1 / (14 : ℝ) + 1 / 84
  · exact
      ⟨14, by decide, by
        norm_num only [Nat.cast_ofNat]; linarith only [h21], h14⟩
  by_cases h11 : alpha ≤ 1 / (11 : ℝ) + 1 / 84
  · exact
      ⟨11, by decide, by
        norm_num only [Nat.cast_ofNat]; linarith only [h14], h11⟩
  by_cases h9 : alpha ≤ 1 / (9 : ℝ) + 1 / 84
  · exact
      ⟨9, by decide, by
        norm_num only [Nat.cast_ofNat]; linarith only [h11], h9⟩
  by_cases h8 : alpha ≤ 1 / (8 : ℝ) + 1 / 84
  · exact
      ⟨8, by decide, by
        norm_num only [Nat.cast_ofNat]; linarith only [h9], h8⟩
  by_cases h7 : alpha ≤ 1 / (7 : ℝ) + 1 / 84
  · exact
      ⟨7, by decide, by
        norm_num only [Nat.cast_ofNat]; linarith only [h8], h7⟩
  refine ⟨6, by decide, ?_, ?_⟩
  · norm_num only [Nat.cast_ofNat]
    linarith only [h7]
  · norm_num only [Nat.cast_ofNat]
    linarith only [hhi]

/-- A finite positive rational family of canonical height at most T has at
most T² elements. Encode each rational by its canonical numerator and denominator
in [1,T]². This elementary bound handles the smallest height band. -/
theorem bounded_positive_rational_card_le_square {T : ℕ} (S : Finset ℚ)
    (hS : ∀ q ∈ S, 0 < q ∧ q.num.natAbs ≤ T ∧ q.den ≤ T) : S.card ≤ T ^ 2 := by
  classical
  let f : ℚ → ℕ × ℕ := fun q ↦ (q.num.natAbs, q.den)
  have hm : Set.MapsTo f (↑S : Set ℚ) (↑(Finset.Icc 1 T ×ˢ Finset.Icc 1 T) : Set (ℕ × ℕ)) := by
    intro q hq
    have h := hS q hq
    exact
      Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr h.1)), h.2.1⟩,
          Finset.mem_Icc.mpr ⟨Rat.den_pos q, h.2.2⟩⟩
  have hi : Set.InjOn f (↑S : Set ℚ) := by
    intro q hq r hr he
    have hn := congrArg Prod.fst he
    have hd := congrArg Prod.snd he
    dsimp only [f] at hn hd
    rw [positive_rat_nat_fraction (hS q hq).1, positive_rat_nat_fraction (hS r hr).1, hn, hd]
  have hb := Finset.card_le_card_of_injOn f hm hi
  simpa only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, pow_two] using hb

/-- A height T=p^alpha in the interval 1/m-beta≤alpha≤1/m+beta
satisfies the two balanced monomial inequalities. Raise the height identity
to m and compare exponents. This translates interval coverage to product bounds. -/
theorem residue_band_of_power_height {p T m : ℕ} {alpha beta : ℝ} (hp : 1 < p) (hm : 0 < m)
    (heq : (T : ℝ) = (p : ℝ) ^ alpha) (hlo : 1 / (m : ℝ) - beta ≤ alpha)
    (hhi : alpha ≤ 1 / (m : ℝ) + beta) :
    (p : ℝ) ≤ (T : ℝ) ^ m * (p : ℝ) ^ (m * beta) ∧
      (T : ℝ) ^ m ≤ (p : ℝ) * (p : ℝ) ^ (m * beta) := by
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr hp.le
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hp)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hcancel : (1 / (m : ℝ)) * m = 1 := div_mul_cancel₀ 1 (ne_of_gt hmR)
  have hl := mul_le_mul_of_nonneg_right hlo hmR.le
  have hh := mul_le_mul_of_nonneg_right hhi hmR.le
  have heT : (T : ℝ) ^ m = (p : ℝ) ^ (alpha * m) := by rw [heq, ← Real.rpow_mul_natCast hp0.le]
  constructor
  · calc
      _ = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (p : ℝ) ^ (alpha * m + m * beta) :=
        Real.rpow_le_rpow_of_exponent_le hpR (by nlinarith only [hl, hcancel])
      _ = _ := by rw [Real.rpow_add hp0, ← heT]
  · calc
      _ = (p : ℝ) ^ (alpha * m) := heT
      _ ≤ (p : ℝ) ^ (1 + m * beta) :=
        Real.rpow_le_rpow_of_exponent_le hpR (by nlinarith only [hh, hcancel])
      _ = _ := by rw [Real.rpow_add hp0, Real.rpow_one]

/-- Natural common coefficient 1 plus the sum of the eight explicit degree
coefficients. Its factorial expression depends only on the precision c,
before the prime and heights vary. This permits effective threshold bounds. -/
def eightDegreeFiberCoefficient (c : ℕ) : ℕ :=
  1 + ∑ m ∈ ({6, 7, 8, 9, 11, 14, 21, 42} : Finset ℕ), fiberBandCoefficient m c

/-- The explicit sum of eight degree coefficients controls all restricted
ratios below p^(5/28), with height exponent 1+1/c and prime loss 1/84.
Apply the exponent covering and the explicit band bounds, using the trivial
count below the smallest band. No existential coefficient is selected. -/
theorem heightRestrictedRatioSet_le_explicit_eight_degree_bound {c : ℕ} (hc : 0 < c) :
    ∀ (p H T : ℕ) [Fact p.Prime],
      H < p →
        (T : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        ((heightRestrictedRatioSet p H T).card : ℝ) ≤
          eightDegreeFiberCoefficient c * (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ (1 / 84 : ℝ) := by
  classical
  let D : Finset ℕ := {6, 7, 8, 9, 11, 14, 21, 42}
  have hD : ∀ m : D, 0 < m.val := by
    intro m
    have hh := m.property
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h | h | h | h | h | h | h | h
    all_goals rw [h]; decide
  let C : D → ℝ := fun m ↦ fiberBandCoefficient m c
  have hC (m : D) : 0 < C m := Nat.cast_pos.mpr (fiberBandCoefficient_pos m c)
  have hbound (m : D) := heightRestrictedRatioSet_le_explicit_fiber_band_bound (hD m) hc
  let K : ℝ := 1 + ∑ m : D, C m
  have hsum : 0 ≤ ∑ m : D, C m := Finset.sum_nonneg (fun m _ ↦ (hC m).le)
  have hK : 1 ≤ K := by
    dsimp only [K]; linarith only [hsum]
  have hCK (m : D) : C m ≤ K := by
    have h := Finset.single_le_sum (s := Finset.univ) (fun i _ ↦ (hC i).le) (Finset.mem_univ m)
    dsimp only [K]
    linarith only [h]
  have hKdef : (eightDegreeFiberCoefficient c : ℝ) = K := by
    simp only [eightDegreeFiberCoefficient, K, C, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
    rw [Finset.sum_coe_sort D (fun m : ℕ ↦ (fiberBandCoefficient m c : ℝ))]
  rw [hKdef]
  intro p H T hp hHp htop
  have hcanonical : ∀ q ∈ heightRestrictedRatioSet p H T, 0 < q ∧ q.num.natAbs ≤ T ∧ q.den ≤ T :=
    fun q hq ↦
    boundedRationalResidue_canonical_height
      (Exists.choose_spec (heightRestrictedRatioSet_has_residues hHp q hq))
  have htriv := Nat.cast_le (α := ℝ).mpr (bounded_positive_rational_card_le_square _ hcanonical)
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := lt_trans (by norm_num only : (0 : ℝ) < 1) hp1
  have hpw : 0 ≤ (p : ℝ) ^ (1 / 84 : ℝ) := Real.rpow_nonneg hp0.le _
  by_cases hT : T = 0
  · subst T
    have hc0 : (0 : ℝ) < 1 + 1 / (c : ℝ) :=
      add_pos_of_pos_of_nonneg (by norm_num only)
        (div_nonneg (by norm_num only) (Nat.cast_nonneg c))
    simpa only [Nat.zero_pow (by decide : 0 < 2), Nat.cast_zero, Real.zero_rpow (ne_of_gt hc0),
      mul_zero, zero_mul] using htriv
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT
  have hT1 : (1 : ℝ) ≤ T := Nat.one_le_cast.mpr hTpos
  have hT0 : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have hTex : (T : ℝ) ≤ (T : ℝ) ^ (1 + 1 / (c : ℝ)) := by
    have he : (1 : ℝ) ≤ 1 + 1 / (c : ℝ) :=
      le_add_of_nonneg_right (div_nonneg (by norm_num only) (Nat.cast_nonneg c))
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1 he
  by_cases hsmall : (T : ℝ) ≤ (p : ℝ) ^ (1 / 84 : ℝ)
  · have h1 := mul_le_mul_of_nonneg_left hsmall hT0.le
    have h2 := mul_le_mul_of_nonneg_right hTex hpw
    have h3 :=
      mul_le_mul_of_nonneg_right hK (mul_nonneg (Real.rpow_nonneg hT0.le (1 + 1 / (c : ℝ))) hpw)
    have htriv' : ((heightRestrictedRatioSet p H T).card : ℝ) ≤ (T : ℝ) ^ 2 := by
      simpa only [Nat.cast_pow] using htriv
    calc
      _ ≤ _ := htriv'
      _ ≤ (T : ℝ) * (p : ℝ) ^ (1 / 84 : ℝ) := by simpa only [pow_two] using h1
      _ ≤ (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ (1 / 84 : ℝ) := h2
      _ ≤ _ := by simpa only [one_mul, mul_assoc] using h3
  let alpha : ℝ := Real.log T / Real.log p
  have heq : (T : ℝ) = (p : ℝ) ^ alpha := by
    rw [Real.rpow_def_of_pos hp0]
    dsimp only [alpha]
    rw [mul_div_cancel₀ (Real.log T) (ne_of_gt (Real.log_pos hp1)), Real.exp_log hT0]
  have halphaLo : (1 / 84 : ℝ) ≤ alpha :=
    ((Real.rpow_le_rpow_left_iff hp1).mp
      (by
        rw [← heq]; exact (not_le.mp hsmall).le))
  have halphaHi : alpha ≤ (5 / 28 : ℝ) :=
    (Real.rpow_le_rpow_left_iff hp1).mp
      (by
        rw [← heq]; exact htop)
  obtain ⟨m, hm, hlo, hhi⟩ := eight_degree_exponent_cover halphaLo halphaHi
  let i : D := ⟨m, hm⟩
  have hb := residue_band_of_power_height (Fact.out : p.Prime).one_lt (hD i) heq hlo hhi
  have hcount := hbound i p H T hHp hTpos (1 / 84) hb.1 hb.2
  have hfactor : 0 ≤ (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ (1 / 84 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hT0.le _) hpw
  exact hcount.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hCK i) hfactor)

/-- The explicit common coefficient is positive for every precision. The
initial one also covers the trivial small-height branch of the ratio bound. -/
theorem eightDegreeFiberCoefficient_pos (c : ℕ) : 0 < eightDegreeFiberCoefficient c := by
  exact Nat.zero_lt_one.trans_le (Nat.le_add_right 1 _)

/-- For each fixed positive precision c, one constant controls all restricted
ratio families at T≤p^(5/28), with height exponent 1+1/c and prime loss 1/84.
Sum eight fixed degree constants, use the trivial bound below p^(1/84),
and apply the balanced growth theorem above it. Constants precede p,H,T. -/
theorem exists_uniform_eight_degree_ratio_bound {c : ℕ} (hc : 0 < c) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (p H T : ℕ) [Fact p.Prime],
          H < p →
            (T : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
            ((heightRestrictedRatioSet p H T).card : ℝ) ≤
              K * (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ (1 / 84 : ℝ) := by
  exact
    ⟨eightDegreeFiberCoefficient c, Nat.cast_pos.mpr (eightDegreeFiberCoefficient_pos c),
      heightRestrictedRatioSet_le_explicit_eight_degree_bound hc⟩

/-- With a prescribed precision 1/c≤eta, the explicit degree sum controls
R(T) by K_c T p^(1/84+eta). Absorb the height power using T≤p and compare
the prime exponents. This retains the coefficient for effective counts. -/
theorem heightRestrictedRatioSet_le_explicit_finite_fiber_ratio_bound {eta : ℝ} {c : ℕ} (hc : 0 < c)
    (hprec : 1 / (c : ℝ) ≤ eta) :
    ∀ (p H T : ℕ) [Fact p.Prime],
      H < p →
        (T : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        ((heightRestrictedRatioSet p H T).card : ℝ) ≤
          eightDegreeFiberCoefficient c * T * (p : ℝ) ^ (1 / 84 + eta) := by
  let K : ℝ := eightDegreeFiberCoefficient c
  have hK : 0 < K := Nat.cast_pos.mpr (eightDegreeFiberCoefficient_pos c)
  have hbound := heightRestrictedRatioSet_le_explicit_eight_degree_bound hc
  intro p H T hp hHp htop
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).pos
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have he : (1 / (c : ℝ)) ≤ eta := hprec
  have hTp : (T : ℝ) ≤ p :=
    htop.trans
      (by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num only : (5 / 28 : ℝ) ≤ 1))
  have hpow : (T : ℝ) ^ (1 / (c : ℝ)) ≤ (p : ℝ) ^ eta :=
    (Real.rpow_le_rpow (Nat.cast_nonneg T) hTp
          (div_nonneg (by norm_num only) (Nat.cast_nonneg c))).trans
      (Real.rpow_le_rpow_of_exponent_le hp1 he)
  have hsplit : (T : ℝ) ^ (1 + 1 / (c : ℝ)) = T * (T : ℝ) ^ (1 / (c : ℝ)) := by
    rw [Real.rpow_add_of_nonneg (Nat.cast_nonneg T) (by norm_num only : (0 : ℝ) ≤ 1)
        (div_nonneg (by norm_num only) (Nat.cast_nonneg c)),
      Real.rpow_one]
  have hh := hbound p H T hHp htop
  rw [hsplit] at hh
  have hm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK.le (Nat.cast_nonneg T)))
      (Real.rpow_nonneg hp0.le (1 / 84))
  have hm' :
    K * T * (T : ℝ) ^ (1 / (c : ℝ)) * (p : ℝ) ^ (1 / 84 : ℝ) ≤
      K * T * (p : ℝ) ^ (1 / 84 + eta) := by
    rw [Real.rpow_add hp0]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
  apply LE.le.trans _ hm'
  simpa only [mul_assoc] using hh

/-- For every eta>0 a common positive constant gives R(T)≤KTp^(1/84+eta)
whenever H<p and T≤p^(5/28). Choose reciprocal precision below eta and
absorb the height loss using T≤p. This is the uniform input for the
reciprocal-height sum exchange and the improved Heilbronn energy budget. -/
theorem exists_uniform_finite_fiber_ratio_bound {eta : ℝ} (heta : 0 < eta) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (p H T : ℕ) [Fact p.Prime],
          H < p →
            (T : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
            ((heightRestrictedRatioSet p H T).card : ℝ) ≤ K * T * (p : ℝ) ^ (1 / 84 + eta) := by
  obtain ⟨c, hc, hprec⟩ := Real.exists_nat_pos_inv_lt heta
  refine ⟨eightDegreeFiberCoefficient c, Nat.cast_pos.mpr (eightDegreeFiberCoefficient_pos c), ?_⟩
  apply heightRestrictedRatioSet_le_explicit_finite_fiber_ratio_bound hc
  simpa only [one_div] using hprec.le

end PseudoPrime.NumberTheory.Heilbronn
