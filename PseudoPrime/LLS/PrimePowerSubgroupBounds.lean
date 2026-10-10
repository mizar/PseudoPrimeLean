/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SubgroupModulusReduction
public import PseudoPrime.Analysis.LogPowerAsymptotics

/-! # Gamma least-prime bounds for odd prime-power moduli

Indices coprime to the prime descend to the prime modulus. A finite remainder
handles bounded primes uniformly, and proper powers save a factor of four
in the squared logarithmic coefficient.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a prime-power modulus and subgroup index coprime to the prime,
the index divides the prime minus one. Lagrange divisibility and the totient
formula let the coprime prime-power factor cancel. This certifies descent
to the prime modulus. -/
theorem prime_pow_index_dvd_pred {p k : ℕ} (hp : p.Prime) (hk : 0 < k) [NeZero (p ^ k)]
    (H : Subgroup (ZMod (p ^ k))ˣ) (hc : Nat.Coprime H.index p) : H.index ∣ p - 1 := by
  have hi := H.index_dvd_card
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hk] at hi
  exact (hc.pow_right (k - 1)).dvd_of_dvd_mul_left hi

/-- For an odd prime-power modulus with positive exponent and subgroup
index coprime to the prime, the eligible prime set equals that of the image
subgroup modulo the prime. The cyclic index criterion gives kernel inclusion,
and positive powers preserve prime support. Least primes therefore agree. -/
theorem prime_pow_primesOutside_reduction {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ) (hc : Nat.Coprime H.index p) :
    primesOutside (p ^ k) H = primesOutside p (H.map (ZMod.unitsMap (dvd_pow_self p hk.ne'))) := by
  let : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 k
  apply primesOutside_reduction (dvd_pow_self p hk.ne') H
  · apply reduction_kernel_le_subgroup_of_cyclic
    rw [Nat.totient_prime hp]
    exact prime_pow_index_dvd_pred hp hk H hc
  · intro r hr
    exact ⟨hr.dvd_of_dvd_pow, fun hd ↦ hd.trans (dvd_pow_self p hk.ne')⟩

theorem gamma_prime_pow_bound_659_with_finite_remainder
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 4 ≤ h) :
    ∃ B : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          0 < k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = h →
              Nat.Coprime h p →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) ≤ max (B : ℝ) ((659 / 1000) * (Real.log p) ^ 2) := by
  obtain ⟨B, hB⟩ := gamma_prime_bound_659_with_finite_remainder hg h hh
  refine ⟨B, ?_⟩
  intro p k hp hp2 hk _ _ H hH hc
  let : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 k
  let hm : p ∣ p ^ k := dvd_pow_self p hk.ne'
  have hd : H.index ∣ Nat.totient p := by
    rw [Nat.totient_prime hp]
    exact prime_pow_index_dvd_pred hp hk H (hH.symm ▸ hc)
  have hi : (H.map (ZMod.unitsMap hm)).index = h :=
    (H.index_map_eq (ZMod.unitsMap_surjective hm)
          (reduction_kernel_le_subgroup_of_cyclic hm H hd)).trans
      hH
  obtain ⟨r, hr, hb⟩ := hB p (H.map (ZMod.unitsMap hm)) hi
  rw [← prime_pow_primesOutside_reduction hp hp2 hk H (hH.symm ▸ hc)] at hr
  exact ⟨r, hr, hb⟩

/-- For exponents at least two, the prime logarithm with coefficient
`659/1000` is bounded by the prime-power logarithm with coefficient
`659/4000`. Rewrite the logarithm as the exponent times the prime logarithm
and use the square of the exponent. This yields the factor-four saving. -/
theorem gamma_prime_pow_log_coefficient_le {p k : ℕ} (hk : 2 ≤ k) :
    (659 / 1000 : ℝ) * (Real.log p) ^ 2 ≤ (659 / 4000) * (Real.log (p ^ k : ℕ)) ^ 2 := by
  have hkR : (2 : ℝ) ≤ k := Nat.cast_le.mpr hk
  have hs : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [sq_nonneg ((k : ℝ) - 2), hkR]
  have hm := mul_nonneg (sq_nonneg (Real.log p)) (sub_nonneg.mpr hs)
  rw [Nat.cast_pow, Real.log_pow]
  nlinarith only [hm]

theorem gamma_proper_prime_pow_bound_659
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 4 ≤ h) :
    ∃ B : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          2 ≤ k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = h →
              Nat.Coprime h p →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) ≤ max (B : ℝ) ((659 / 4000) * (Real.log (p ^ k : ℕ)) ^ 2) := by
  obtain ⟨B, hB⟩ := gamma_prime_pow_bound_659_with_finite_remainder hg h hh
  refine ⟨B, ?_⟩
  intro p k hp hp2 hk _ _ H hH hc
  obtain ⟨r, hr, hb⟩ := hB p k hp hp2 (lt_of_lt_of_le (by norm_num only) hk) H hH hc
  exact ⟨r, hr, hb.trans (max_le_max_left _ (gamma_prime_pow_log_coefficient_le hk))⟩

/-- Under GRH, fixed indices at least four and any positive error admit
a strict asymptotic prime-power bound with coefficient `659/4000 + ε`,
provided the odd prime and index are coprime. Logarithmic growth absorbs the
finite remainder uniformly in the prime and exponent. The threshold is on
the full modulus, so bounded prime bases are included. -/
theorem gamma_proper_prime_pow_asymptotic_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 4 ≤ h) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          2 ≤ k →
          Q ≤ p ^ k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = h →
              Nat.Coprime h p →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) < (659 / 4000 + ε) * (Real.log (p ^ k : ℕ)) ^ 2 := by
  obtain ⟨B, hB⟩ := gamma_proper_prime_pow_bound_659 hg h hh
  have hc : (0 : ℝ) < 659 / 4000 + ε := by linarith only [hε]
  obtain ⟨Q, hQ2, hQ⟩ := Analysis.exists_nat_threshold_const_lt_log_sq (Nat.cast_nonneg B) hc
  refine ⟨Q, ?_⟩
  intro p k hp hp2 hk hq _ _ H hH hc'
  obtain ⟨r, hr, hb⟩ := hB p k hp hp2 hk H hH hc'
  have hlog : 0 < Real.log (p ^ k : ℕ) := Real.log_pos (by exact_mod_cast hQ2.trans hq)
  refine ⟨r, hr, hb.trans_lt (max_lt_iff.mpr ⟨hQ _ hq, ?_⟩)⟩
  exact mul_lt_mul_of_pos_right (lt_add_of_pos_right _ hε) (sq_pos_of_pos hlog)

/-- Under GRH, all proper powers of odd primes satisfy the strict
index-four least-prime bound with coefficient `659/4000 + ε` for sufficiently
large moduli. Odd primes are coprime to four, so the general prime-power bound
needs no extra coprimality premise. The threshold is uniform in subgroups. -/
theorem gamma_index_four_proper_prime_pow_asymptotic_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          2 ≤ k →
          Q ≤ p ^ k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = 4 →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) < (659 / 4000 + ε) * (Real.log (p ^ k : ℕ)) ^ 2 := by
  obtain ⟨Q, hQ⟩ := gamma_proper_prime_pow_asymptotic_bound hg 4 le_rfl ε hε
  refine ⟨Q, ?_⟩
  intro p k hp hp2 hk hq _ _ H hH
  have hc : Nat.Coprime 4 p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hd' : p ∣ 2 ^ 2 := by
      norm_num only at hd ⊢; exact hd
    exact hp2 ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow hd')).symm
  exact hQ p k hp hp2 hk hq H hH hc

/-- The coefficient `659/4000` is strictly below the original index-four
coefficient of Theorem 1.3. Certified bounds on `log 2` bound `log 8` and its
negative denominator away from zero. Comparing squares reduces the assertion
to a strict rational margin. This is the slack used in the prime-power branch. -/
theorem gamma_index_four_proper_power_coefficient :
    (659 / 4000 : ℝ) < (9 / 64) * (Real.log 8 / (Real.log 8 - 4)) ^ 2 := by
  have hid : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have hi := Real.log_pow (2 : ℝ) 3
    norm_num only at hi
    exact hi
  have hlo : (20793 / 10000 : ℝ) < Real.log 8 := by
    rw [hid]
    linarith only [Real.log_two_gt_d9]
  have hup : Real.log (8 : ℝ) < 3 := by
    rw [hid]
    linarith only [Real.log_two_lt_d9]
  have hden : Real.log (8 : ℝ) - 4 ≠ 0 := by linarith only [hup]
  have hs : (Real.log (8 : ℝ) - 4) ^ 2 ≤ (20793 / 10000 - 4 : ℝ) ^ 2 := by
    have hm :=
      mul_nonneg (sub_nonneg.mpr hlo.le)
        (by linarith only [hup] : (0 : ℝ) ≤ 8 - 20793 / 10000 - Real.log 8)
    nlinarith only [hm]
  have hl := mul_self_lt_mul_self (by norm_num only : (0 : ℝ) ≤ 20793 / 10000) hlo
  rw [div_pow, ← mul_div_assoc, lt_div_iff₀ (sq_pos_of_ne_zero hden)]
  nlinarith only [hs, hl]

/-- For a fixed odd prime and positive reduction exponent, all larger
prime powers have one common bound on least outside primes of a fixed index
dividing the reduced totient. The reduction kernel lies in every such
subgroup; prime support and index are preserved. Finite existence at the
fixed modulus bounds all image subgroups, with no explicit enumeration. -/
theorem exists_uniform_prime_pow_bound_of_fixed_reduction {p a h : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (hh : 1 < h) (hd : h ∣ Nat.totient (p ^ a)) [NeZero p] :
    ∃ B : ℕ,
      ∀ k : ℕ,
        a ≤ k →
          ∀ [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = h → ∃ r : ℕ, IsLeast (primesOutside (p ^ k) H) r ∧ r ≤ B := by
  obtain ⟨B, hB⟩ := exists_uniform_least_prime_bound_of_modulus_le (p ^ a)
  refine ⟨B, ?_⟩
  intro k hak _ H hH
  let : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 k
  let hm : p ^ a ∣ p ^ k := pow_dvd_pow p hak
  have hker := reduction_kernel_le_subgroup_of_cyclic hm H (hH.symm ▸ hd)
  have hi : (H.map (ZMod.unitsMap hm)).index = h :=
    (H.index_map_eq (ZMod.unitsMap_surjective hm) hker).trans hH
  have hproper : H.map (ZMod.unitsMap hm) ≠ ⊤ := fun ht ↦
    (ne_of_gt hh) (hi.symm.trans (ht ▸ Subgroup.index_top))
  obtain ⟨r, hr, hb⟩ := hB (p ^ a) le_rfl (H.map (ZMod.unitsMap hm)) hproper
  have hs : ∀ r : ℕ, r.Prime → (r ∣ p ^ k ↔ r ∣ p ^ a) := by
    intro r hr
    exact ⟨fun hk ↦ (hr.dvd_of_dvd_pow hk).trans (dvd_pow_self p ha.ne'), fun ha' ↦ ha'.trans hm⟩
  rw [← primesOutside_reduction hm H hker hs] at hr
  exact ⟨r, hr, hb⟩

/-- Under GRH, one exceptional odd prime can be added to the coprime
prime-power bound if its square totient is divisible by the fixed index.
Reduce its powers to the square modulus and use a uniform finite bound;
logarithmic growth absorbs this bound. All other odd primes use the coprime
bound. This supplies the exceptional bases for indices five and six. -/
theorem gamma_proper_prime_pow_asymptotic_bound_of_exceptional_prime
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h t : ℕ} (hh : 4 ≤ h)
    (ht : t.Prime) (ht2 : t ≠ 2) [NeZero t] (hd : h ∣ Nat.totient (t ^ 2))
    (hc : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ t → Nat.Coprime h p) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          2 ≤ k →
          Q ≤ p ^ k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = h →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) < (659 / 4000 + ε) * (Real.log (p ^ k : ℕ)) ^ 2 := by
  obtain ⟨B, hB⟩ :=
    exists_uniform_prime_pow_bound_of_fixed_reduction ht ht2 (by norm_num only : 0 < 2)
      (lt_of_lt_of_le (by norm_num only : 1 < 4) hh) hd
  obtain ⟨Q0, hQ0⟩ := gamma_proper_prime_pow_asymptotic_bound hg h hh ε hε
  obtain ⟨Q1, _, hQ1⟩ :=
    Analysis.exists_nat_threshold_const_lt_log_sq (Nat.cast_nonneg B)
      (by linarith only [hε] : (0 : ℝ) < 659 / 4000 + ε)
  refine ⟨max Q0 Q1, ?_⟩
  intro p k hp hp2 hk hq _ _ H hH
  by_cases hpt : p = t
  · subst p
    obtain ⟨r, hr, hb⟩ := hB k hk H hH
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans_lt (hQ1 _ ((le_max_right Q0 Q1).trans hq))⟩
  · exact hQ0 p k hp hp2 hk ((le_max_left Q0 Q1).trans hq) H hH (hc p hp hp2 hpt)

/-- Under GRH, all proper powers of odd primes satisfy the index-five
asymptotic least-prime bound with coefficient `659/4000 + ε`. The exceptional
base five reduces to modulus twenty-five, whose totient is divisible by five;
all other prime bases are coprime to the index. The threshold is uniform. -/
theorem gamma_index_five_proper_prime_pow_asymptotic_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          2 ≤ k →
          Q ≤ p ^ k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = 5 →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) < (659 / 4000 + ε) * (Real.log (p ^ k : ℕ)) ^ 2 := by
  have hd : 5 ∣ Nat.totient (5 ^ 2) := by
    rw [Nat.totient_prime_pow Nat.prime_five (by norm_num only : 0 < 2)]
    norm_num only
  apply
    gamma_proper_prime_pow_asymptotic_bound_of_exceptional_prime hg (by norm_num only : 4 ≤ 5)
      Nat.prime_five (by norm_num only) hd ?_ ε hε
  intro p hp _ hp5
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact hp5 ((Nat.prime_five.dvd_iff_eq hp.ne_one).mp hd).symm

/-- Under GRH, all proper powers of odd primes satisfy the index-six
asymptotic least-prime bound with coefficient `659/4000 + ε`. The exceptional
base three reduces to modulus nine, whose totient is six; every other odd
prime is coprime to the index. Finite existence covers the exceptional tower. -/
theorem gamma_index_six_proper_prime_pow_asymptotic_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          2 ≤ k →
          Q ≤ p ^ k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = 6 →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) < (659 / 4000 + ε) * (Real.log (p ^ k : ℕ)) ^ 2 := by
  have hd : 6 ∣ Nat.totient (3 ^ 2) := by
    rw [Nat.totient_prime_pow Nat.prime_three (by norm_num only : 0 < 2)]
    norm_num only
  apply
    gamma_proper_prime_pow_asymptotic_bound_of_exceptional_prime hg (by norm_num only : 4 ≤ 6)
      Nat.prime_three (by norm_num only) hd ?_ ε hε
  intro p hp hp2 hp3
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hd' : p ∣ 2 * 3 := hd
  rcases hp.dvd_mul.mp hd' with h2 | h3
  · exact hp2 ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp h2).symm
  · exact hp3 ((Nat.prime_three.dvd_iff_eq hp.ne_one).mp h3).symm

/-- Under GRH, each index from four through six admits the strict
prime-power bound with coefficient `659/4000 + ε` for sufficiently large
odd proper-prime-power moduli. The three index-specific results include all
prime bases, including the exceptional bases five and three. -/
theorem gamma_small_index_proper_prime_pow_asymptotic_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh4 : 4 ≤ h) (hh6 : h ≤ 6)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          2 ≤ k →
          Q ≤ p ^ k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = h →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) < (659 / 4000 + ε) * (Real.log (p ^ k : ℕ)) ^ 2 := by
  rcases Nat.eq_or_lt_of_le hh4 with he | he
  · subst h
    exact gamma_index_four_proper_prime_pow_asymptotic_bound hg ε hε
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt he) with he5 | he5
    · subst h
      exact gamma_index_five_proper_prime_pow_asymptotic_bound hg ε hε
    · have he6 : h = 6 := Nat.le_antisymm hh6 (Nat.succ_le_of_lt he5)
      subst h
      exact gamma_index_six_proper_prime_pow_asymptotic_bound hg ε hε

/-- If the scalar factor is at least `4/25` and the logarithmic argument
lies between `23/10` and three, its squared ratio with denominator `L-4`
exceeds `659/4000`. Square bounds and a rational margin prove the comparison.
This is used for the index-five and index-six coefficients. -/
private theorem proper_prime_power_coefficient_lt_of_log {a L : ℝ} (ha : 4 / 25 ≤ a)
    (hlo : 23 / 10 < L) (hup : L < 3) : (659 / 4000 : ℝ) < a * (L / (L - 4)) ^ 2 := by
  have hden : L - 4 ≠ 0 := by linarith only [hup]
  have hs : (L - 4) ^ 2 ≤ (23 / 10 - 4 : ℝ) ^ 2 := by
    have hm :=
      mul_nonneg (sub_nonneg.mpr hlo.le) (by linarith only [hup] : (0 : ℝ) ≤ 8 - 23 / 10 - L)
    nlinarith only [hm]
  have hl := mul_self_lt_mul_self (by norm_num only : (0 : ℝ) ≤ 23 / 10) hlo
  have hm := mul_le_mul_of_nonneg_right ha (sq_nonneg L)
  rw [div_pow, ← mul_div_assoc, lt_div_iff₀ (sq_pos_of_ne_zero hden)]
  nlinarith only [hs, hl, hm]

/-- For indices four through six, coefficient `659/4000` lies strictly
below the original leading coefficient of Theorem 1.3. The index-four margin
uses its sharper certificate; certified logarithms of two, three and five
place the other cases in a common rational interval. -/
theorem proper_prime_power_coefficient_lt_small_index {h : ℕ} (hh4 : 4 ≤ h) (hh6 : h ≤ 6) :
    (659 / 4000 : ℝ) <
      (1 / 4) * (1 - 1 / (h : ℝ)) ^ 2 *
        (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2 := by
  rcases Nat.eq_or_lt_of_le hh4 with he | he
  · subst h
    norm_num only
    exact gamma_index_four_proper_power_coefficient
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt he) with he5 | he5
    · subst h
      have hid : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
        have hi := Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0)
        norm_num only at hi
        exact hi
      norm_num only
      apply proper_prime_power_coefficient_lt_of_log (by norm_num only)
      · rw [hid]
        linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
      · rw [hid]
        linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
    · have he6 : h = 6 := Nat.le_antisymm hh6 (Nat.succ_le_of_lt he5)
      subst h
      have hid : Real.log (12 : ℝ) = 2 * Real.log 2 + Real.log 3 := by
        have hi := Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0)
        have hi4 := Real.log_pow (2 : ℝ) 2
        norm_num only at hi hi4
        rw [hi, hi4]
      norm_num only
      apply proper_prime_power_coefficient_lt_of_log (by norm_num only)
      · rw [hid]
        linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
      · rw [hid]
        linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]

/-- Under GRH, every index from four through six satisfies the original
leading-coefficient bound of Theorem 1.3 for all sufficiently large proper
powers of odd primes. The uniform gamma bound includes every prime base;
half the positive coefficient gap supplies the asymptotic error. This proves
the full odd proper-prime-power branch, without changing the paper's
statement or settling arbitrary moduli and prime moduli. -/
theorem theorem13_small_index_of_odd_proper_prime_power
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh4 : 4 ≤ h)
    (hh6 : h ≤ 6) :
    ∃ Q : ℕ,
      ∀ (p k : ℕ),
        p.Prime →
          p ≠ 2 →
          2 ≤ k →
          Q ≤ p ^ k →
          ∀ [NeZero p] [NeZero (p ^ k)] (H : Subgroup (ZMod (p ^ k))ˣ),
            H.index = h →
              ∃ r : ℕ,
                IsLeast (primesOutside (p ^ k) H) r ∧
                  (r : ℝ) <
                    (1 / 4) * (1 - 1 / (h : ℝ)) ^ 2 *
                      (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2 *
                      (Real.log (p ^ k : ℕ)) ^ 2 := by
  let C : ℝ :=
    (1 / 4) * (1 - 1 / (h : ℝ)) ^ 2 * (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2
  have hc : (659 / 4000 : ℝ) < C := proper_prime_power_coefficient_lt_small_index hh4 hh6
  let ε : ℝ := (C - 659 / 4000) / 2
  have hε : 0 < ε := by
    dsimp only [ε]; linarith only [hc]
  obtain ⟨Q, hQ⟩ := gamma_small_index_proper_prime_pow_asymptotic_bound hg h hh4 hh6 ε hε
  refine ⟨Q, ?_⟩
  intro p k hp hp2 hk hq _ _ H hH
  obtain ⟨r, hr, hb⟩ := hQ p k hp hp2 hk hq H hH
  have hm : (659 / 4000 : ℝ) + ε ≤ C := by
    dsimp only [ε]; linarith only [hc]
  exact ⟨r, hr, hb.trans_le (mul_le_mul_of_nonneg_right hm (sq_nonneg _))⟩

end PseudoPrime.LLS.PaperStatements
