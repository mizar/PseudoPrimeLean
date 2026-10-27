/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalResidues
public import Mathlib.Data.Finset.Max

/-! # Finite fibers of bounded rational residues -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A finite rational family in [a,b] with successive gaps at least d has
cardinality times d at most b-a+d. The nonnegative gap and interval hypotheses
are explicit. Induction on the largest point gives the packing estimate used
for residue fibers. -/
theorem finite_separated_card_mul_le (S : Finset ℚ) {a b d : ℚ} (hd : 0 ≤ d) (hab : a ≤ b)
    (hbox : ∀ x ∈ S, a ≤ x ∧ x ≤ b) (hgap : ∀ x ∈ S, ∀ y ∈ S, x < y → d ≤ y - x) :
    (S.card : ℚ) * d ≤ b - a + d := by
  classical
    induction S using Finset.induction_on_max generalizing b with
  | empty =>
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith only [hab, hd]
  | insert x S hmax ih =>
    have hx := hbox x (Finset.mem_insert_self x S)
    have hxS : x ∉ S := fun h ↦ (lt_irrefl x) (hmax x h)
    rw [Finset.card_insert_of_notMem hxS, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.card_empty, Nat.cast_zero, zero_mul, zero_add]
      linarith only [hab]
    · obtain ⟨y, hy⟩ := hne
      have hS : ∀ y ∈ S, a ≤ y ∧ y ≤ x - d := by
        intro y hy
        have hb := hbox y (Finset.mem_insert_of_mem hy)
        have hg := hgap y (Finset.mem_insert_of_mem hy) x (Finset.mem_insert_self x S) (hmax y hy)
        exact ⟨hb.1, by linarith only [hg]⟩
      have hax : a ≤ x - d := (hS y hy).1.trans (hS y hy).2
      have hi :=
        ih hax hS
          (fun y hy z hz ↦ hgap y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz))
      linarith only [hi, hx.2]

/-- Two ordered positive bounded fractions at the same residue modulo M
have transformed separation at least M/(4U²). Raw representations need not
have invertible denominators. A nonzero determinant is divisible by M;
the map q/(1+q) bounds its denominator by 4U². -/
theorem boundedRationalResidue_separation {M U : ℕ} {q r : ℚ} {u : ZMod M}
    (hq : boundedRationalResidue M U q u) (hr : boundedRationalResidue M U r u) (hqr : q < r) :
    (M : ℚ) ≤ 4 * (U : ℚ) ^ 2 * (r / (1 + r) - q / (1 + q)) := by
  obtain ⟨a, b, ha, haU, hb, hbU, rfl, hu⟩ := hq
  obtain ⟨c, d, hc, hcU, hd, hdU, rfl, hv⟩ := hr
  have hbQ : (0 : ℚ) < b := Nat.cast_pos.mpr hb
  have hdQ : (0 : ℚ) < d := Nat.cast_pos.mpr hd
  have haQ : (0 : ℚ) < a := Nat.cast_pos.mpr ha
  have hcQ : (0 : ℚ) < c := Nat.cast_pos.mpr hc
  have hcross : (a : ℚ) * d < c * b := (div_lt_div_iff₀ hbQ hdQ).mp hqr
  have hdetQ : (0 : ℚ) < c * b - a * d := sub_pos.mpr hcross
  have hdetZ : (0 : ℤ) < (c : ℤ) * b - a * d := by
    apply (Int.cast_pos (R := ℚ)).mp
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hdetQ
  have hz : (((c : ℤ) * b - a * d : ℤ) : ZMod M) = 0 := by
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
      Int.cast_natCast, Int.cast_natCast, ← hu, ← hv]
    ring
  have hm := Int.le_abs_of_dvd (ne_of_gt hdetZ) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  rw [abs_of_pos hdetZ] at hm
  have hmQ : (M : ℚ) ≤ c * b - a * d := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using (Int.cast_le (R := ℚ)).mpr hm
  have hab : (0 : ℚ) < a + b := add_pos haQ hbQ
  have hcd : (0 : ℚ) < c + d := add_pos hcQ hdQ
  have hrep (v w : ℕ) (hw : (0 : ℚ) < w) :
    ((v : ℚ) / w) / (1 + (v : ℚ) / w) = (v : ℚ) / (v + w) := by
    rw [one_add_div (ne_of_gt hw), div_div_div_cancel_right₀ (ne_of_gt hw), add_comm]
  rw [hrep a b hbQ, hrep c d hdQ, div_sub_div _ _ (ne_of_gt hcd) (ne_of_gt hab)]
  have hprod : (c + d : ℚ) * (a + b) ≤ 4 * (U : ℚ) ^ 2 := by
    have haUQ : (a : ℚ) ≤ U := Nat.cast_le.mpr haU
    have hbUQ : (b : ℚ) ≤ U := Nat.cast_le.mpr hbU
    have hcUQ : (c : ℚ) ≤ U := Nat.cast_le.mpr hcU
    have hdUQ : (d : ℚ) ≤ U := Nat.cast_le.mpr hdU
    have h :=
      mul_le_mul (add_le_add hcUQ hdUQ) (add_le_add haUQ hbUQ) (le_of_lt hab)
        (by linarith only [hcQ, hdQ, hcUQ, hdUQ] : (0 : ℚ) ≤ U + U)
    nlinarith only [h]
  have hden : (0 : ℚ) < (c + d) * (a + b) := mul_pos hcd hab
  have hnum : (c : ℚ) * (a + b) - (c + d) * a = c * b - a * d := by ring
  rw [hnum]
  have hratio : (0 : ℚ) ≤ (c * b - a * d) / ((c + d) * (a + b)) := (div_pos hdetQ hden).le
  have hmul := mul_le_mul_of_nonneg_right hprod hratio
  have he : ((c + d) * (a + b)) * ((c * b - a * d) / ((c + d) * (a + b))) = (c * b - a * d : ℚ) :=
    mul_div_cancel₀ _ (ne_of_gt hden)
  rw [he] at hmul
  exact hmQ.trans hmul

/-- A finite family of positive height-U fractions at one residue modulo M
satisfies card(S)*M ≤ M+4U², without a short-height or primality assumption.
Pack q/(1+q) into [0,1] using determinant separation. This replaces injectivity
when product heights exceed the square-root modulus. -/
theorem boundedRationalResidue_fiber_card_mul_modulus_le {M U : ℕ} (S : Finset ℚ) (u : ZMod M)
    (hS : ∀ q ∈ S, boundedRationalResidue M U q u) : S.card * M ≤ M + 4 * U ^ 2 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.zero_mul]
    exact Nat.zero_le _
  have hpos : ∀ q ∈ S, (0 : ℚ) < q := by
    intro q hq
    obtain ⟨a, b, ha, _, hb, _, rfl, _⟩ := hS q hq
    exact div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)
  obtain ⟨q, hq⟩ := hne
  obtain ⟨a, b, ha, haU, hb, hbU, heq, hu⟩ := hS q hq
  have hU : (0 : ℚ) < U := Nat.cast_pos.mpr (hb.trans_le hbU)
  have hC : (0 : ℚ) < 4 * (U : ℚ) ^ 2 := mul_pos (by norm_num only) (sq_pos_of_pos hU)
  let f : ℚ → ℚ := fun q ↦ q / (1 + q)
  have hden : ∀ q ∈ S, (0 : ℚ) < 1 + q := fun q hq ↦ add_pos (by norm_num only) (hpos q hq)
  have hinj : Set.InjOn f (↑S : Set ℚ) := by
    intro q hq r hr he
    have hc := (div_eq_div_iff (ne_of_gt (hden q hq)) (ne_of_gt (hden r hr))).mp he
    nlinarith only [hc]
  have hbox : ∀ x ∈ S.image f, (0 : ℚ) ≤ x ∧ x ≤ 1 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨(div_pos (hpos q hq) (hden q hq)).le, (div_le_one (hden q hq)).mpr (by linarith only)⟩
  have hgap : ∀ x ∈ S.image f, ∀ y ∈ S.image f, x < y → (M : ℚ) / (4 * (U : ℚ) ^ 2) ≤ y - x := by
    intro x hx y hy hxy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    have hc := (div_lt_div_iff₀ (hden q hq) (hden r hr)).mp hxy
    have hqr : q < r := by nlinarith only [hc]
    exact
      (div_le_iff₀ hC).mpr
        (by simpa only [mul_comm] using boundedRationalResidue_separation (hS q hq) (hS r hr) hqr)
  have hp :=
    finite_separated_card_mul_le (S.image f) (div_nonneg (Nat.cast_nonneg M) hC.le)
      (by norm_num only : (0 : ℚ) ≤ 1) hbox hgap
  rw [Finset.card_image_iff.mpr hinj, sub_zero, ← mul_div_assoc, one_add_div (ne_of_gt hC)] at hp
  have hh := (div_le_div_iff_of_pos_right hC).mp hp
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, add_comm] using hh

/-- If each height-U fraction has a residue in a finite indexed family, its
cardinality times M is at most the index count times M+4U². Choose one residue
per fraction and sum the proved fiber bounds. No injectivity of the residue
family is required; this is the interface for finite multiplicative subgroups. -/
theorem boundedRationalResidue_family_card_mul_modulus_le {ι : Type*} [Fintype ι] {M U : ℕ}
    (S : Finset ℚ) (v : ι → ZMod M) (hS : ∀ q ∈ S, ∃ i, boundedRationalResidue M U q (v i)) :
    S.card * M ≤ Fintype.card ι * (M + 4 * U ^ 2) := by
  classical
  choose f hf using (fun q : S ↦ hS q.val q.property)
  have hsum :=
    Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := f)
      (fun _ _ ↦ Finset.mem_univ _)
  have hb : ∀ i : ι, ((Finset.univ.filter (fun q : S ↦ f q = i)).card) * M ≤ M + 4 * U ^ 2 := by
    intro i
    let T := (Finset.univ.filter (fun q : S ↦ f q = i)).image Subtype.val
    have hT : ∀ q ∈ T, boundedRationalResidue M U q (v i) := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      have he := (Finset.mem_filter.mp hr).2
      rw [← he]
      exact hf r
    have hh := boundedRationalResidue_fiber_card_mul_modulus_le T (v i) hT
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
    exact hh
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hb i)
  rw [← Finset.sum_mul, ← hsum] at ht
  simpa only [Finset.card_univ, Fintype.card_coe, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using
    ht

end PseudoPrime.NumberTheory.Heilbronn
