import Mathlib.Data.Nat.Prime
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Prereqs.Expect.Basic
import LeanAPAP.Mathlib.Combinatorics.Additive.Energy
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.SetLike.Fintype
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Pseudorandom.Additive.Main
import Mathlib.Algebra.IsPrimePow
import Mathlib.FieldTheory.Finite.Basic

variable {α : Type*} [Field α] [Fintype α] [DecidableEq α]
  (A B C : Finset α)

open NNRat Real BigOps Finset Pointwise

lemma card_field_prime_pow : IsPrimePow (Fintype.card α) := by
  have ⟨p, n, h⟩ := FiniteField.card' α
  exists p, n
  simp [h, Nat.Prime.prime]

lemma two_le_card_field : 2 ≤ Fintype.card α := IsPrimePow.two_le card_field_prime_pow

set_option maxHeartbeats 300000

theorem exists_grower : ∃ (a : α), a ≠ 0 ∧ (A + a • A).card ≥ ((min (A.card^2) (Fintype.card α)) / 2 : ℚ) := by
  by_cases ane : A.Nonempty
  have vnn : 0 ≤ (A.card^2 * (A.card^2 - 1) : ℚ) := by
    apply mul_nonneg
    simp
    simp
    exact Nat.one_le_of_lt ane.card_pos
  have t1 : 2 ≤ Fintype.card α := two_le_card_field
  have t3 : 0 < (Fintype.card α - 1 : ℚ) := by
    simp
    linarith
  have t2 : 0 < (A.card^2 * (Fintype.card α - 1) + A.card^2 * (A.card^2 - 1) : ℚ) := by
    apply add_pos_of_pos_of_nonneg
    apply mul_pos
    apply pow_pos
    norm_cast
    exact ane.card_pos
    exact t3
    assumption
  have t4 : 0 < (2 * (Fintype.card α + A.card^2 - 2) : ℚ) := by
    simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left, sub_pos]
    norm_cast
    have : 1 ≤ A.card^2 := Nat.one_le_of_lt <| pow_pos ane.card_pos 2
    linarith
  suffices ∃ (a : α), a ≠ 0 ∧ E[A, a • A] ≤ A.card^2 + (A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1) : ℚ) by
    have ⟨a, h1, h2⟩ := this
    exists a
    refine' ⟨h1, _⟩
    have mulnE : (a • A).Nonempty := by simp; assumption
    have en_pos : 0 < E[A, a • A] := additiveEnergy_pos (by assumption) mulnE
    calc ((A + a • A).card : ℚ)
      _ = ((A + a • A).card * E[A, a • A]) / E[A, a • A] := by field_simp
      _ ≥ (A.card^2 * (a • A).card^2) / E[A, a • A] := by
        gcongr ?X / _
        norm_cast
        apply le_card_add_mul_additiveEnergy
      _ = (A.card^2 * A.card^2) / E[A, a • A] := by
        rwa [card_of_inv]
      _ ≥ (A.card^2 * A.card^2) / (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) := by
        gcongr
      _ ≥ (min (A.card^2) (Fintype.card α)) / 2 := by
        by_cases h : A.card^2 < Fintype.card α
        · simp [le_of_lt h]
          calc ((A.card^2 * A.card^2) / (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) : ℚ)
            _ ≥ (A.card^2 * A.card^2) / (A.card^2 + A.card^4 / A.card^2) := by
              gcongr
              · simp [mul_sub]
                ring_nf
                simp
              · norm_cast
                rw [Int.subNatNat_eq_coe]
                apply Int.le_of_lt_add_one
                simp
                norm_cast
            _ = A.card^2 / 2 := by field_simp; ring
        · simp at h
          simp [h]
          apply le_of_sub_nonneg
          have : (A.card^2 * A.card^2) / (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) - (Fintype.card α / 2) =
            ((Fintype.card α -2) * (A.card^2 - Fintype.card α) / (2 * (Fintype.card α + A.card^2 - 2)) : ℚ) := by
            generalize A.card = x at t1 t2 t3 t4
            field_simp
            ring_nf
          rw [this]
          apply div_nonneg
          apply mul_nonneg
          simp [t1]
          simp
          norm_cast
          simp
          norm_cast
          calc
            2 ≤ Fintype.card α := t1
            _ ≤ Fintype.card α + A.card^2 := by simp
  suffices (∑ a : α, if a ≠ 0 then E[A, a • A] else 0 : ℚ) ≤ A.card^2 * (Fintype.card α - 1) + A.card^2 * (A.card^2 - 1) by
    by_contra! nh
    suffices A.card^2 * (Fintype.card α - 1) + A.card^2 * (A.card^2 - 1) < (∑ a : α, if a ≠ 0 then E[A, a • A] else 0 : ℚ) by linarith
    calc (A.card^2 * (Fintype.card α - 1) + A.card^2 * (A.card^2 - 1) : ℚ)
      _ = (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) * (Fintype.card α - 1) := by field_simp
      _ = ∑ a : α, (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) * (if a ≠ 0 then 1 else 0 : ℚ) := by
        simp only [←mul_sum, sum_boole]
        congr
        have : (univ.filter fun x => x ≠ 0) = (univ : Finset α) \ {0} := by
          ext
          simp only [ne_eq, mem_filter, mem_univ, true_and, mem_sdiff, mem_singleton]
        rw [this]
        rw [Finset.cast_card_sdiff]
        simp
        rfl
        simp
      _ < ∑ a : α, (if a ≠ 0 then E[A, a • A] else 0 : ℚ) := by
        apply sum_lt_sum
        intro i _
        split
        · apply le_of_lt
          rw [mul_one]
          apply nh
          assumption
        · simp
        exists 1
        simp only [mem_univ, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, mul_one,
          true_and]
        apply nh 1
        exact one_ne_zero
  calc (∑ a : α, if a ≠ 0 then E[A, a • A] else 0 : ℚ)
    _ = ∑ a, (if a ≠ 0 then ((((A ×ˢ A) ×ˢ A ×ˢ A)).filter
    fun x : (α × α) × α × α => x.1.1 + a * x.1.2 = x.2.1 + a * x.2.2).card else 0 : ℚ) := by
      apply sum_congr
      rfl
      intro a _
      split
      norm_cast
      apply additive_mul_eq
      assumption
      rfl
    _ = ∑ a, (if a ≠ 0 then (∑ x ∈ ((A ×ˢ A) ×ˢ A ×ˢ A),
        if x.1.1 + a * x.1.2 = x.2.1 + a * x.2.2 then 1 else 0) else 0 : ℚ) := by simp
    _ = ∑ a, (∑ x ∈ ((A ×ˢ A) ×ˢ A ×ˢ A),
        if a ≠ 0 ∧ x.1.1 + a * x.1.2 = x.2.1 + a * x.2.2 then 1 else 0 : ℚ) := by
      apply sum_congr
      rfl
      intro a _
      split
      congr
      ext
      simp_all
      apply Eq.symm
      apply sum_eq_zero
      intro x
      simp_all
    _ = ∑ x ∈ ((A ×ˢ A) ×ˢ A ×ˢ A), ∑ a,
        if a ≠ 0 ∧ x.1.1 + a * x.1.2 = x.2.1 + a * x.2.2 then 1 else 0 := by rw [sum_comm]
    _ = ∑ x₁ ∈ A ×ˢ A, ∑ x₂ ∈ A ×ˢ A, ∑ a,
        if a ≠ 0 ∧ x₁.1 + a * x₁.2 = x₂.1 + a * x₂.2 then 1 else 0 := by rw [sum_product' (f := fun (x₁ x₂ : α × α) => ∑ a : α, if a ≠ 0 ∧ x₁.1 + a * x₁.2 = x₂.1 + a * x₂.2 then 1 else 0)]
    _ = ∑ x₁ ∈ A ×ˢ A, ((∑ a,
        if a ≠ 0 ∧ x₁.1 + a * x₁.2 = x₁.1 + a * x₁.2 then 1 else 0) + ∑ x₂ ∈ A ×ˢ A \ {x₁}, ∑ a,
        if a ≠ 0 ∧ x₁.1 + a * x₁.2 = x₂.1 + a * x₂.2 then 1 else 0) := by
      apply sum_congr
      rfl
      intro x hx
      rw [sum_eq_add_sum_diff_singleton hx]
    _ = ∑ x₁ ∈ A ×ˢ A, ((∑ a : α, if a ≠ 0 then 1 else 0) + (∑ x₂ ∈ A ×ˢ A \ {x₁}, ∑ a,
        if a ≠ 0 ∧ x₁.1 + a * x₁.2 = x₂.1 + a * x₂.2 then 1 else 0)) := by simp
    _ ≤ ∑ x₁ ∈ A ×ˢ A, ((∑ a : α, if a ≠ 0 then 1 else 0) + (∑ x₂ ∈ A ×ˢ A \ {x₁}, 1)) := by
      gcongr with x₁ _ x₂ _
      have ⟨x11, x12⟩ := x₁
      have ⟨x21, x22⟩ := x₂
      simp
      rw [Finset.card_le_one]
      intros a ha b hb
      simp at ha
      simp at hb
      have : (a - b) * (x12 - x22) = 0 := by linear_combination ha.2 - hb.2
      apply eq_of_sub_eq_zero
      simp at this
      cases this
      · assumption
      · rename_i e1
        apply eq_of_sub_eq_zero at e1
        exfalso
        rw [e1] at ha
        have : x11 = x21 := by linear_combination ha.2
        simp_all
    _ = ∑ x₁ ∈ A ×ˢ A, ((Fintype.card α - 1) + ((A ×ˢ A).card - 1) : ℚ) := by
      apply sum_congr
      rfl
      intro x hx
      congr
      · simp only [sum_boole]
        have (x : α) : ¬ x = 0 ↔ (x ∉ ({0} : Finset α)) := by simp
        simp [this]
        rw [← sdiff_eq_filter]
        rw [cast_card_sdiff]
        simp
        rfl
        simp
      · simp
        rw [cast_card_sdiff]
        simp
        simp [hx]
    _ = A.card^2 * (Fintype.card α - 1) + A.card^2 * (A.card^2 - 1) := by
      simp
      ring_nf
  · exists 1
    simp_all

theorem GUS (p : ℕ) [Fact (p.Prime)] (A : Finset (ZMod p)) : (3 • A^2 - 3 • A^2).card ≥
    ((min (A.card^2) p) / 2 : ℚ) := by
  by_cases cardb : A.card > 1
  have : A.Nonempty := by
    rw [← card_pos]
    omega
  let B := (A - A) / (A - A)
  by_cases univ ⊆ B
  ·
    rw [ge_iff_le]
    suffices ((min (A.card^2) p) / 2 : ℚ) ≤ (2 • A^2 - 2 • A^2).card by
      refine' this.trans _
      have : 3 • A^2 - 3 • A^2 = 2 • A^2 - 2 • A^2 + (A^2 - A^2) := by
        simp [sub_eq_add_neg]
        rw [← neg_nsmul]
        rw [← neg_nsmul]
        generalize - A^2 = C
        abel
      rw [this]
      norm_cast
      apply card_le_card_add_right
      simp [sq]
      assumption
    obtain ⟨g, ⟨gnz, hg⟩⟩ := exists_grower A
    rw [ZMod.card] at hg
    refine' hg.trans _
    have : g ∈ B := by simp_all
    simp only [mem_div, mem_sub, exists_exists_and_exists_and_eq_and, B] at this
    obtain ⟨a, ha, b, hb, c, hc, d, hd, h⟩ := this
    have : c - d ≠ 0 := by
      intro v
      simp [v] at h
      exact gnz h.symm
    rw [← h]
    conv =>
      lhs
      arg 1
      rw [← card_of_inv _ (c - d) this]
    gcongr
    rw [subset_iff]
    intro x hx
    simp only [mem_smul_finset, mem_add, smul_eq_mul, exists_exists_and_eq_and,
      exists_exists_and_exists_and_eq_and] at hx
    obtain ⟨e, he, f, hf, h⟩ := hx
    conv at h =>
      lhs
      tactic =>
        change _ = (c-d)*e + (a-b) * f
        field_simp
        ring
    rw [← h]
    rw [sub_mul, sub_mul]
    simp only [sq, two_nsmul]
    simp only [mem_sub, mem_add, mem_mul, exists_exists_and_exists_and_eq_and]
    exists c*e + a*f
    constructor
    exists c, hc, e, he, a, ha, f, hf
    exists d*e + b*f
    constructor
    exists d, hd, e, he, b, hb, f, hf
    ring
  ·
    let B' := Bᶜ
    have : B'.Nonempty := by
      rw [← compl_ne_univ_iff_nonempty]
      simp_all [B']
    have : B.Nonempty := by simp_all [B]
    have ⟨x, hx⟩ := this.bex
    let x₂ := (B'.image fun y => (y - x).val).min' (by simp_all)
    have mm : x₂ ∈ (B'.image fun y => (y - x).val) := min'_mem (B'.image fun y => (y - x).val) (by simp_all)
    have x₂_neq_zero : x₂ ≠ 0 := fun v => by
      simp only [v, mem_image, ZMod.val_eq_zero] at mm
      obtain ⟨m, hm1, hm2⟩ := mm
      apply eq_of_sub_eq_zero at hm2
      rw [hm2] at hm1
      simp [B'] at hm1
      contradiction
    simp only [mem_image] at mm
    have ⟨m, hm1, hm2⟩ := mm
    have t2 : x + x₂ ∈ B' := by
      have : ((m-x).val : ZMod p) = (x₂ : ZMod p) := by rw [hm2]
      simp [sub_eq_iff_eq_add] at this
      rw [this, add_comm] at hm1
      exact hm1
    have t1 : x + x₂ - 1 ∈ B := by
      by_contra! nh
      have : x₂ - 1 ∈ (B'.image fun y => (y - x).val) := by
        simp
        exists x + (x₂ - 1 : ℕ)
        constructor
        rw [Nat.cast_sub]
        simp [B', nh, ← add_sub_assoc]
        omega
        ring_nf
        apply ZMod.val_cast_of_lt
        have : x₂ < p := by
          rw [← hm2]
          apply ZMod.val_lt
        omega
      have : x₂ ≤ x₂ - 1 := Finset.min'_le (B'.image fun y => (y - x).val) _ this
      omega
    rw [ge_iff_le]
    let v := x + x₂
    change v ∈ B' at t2
    simp only [B', mem_compl] at t2
    change v - 1 ∈ B at t1
    simp [B, mem_div, mem_sub] at t1
    have ⟨a, ha, b, hb, c, hc, d, hd, h⟩ := t1
    clear mm hm1 hm2 hx x₂_neq_zero t1
    have diff_ne_zero : c - d ≠ 0 := by
      intro h₂
      rw [h₂] at h
      simp at h
      have h : v = 1 := by linear_combination -h
      rw [h] at t2
      suffices 1 ∈ B by exact t2 this
      have ⟨a, ha, b, hb, neq⟩ := one_lt_card.mp cardb
      have : a - b ≠ 0 := sub_ne_zero_of_ne neq
      have : (a - b) / (a - b) = 1 := by field_simp
      rw [← this]
      simp [B, div_mem_div, sub_mem_sub, ha, hb]
    calc ((min (A.card^2) p) / 2 : ℚ)
      _ ≤ (A.card^2) / 2 := by gcongr; simp
      _ ≤ A.card^2 := by simp
      _ = (A + v • A).card := by
        norm_cast
        rw [sq, ← card_product]
        apply card_congr (fun ⟨x1, x2⟩ _ => x1 + v • x2)
        · intros
          apply add_mem_add
          simp_all
          apply smul_mem_smul_finset
          simp_all
        · rintro ⟨e₁, e₂⟩ ⟨f₁, f₂⟩ he hf h₂
          simp only [mem_product] at he hf
          simp only [smul_eq_mul] at h₂
          have : f₂ = e₂ := by
            by_contra! nh
            have : e₁ - f₁ = v * (f₂ - e₂) := by linear_combination h₂
            apply sub_ne_zero_of_ne at nh
            have : v = (e₁ - f₁) / (f₂ - e₂) := by field_simp [this]
            suffices v ∈ B by exact t2 this
            rw [this]
            simp [B, he, div_mem_div, sub_mem_sub, hf]
          rw [this] at h₂
          have : e₁ = f₁ := by linear_combination h₂
          simp_all
        · intro b hb
          simp only [mem_add, mem_smul_finset, smul_eq_mul, exists_exists_and_eq_and] at hb
          have ⟨y, hy, a, ha, v⟩ := hb
          exists (y, a)
          simp [v, ha, hy]
      _ = (A + ((a - b) / (c - d) + 1) • A).card := by
        congr
        linear_combination h.symm
      _ = ((c - d) • (A + ((a - b) / (c - d) + 1) • A)).card := by
        norm_cast
        apply Eq.symm
        apply card_of_inv
        assumption
      _ = ((c - d) • A + (c - d) • ((a - b) / (c - d) + 1) • A).card := by
        simp
      _ = ((c - d) • A + ((a - b) + (c - d)) • A).card := by
        congr 3
        rw [← smul_assoc]
        congr 1
        field_simp
        ring
      _ ≤ ((c - d) • A + ((a - b) • A + (c - d) • A)).card := by
        gcongr
        apply add_subset_add_left
        apply add_smul_subset_smul_add_smul
      _ ≤ ((c • A - d • A) + ((a • A - b • A) + (c • A - d • A))).card := by
        gcongr
        apply add_subset_add
        apply sub_smul_subset_smul_sub_smul
        apply add_subset_add
        apply sub_smul_subset_smul_sub_smul
        apply sub_smul_subset_smul_sub_smul
      _ ≤ ((A * A - A * A) + ((A * A - A * A) + (A * A - A * A))).card := by
        gcongr
        apply add_subset_add
        · apply sub_subset_sub
          · apply smul_finset_subset_smul
            assumption
          · apply smul_finset_subset_smul
            assumption
        apply add_subset_add
        · apply sub_subset_sub
          · apply smul_finset_subset_smul
            assumption
          · apply smul_finset_subset_smul
            assumption
        · apply sub_subset_sub
          · apply smul_finset_subset_smul
            assumption
          · apply smul_finset_subset_smul
            assumption
      _ = _ := by
        congr
        simp [← sq, sub_eq_add_neg]
        rw [← neg_nsmul]
        generalize -A^2 = B
        abel_nf
  · by_cases A.card = 0
    · simp_all
    · have : A.card = 1 := by omega
      calc ((min (A.card^2) p) / 2 : ℚ)
        _ ≤ 1 / 2 := by gcongr; simp [this]
        _ ≤ 1 := by norm_num
        _ ≤ _ := by
          norm_cast
          rw [Nat.one_le_iff_ne_zero]
          have : 3•A^2 - 3•A^2 = ((A*A + A*A + A*A) - (A*A + A*A + A*A)) := by
            congr <;> (simp [sq]; abel_nf)
          rw [this]
          apply card_ne_zero_of_mem (a := 0)
          simp only [sub_self, zero_mem_sub_iff, disjoint_self, bot_eq_empty, add_eq_empty,
            mul_eq_empty, or_self]
          apply Nonempty.ne_empty
          rw [← card_pos]
          simp_all
