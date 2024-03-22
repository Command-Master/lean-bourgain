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

variable {α : Type*} [Field α] [Fintype α]
  (A B C : Finset α)

open NNRat Classical Real BigOps Finset Pointwise

lemma card_field_prime_pow : IsPrimePow (Fintype.card α) := by
  have ⟨p, n, h⟩ := FiniteField.card' α
  exists p, n
  simp [h, Nat.Prime.prime]

lemma two_le_card_field : 2 ≤ Fintype.card α := IsPrimePow.two_le card_field_prime_pow

set_option maxHeartbeats 300000

theorem exists_grower : ∃ (a : α), (A + a • A).card ≥ ((min (A.card^2) (Fintype.card α)) / 2 : ℚ) := by
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
    -- sorry
    have ⟨a, h1, h2⟩ := this
    exists a
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
              -- apply add_pos_of_pos_of_nonneg
              -- · apply pow_pos
              --   norm_cast
              --   exact ane.card_pos
              -- · apply div_nonneg
              --   assumption
              --   simp
              --   exact Nat.one_le_of_lt h
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
    -- sorry
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
  · simp_all

#print exists_grower

theorem GUS (p : ℕ) [Fact (p.Prime)] (A : Finset (ZMod p)) : (3 • A^2 - 3 • A^2).card ≥ ((min (A.card^2) (Fintype.card α)) / 2 : ℚ) := by
  sorry
