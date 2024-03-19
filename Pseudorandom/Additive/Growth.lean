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

lemma min_eq (a b : ℚ) : min a b = if a ≤ b then a else b := rfl

lemma card_field_prime_pow : IsPrimePow (Fintype.card α) := by
  have ⟨p, n, h⟩ := FiniteField.card' α
  exists p, n
  simp [h, Nat.Prime.prime]

lemma two_le_card_field : 2 ≤ Fintype.card α := IsPrimePow.two_le card_field_prime_pow


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
    sorry
    -- have ⟨a, h1, h2⟩ := this
    -- exists a
    -- have mulnE : (a • A).Nonempty := by simp; assumption
    -- have en_pos : 0 < E[A, a • A] := additiveEnergy_pos (by assumption) mulnE
    -- calc ((A + a • A).card : ℚ)
    --   _ = ((A + a • A).card * E[A, a • A]) / E[A, a • A] := by field_simp
    --   _ ≥ (A.card^2 * (a • A).card^2) / E[A, a • A] := by
    --     gcongr ?X / _
    --     norm_cast
    --     apply le_card_add_mul_additiveEnergy
    --   _ = (A.card^2 * A.card^2) / E[A, a • A] := by
    --     rwa [card_of_inv]
    --   _ ≥ (A.card^2 * A.card^2) / (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) := by
    --     gcongr
    --   _ ≥ (min (A.card^2) (Fintype.card α)) / 2 := by
    --     by_cases h : A.card^2 < Fintype.card α
    --     · simp [le_of_lt h]
    --       calc ((A.card^2 * A.card^2) / (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) : ℚ)
    --         _ ≥ (A.card^2 * A.card^2) / (A.card^2 + A.card^4 / A.card^2) := by
    --           gcongr
    --           apply add_pos_of_pos_of_nonneg
    --           · apply pow_pos
    --             norm_cast
    --             exact ane.card_pos
    --           · apply div_nonneg
    --             assumption
    --             simp
    --             exact Nat.one_le_of_lt h
    --           · simp [mul_sub]
    --             ring_nf
    --             simp
    --           · norm_cast
    --             rw [Int.subNatNat_eq_coe]
    --             apply Int.le_of_lt_add_one
    --             simp
    --             norm_cast
    --         _ = A.card^2 / 2 := by field_simp; ring
    --     · simp at h
    --       simp [h]
    --       apply le_of_sub_nonneg
    --       have : (A.card^2 * A.card^2) / (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) - (Fintype.card α / 2) =
    --         ((Fintype.card α -2) * (A.card^2 - Fintype.card α) / (2 * (Fintype.card α + A.card^2 - 2)) : ℚ) := by
    --         generalize A.card = x at t1 t2 t3 t4
    --         field_simp
    --         ring_nf
    --       rw [this]
    --       apply div_nonneg
    --       apply mul_nonneg
    --       simp [t1]
    --       simp
    --       norm_cast
    --       simp
    --       norm_cast
    --       calc
    --         2 ≤ Fintype.card α := t1
    --         _ ≤ Fintype.card α + A.card^2 := by simp
  suffices (∑ a : α, if a ≠ 0 then E[A, a • A] else 0 : ℚ) ≤ A.card^2 * (Fintype.card α - 1) + A.card^2 * (A.card^2 - 1) by
    sorry
    -- by_contra! nh
    -- suffices A.card^2 * (Fintype.card α - 1) + A.card^2 * (A.card^2 - 1) < (∑ a : α, if a ≠ 0 then E[A, a • A] else 0 : ℚ) by linarith
    -- calc (A.card^2 * (Fintype.card α - 1) + A.card^2 * (A.card^2 - 1) : ℚ)
    --   _ = (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) * (Fintype.card α - 1) := by field_simp
    --   _ = ∑ a : α, (A.card^2 + A.card^2 * (A.card^2 - 1) / (Fintype.card α - 1)) * (if a ≠ 0 then 1 else 0 : ℚ) := by
    --     simp only [←mul_sum, sum_boole]
    --     congr
    --     have : (univ.filter fun x => x ≠ 0) = (univ : Finset α) \ {0} := by
    --       ext
    --       simp only [ne_eq, mem_filter, mem_univ, true_and, mem_sdiff, mem_singleton]
    --     rw [this]
    --     rw [Finset.cast_card_sdiff]
    --     simp
    --     rfl
    --     simp
    --   _ < ∑ a : α, (if a ≠ 0 then E[A, a • A] else 0 : ℚ) := by
    --     apply sum_lt_sum
    --     intro i _
    --     split
    --     · apply le_of_lt
    --       rw [mul_one]
    --       apply nh
    --       assumption
    --     · simp
    --     exists 1
    --     simp only [mem_univ, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, mul_one,
    --       true_and]
    --     apply nh 1
    --     exact one_ne_zero
  norm_cast
  sorry
  · simp_all
