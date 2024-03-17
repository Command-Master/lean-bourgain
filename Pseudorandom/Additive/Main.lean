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
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.SetLike.Fintype
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

open Classical Real BigOps Finset Pointwise

variable {α : Type*} [Field α] [Fintype α]
  (A B : Finset α)

theorem card_sq_div_add_card_le_energy :
    (A.card^2 * B.card^2 / (A + B).card ≤ additiveEnergy A B) := by
  -- apply Nat.div_le_of_le_mul
  have := calc additiveEnergy A B
    _ = (((A ×ˢ A) ×ˢ B ×ˢ B).filter fun x : (α × α) × α × α => x.1.1 + x.2.1 = x.1.2 + x.2.2).card := rfl
    _ = (((A ×ˢ B) ×ˢ A ×ˢ B).filter fun x : (α × α) × α × α => x.1.1 + x.1.2 = x.2.1 + x.2.2).card := by
      apply card_congr (fun ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ _ => ((a1, b1), (a2, b2)))
      · rename_i
          inst
          inst_1
        intro
          a
          ha
        simp_all only [mem_filter,
          mem_product]
        simp_all only [mem_filter,
          mem_product,
          and_self]
      · intro
          a
          b
          ha
          hb
          a_1
        simp_all only [Prod.mk.injEq]
        simp_all only [mem_filter,
          mem_product,
          and_self]
        unhygienic
          with_reducible
            aesop_destruct_products
        simp_all only
      · intro
          b
          a
        simp_all only [mem_filter,
          mem_product,
          exists_prop,
          Prod.exists]
        unhygienic
          with_reducible
            aesop_destruct_products
        simp_all only [Prod.mk.injEq]
        apply
          Exists.intro
        apply
          Exists.intro
        apply
          Exists.intro
        apply
          Exists.intro
        apply
          And.intro
        on_goal
          2 =>
          apply
            And.intro
        on_goal
          3 =>
          apply
            And.intro
        on_goal
          4 =>
          apply
            Eq.refl
        simp_all only [and_true]
        apply
          And.intro
        on_goal
          2 =>
          exact
            right
        simp_all only [and_self]
        on_goal
          2 =>
          simp_all only
        simp_all only [and_self]
    _ = ∑ x ∈ ((A ×ˢ B) ×ˢ A ×ˢ B), if x.1.1 + x.1.2 = x.2.1 + x.2.2 then 1 else 0 := by simp
    _ = ∑ x ∈ (A ×ˢ B), ∑ y ∈ (A ×ˢ B), if x.1 + x.2 = y.1 + y.2 then 1 else 0 := by rw [sum_product]
    _ = ∑ (a : α), ∑ x ∈ ((A ×ˢ B).filter fun x => x.1 + x.2 = a),
        ∑ y ∈ (A ×ˢ B), if x.1 + x.2 = y.1 + y.2 then 1 else 0 := by
      rw [sum_fiberwise (s := A ×ˢ B) (g := fun x => x.1 + x.2)]
    _ = ∑ (a : α), ∑ x ∈ ((A ×ˢ B).filter fun x => x.1 + x.2 = a),
        ∑ y ∈ (A ×ˢ B), if a = y.1 + y.2 then 1 else 0 := by
      congr
      ext a
      apply sum_congr
      rfl
      intro x hx
      simp at hx
      rcongr
      exact hx.2
    _ = ∑ a ∈ A+B, ∑ x ∈ ((A ×ˢ B).filter fun x => x.1 + x.2 = a),
        ∑ y ∈ (A ×ˢ B), if a = y.1 + y.2 then 1 else 0 := by
      apply Eq.symm
      apply sum_subset
      simp
      intro a _ ha
      suffices ((A ×ˢ B).filter fun x => x.1 + x.2 = a) = ∅ by simp [this]
      apply eq_empty_of_forall_not_mem
      intro x hx
      simp at hx
      have : x.1 + x.2 ∈ A + B := by
        rw [mem_add]
        exists x.1, hx.1.1, x.2, hx.1.2
      rw [hx.2] at this
      exact ha this
    _ ≥ 1 := sorry
  sorry

noncomputable def Stab (K : ℚ) (A : Finset α) := (univ : Finset α).filter fun a => (A + a • A).card ≤ K * A.card

lemma Stab_inv (h : a ∈ Stab K A) : 1/a ∈ Stab K A := by
  by_cases a = 0
  simp_all
  simp [Stab] at h
  simp [Stab]
  suffices (A + a • A).card = (A + a⁻¹ • A).card by rwa [←this]
  rw [add_comm]
  apply card_congr (fun x _ => x / a)
  · intros b hb
    simp [mem_add] at hb
    have ⟨y, hy, z, hz⟩ := hb
    simp [mem_smul_finset] at hy
    have ⟨y, hy⟩ := hy
    simp [mem_add]
    exists y
    constructor; exact hy.1
    exists z / a
    constructor
    · simp [mem_smul_finset]
      exists z
      constructor
      exact hz.1
      field_simp
    · field_simp
      rw [mul_comm, hy.2, hz.2]
  · intros _ _ _ _ a
    field_simp at a
    assumption
  · intros b hb
    exists a*b
    simp
    constructor
    · simp [mem_add] at hb
      have ⟨y, hy, z, hz, ht⟩ := hb
      simp [mem_smul_finset] at hz
      have ⟨z, hz⟩ := hz
      simp [mem_add]
      exists a * y
      constructor
      · simp [mem_smul_finset]
        exists y
        simp [hy]
      exists z
      field_simp at hz
      constructor; exact hz.1
      rw [←ht, hz.2]
      ring
    · field_simp; ring

lemma sub_le_add : (A - B).card ≤ ((A + B).card^3 / (A.card * B.card) : ℚ) := by
  by_cases A.Nonempty
  by_cases B.card ≠ 0
  calc ((A - B).card : ℚ)
    _ = ((A - B).card * B.card) / B.card := by field_simp
    _ ≤ ((A + B).card * (B + B).card) / B.card := by
      gcongr ?a / ?b
      norm_cast
      apply card_sub_mul_le_card_add_mul_card_add
      simp
    _ = ((A + B).card * (2 • B).card) / B.card := by rw [two_smul]
    _ ≤ ((A + B).card * (((A+B).card / A.card)^2 * A.card)) / B.card := by
        gcongr
        apply card_nsmul_le
        assumption
    _ = ((A + B).card^3 / (A.card * B.card) : ℚ) := by field_simp; ring_nf
  · simp_all
  · simp_all
  -- WHY DOES IT FAIL WHEN I REMOVED THIS COMMENT

lemma card_of_inv (a : α) (A : Finset α) (h : a ≠ 0) : (a • A).card = A.card := by
  apply Eq.symm
  apply card_congr (fun x _ => a * x)
  · intros a ha
    simp [mem_smul_finset]
    exists a
    simp [ha]
  · intros a b _ _ e
    simp_all
  · intros a ha
    simp [mem_smul_finset] at ha
    have ⟨y, hy⟩ := ha
    exists y
    simp
    assumption

lemma add_le_of_add_add (C : Finset α) : (B+C).card ≤ (A+B).card * (A+C).card := by
  sorry
  -- calc (B+C).card
  --   _ =

lemma Stab_neg (h : a ∈ Stab K A) : -a ∈ Stab (K^3) A := by
  by_cases A.card = 0
  · simp_all [Stab]
  have : A.Nonempty := by apply nonempty_of_ne_empty; simp_all
  by_cases a = 0
  simp_all [Stab]
  have : 1 ≤ K := by
    by_contra! nh
    have := calc
      (A.card : ℚ) ≤ K * A.card := by assumption
      _ < 1 * A.card := by gcongr
      _ = A.card := by simp
    linarith
  calc
    (A.card : ℚ) ≤ K * A.card := by assumption
    _ ≤ 1^2 * K * A.card := by simp
    _ ≤ K^2 * K * A.card := by gcongr
    _ = K^3 * A.card := by ring
  simp [Stab] at *
  rw [← sub_eq_add_neg]
  calc ((A - a • A).card : ℚ)
    _ ≤ (A + a • A).card^3 / (A.card * (a • A).card) := sub_le_add ..
    _ ≤ (K * A.card)^3 / (A.card * (a • A).card) := by gcongr
    _ = (K * A.card)^3 / (A.card * A.card) := by rwa [card_of_inv]
    _ = K^3 * A.card := by field_simp; ring
