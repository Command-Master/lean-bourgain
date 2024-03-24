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
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Pseudorandom.Additive.Main

variable {α : Type*} [Field α] [Fintype α] [DecidableEq α]
  (A B C : Finset α)

open NNRat Real BigOps Finset Pointwise

noncomputable def Stab (K : ℚ) (A : Finset α) := (univ : Finset α).filter fun a => (A + a • A).card ≤ K * A.card

lemma Stab_inv (h : a ∈ Stab K A) : 1/a ∈ Stab K A := by
  by_cases a = 0
  · simp_all
  simp [Stab] at h
  simp [Stab]
  calc ((A + a⁻¹ • A).card : ℚ)
    _ = (a • (A + a⁻¹ • A)).card := by rwa [card_of_inv]
    _ = (a • A + a • a⁻¹ • A).card := by simp
    _ = (a • A + (a • a⁻¹) • A).card := by rw [smul_assoc]
    _ = (a • A + (1 : α) • A).card := by field_simp
    _ = (a • A + A).card := by simp
    _ = (A + a • A).card := by rw [add_comm]
    _ ≤ K * A.card := by assumption

lemma one_le_of_mem (hA : A.Nonempty) (h : a ∈ Stab K A) : 1 ≤ K := by
  by_contra! nh
  simp [Stab] at h
  have := calc
    (A.card : ℚ) ≤ (A + a • A).card := by
      norm_cast
      apply card_le_card_add_right
      simp [hA]
    _ ≤ K * A.card := by assumption
    _ < 1 * A.card := by gcongr
    _ = A.card := by simp
  linarith

lemma Stab_neg (h : a ∈ Stab K A) : -a ∈ Stab (K^3) A := by
  by_cases A.card = 0
  · simp_all [Stab]
  have : A.Nonempty := by apply nonempty_of_ne_empty; simp_all
  by_cases a = 0
  have := one_le_of_mem A this h
  simp_all [Stab]
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

lemma Stab_add (h₁ : a ∈ Stab K A) (h₂ : b ∈ Stab K A) : a + b ∈ Stab (K^9) A := by
  by_cases A.Nonempty
  have : 1 ≤ K := one_le_of_mem A (by assumption) h₁
  by_cases a ≠ 0
  simp_all only [Stab, mem_filter, mem_univ, true_and, ne_eq, ge_iff_le]
  calc ((A + (a + b) • A).card : ℚ)
    _ ≤ (A + (a • A + b • A)).card := by
      gcongr
      apply add_subset_add_left (s := A)
      rw [subset_iff]
      intros x hx
      rw [mem_smul_finset] at hx
      have ⟨y, hy⟩ := hx
      rw [mem_add]
      exists a • y
      constructor
      rw [mem_smul_finset]
      exists y
      exact ⟨hy.1, rfl⟩
      exists b • y
      constructor
      rw [mem_smul_finset]
      exists y
      exact ⟨hy.1, rfl⟩
      rw [←hy.2]
      simp
      ring_nf
    _ = (A + a • A + b • A).card := by abel_nf
    _ ≤ (b • A + A).card * (A + a • A).card^8 / (A.card^6 * (a • A).card^2) := by
      apply triple_add
    _ = (A + b • A).card * (A + a • A).card^8 / (A.card^6 * A.card^2) := by
      congr 4
      abel
      apply card_of_inv
      assumption
    _ ≤ (K * A.card) * (K * A.card)^8 / (A.card^6 * A.card^2) := by gcongr
    _ = K^9 * A.card := by field_simp; ring_nf
  · simp_all only [Stab, mem_filter, mem_univ, true_and, ne_eq, not_not, zero_add, ge_iff_le,
    zero_smul_finset, add_zero]
    calc
      ((A + b•A).card : ℚ) ≤ K * A.card := by assumption
      _ ≤ 1^8 * K * A.card := by simp
      _ ≤ K^8 * K * A.card := by gcongr
      _ = K^9 * A.card := by ring
  · simp_all [Stab]

lemma Stab_mul (h₁ : a ∈ Stab K A) (h₂ : b ∈ Stab K A) : a * b ∈ Stab (K^2) A := by
  by_cases ane : A.Nonempty
  have := one_le_of_mem A ane h₁
  by_cases h : a ≠ 0
  apply Stab_inv at h₁
  simp_all [Stab]
  calc ((A + (a * b) • A).card : ℚ)
    _ = (a⁻¹ • (A + (a * b) • A)).card := by rw [card_of_inv]; simp [h]
    _ = (a⁻¹ • A + a⁻¹ • (a * b) • A).card := by simp
    _ = (a⁻¹ • A + (a⁻¹ • (a * b)) • A).card := by rw [smul_assoc]
    _ = (a⁻¹ • A + b • A).card := by congr; field_simp; apply mul_comm
    _ = ((a⁻¹ • A + b • A).card * A.card) / A.card := by field_simp
    _ ≤ ((a⁻¹ • A + A).card * (A + b • A).card) / A.card := by
      gcongr ?X / _
      norm_cast
      apply card_add_mul_card_le_card_add_mul_card_add
    _ ≤ ((A + a⁻¹ • A).card * (A + b • A).card) / A.card := by rw [add_comm]
    _ ≤ ((K * A.card) * (K * A.card)) / A.card := by gcongr
    _ = K^2 * A.card := by field_simp; ring
  · simp_all [Stab]
    calc (A.card : ℚ)
      _ ≤ K * A.card := by assumption
      _ = (1*K) * A.card := by ring
      _ ≤ (K*K) * A.card := by gcongr;
      _ = K^2 * A.card := by ring
  · simp_all [Stab]
