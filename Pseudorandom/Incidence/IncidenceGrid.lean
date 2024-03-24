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
import Pseudorandom.Additive.Main
import Pseudorandom.Geometry.Lines
import Pseudorandom.Incidence.Constants
import Pseudorandom.Incidence.Claim342_grid

open Classical Real BigOps Finset Pointwise

variable {α : Type} [Field α] [Fintype α] {p : ℕ} [Fact p.Prime] [Fact (α = ZMod p)]

set_option maxHeartbeats 500000

theorem ST_grid_final (β : ℝ) (h : 0 < β) (A B : Finset α) (n : ℕ+) (nhₗ : (p^β : ℝ) ≤ n)
  (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
  (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
  (b₁ : α) (hb₁ : ¬b₁ ∈ B) (b₂ : α)
  (hb₂ : ¬b₂ ∈ B) (neq : b₁ ≠ b₂)
  (allInt : ∀ b ∈ B, (n ^ (1 - SG_eps₃ β) : ℝ) < ∑ v ∈ A ×ˢ A, if (b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2 ∈ A then 1 else 0):
  B.card < (((SG_C₄ - 4) / 16 - 2) * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β) : ℝ) := by
  -- have : Finset α := (2 • A)
  have nd0₃ : ¬(b₂ - b₁ = 0) := fun v => neq (eq_of_sub_eq_zero v).symm
  have ane : A.Nonempty := sorry
  have : ∀ b ∈ B, (4⁻¹ * (n^(2 - 2 * SG_eps₃ β - (1/2 + 2*ST_prime_field_eps₂ β)) : ℝ)) < additiveEnergy A (((b₂ - b) / (b -b₁)) • A) := by
    intro b hb
    have nd0 : ¬(b₂ - b = 0) := fun h => by
      sorry
    have nd0₂ : ¬(b - b₁ = 0) := fun h => by
      sorry
    have := allInt b hb
    -- simp at this
    calc (additiveEnergy A (((b₂ - b) / (b - b₁)) • A) : ℝ)
      _ = ((((A ×ˢ A) ×ˢ A ×ˢ A)).filter
          fun x : (α × α) × α × α => (b - b₁) / (b₂ - b₁) * x.1.1 + (b₂ - b) / (b₂ - b₁) * x.1.2 =
          (b - b₁) / (b₂ - b₁) * x.2.1 + (b₂ - b) / (b₂ - b₁) * x.2.2).card := by
        norm_cast
        rw [additive_mul_eq]
        congr
        ext x
        field_simp
        ring_nf
        apply div_ne_zero nd0 nd0₂
      _ = ∑ x ∈ (A ×ˢ A) ×ˢ A ×ˢ A, if (b - b₁) / (b₂ - b₁) * x.1.1 + (b₂ - b) / (b₂ - b₁) * x.1.2 = (b - b₁) / (b₂ - b₁) * x.2.1 + (b₂ - b) / (b₂ - b₁) * x.2.2 then 1 else 0 := by simp
      _ = ∑ x₁ ∈ A ×ˢ A, ∑ x₂ ∈ A ×ˢ A, if (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = (b - b₁) / (b₂ - b₁) * x₂.1 + (b₂ - b) / (b₂ - b₁) * x₂.2 then 1 else 0 := by rw [sum_product]
      _ = ∑ (a : α), ∑ x₁ ∈ ((A ×ˢ A).filter fun x₁ => (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = a),
          ∑ x₂ ∈ A ×ˢ A, if (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = (b - b₁) / (b₂ - b₁) * x₂.1 + (b₂ - b) / (b₂ - b₁) * x₂.2 then 1 else 0 := by
        rw [sum_fiberwise (s := A ×ˢ A) (g := fun x₁ => (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2)]
      _ = ∑ (a : α), ∑ x₁ ∈ ((A ×ˢ A).filter fun x₁ => (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = a),
          ∑ x₂ ∈ A ×ˢ A, if a = (b - b₁) / (b₂ - b₁) * x₂.1 + (b₂ - b) / (b₂ - b₁) * x₂.2 then 1 else 0 := by
        -- sorry
        congr
        ext a
        apply sum_congr
        rfl
        intro x₁ hx
        simp at hx
        rcongr
        exact hx.2
      _ = ∑ (a : α), ((A ×ˢ A).filter fun x₁ => (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = a).card *
          ((A ×ˢ A).filter fun x₁ => a = (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2).card := by simp only [sum_boole,
            sum_const, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul]
      _ = ∑ (a : α), (((A ×ˢ A).filter fun x₁ => (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = a).card^2 : ℝ) := by
        simp only [Nat.cast_sum, Nat.cast_mul, sq]
        rcongr
        exact eq_comm
      _ ≥ ∑ a ∈ A, (((A ×ˢ A).filter fun x₁ => (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = a).card^2 : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        simp
        intros
        simp
      _ ≥ (A.card : ℝ)⁻¹ * (∑ a ∈ A, ((A ×ˢ A).filter fun x₁ => (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = a).card)^2 := by
        simp only [Nat.cast_sum, ge_iff_le]
        rw [inv_mul_le_iff]
        apply sq_sum_le_card_mul_sum_sq
        norm_cast
        rw [card_pos]
        exact ane
      _ = (A.card : ℝ)⁻¹ * (∑ a ∈ A, ∑ x₁ ∈ (A ×ˢ A), if (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = a then 1 else 0)^2 := by simp
      _ = (A.card : ℝ)⁻¹ * (∑ x₁ ∈ (A ×ˢ A), ∑ a ∈ A, if (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 = a then 1 else 0)^2 := by rw [sum_comm]
      _ = (A.card : ℝ)⁻¹ * (∑ x₁ ∈ (A ×ˢ A), if (b - b₁) / (b₂ - b₁) * x₁.1 + (b₂ - b) / (b₂ - b₁) * x₁.2 ∈ A then 1 else 0)^2 := by simp
      _ = (A.card : ℝ)⁻¹ * (∑ x₁ ∈ A, ∑ x₂ ∈ A, if (b - b₁) / (b₂ - b₁) * x₁ + (b₂ - b) / (b₂ - b₁) * x₂ ∈ A then 1 else 0)^2 := by rw [sum_product' (f := fun x₁ x₂ => if (b - b₁) / (b₂ - b₁) * x₁ + (b₂ - b) / (b₂ - b₁) * x₂ ∈ A then 1 else 0)]
      _ = (A.card : ℝ)⁻¹ * (∑ x₁ ∈ (A ×ˢ A), if (b - b₁) / (b₂ - b₁) * x₁.2 + (b₂ - b) / (b₂ - b₁) * x₁.1 ∈ A then 1 else 0)^2 := by rw [sum_product_right' (f := fun x₁ x₂ => if (b - b₁) / (b₂ - b₁) * x₂ + (b₂ - b) / (b₂ - b₁) * x₁ ∈ A then 1 else 0)]
      _ = (A.card : ℝ)⁻¹ * (∑ x₁ ∈ (A ×ˢ A), if (b₂ - b) / (b₂ - b₁) * x₁.1 + (b - b₁) / (b₂ - b₁) * x₁.2 ∈ A then 1 else 0)^2 := by simp [add_comm]
      _ > (A.card : ℝ)⁻¹ * (n^(1 - SG_eps₃ β))^2 := by
        gcongr
      _ ≥ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)⁻¹ * (n^(1 - SG_eps₃ β))^2 := by
        gcongr
      _ = (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)⁻¹ * (n^(2 - 2 * SG_eps₃ β)) := by
        congr 1
        rw [←rpow_nat_cast, ←rpow_mul]
        ring_nf
        simp
      _ = 4⁻¹ * (n^(2 - 2 * SG_eps₃ β) / n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ) := by
        ring
      _ = 4⁻¹ * (n^(2 - 2 * SG_eps₃ β - (1/2 + 2*ST_prime_field_eps₂ β)) : ℝ) := by rw [←rpow_sub]; simp
  sorry

theorem ST_grid_aux₂ (β : ℝ) (h : 0 < β) (A B : Finset α) (L : Finset (Line α)) (n : ℕ+) (nhₗ : (p^β : ℝ) ≤ n)
  (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
  (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)) (h₂ : L.card ≤ n)
  (hC : ∀ l ∈ L, (n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card)
  (hHoriz : ∀ l ∈ L, ¬l.horiz)
  :
  (Intersections (A ×ˢ B) L).card ≤ (SG_C₃ * n ^ (3/2 - SG_eps β) : ℝ) := by
  by_contra! nh
  have ⟨b₁, hb₁, b₂, hb₂, ⟨neq, large'⟩⟩ := claim342_grid β h A B L n hA hB h₂ hHoriz nh
  let L' := L.filter (fun l => (∃ p ∈ A ×ˢ {b₁}, p ∈ l) ∧ ∃ p ∈ A ×ˢ {b₂}, p ∈ l)
  have large : L'.card > (SG_C₄ * n^(1 - SG_eps₂ β) : ℝ) := large'
  have : b₂ - b₁ ≠ 0 := fun v => neq (eq_of_sub_eq_zero v).symm
  let JSS := (B.filter
        (fun b => ∑ v ∈ (A ×ˢ A), (if (b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2 ∈ A then 1 else 0 : ℝ) ≤ n^(1 - SG_eps₃ β)))
  let JSS' := (B.filter
    (fun b => ¬∑ v ∈ (A ×ˢ A), (if (b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2 ∈ A then 1 else 0 : ℝ) ≤ n^(1 - SG_eps₃ β)))
  have := calc (SG_C₄ * n^(3/2 - SG_eps₂ β - SG_eps β) : ℝ)
    _ = (SG_C₄ * n^(1 - SG_eps₂ β)) * n ^ (1/2 - SG_eps β) := by
      rw [mul_assoc, ←rpow_add]
      ring_nf
      simp
    _ ≤ ∑ l ∈ L', (n ^ (1/2 - SG_eps β) : ℝ) := by simp; gcongr
    _ ≤ ∑ l ∈ L', (IntersectionsP (A ×ˢ B) l).card := by
      simp only [Nat.cast_sum]
      apply sum_le_sum
      intros
      apply le_of_lt
      apply hC
      simp_all only [mem_filter, L']
    _ = ∑ l ∈ L', ∑ p ∈ (A ×ˢ B), (if p ∈ l then 1 else 0) := by simp [IntersectionsP]
    _ = ∑ l ∈ L', ∑ b ∈ B, ∑ a ∈ A, (if (a, b) ∈ l then 1 else 0) := by simp [sum_product_right (s := A) (t := B)]
    _ = ∑ b ∈ B, ∑ l ∈ L', ∑ a ∈ A, (if (a, b) ∈ l then 1 else 0) := by rw [sum_comm]
    _ ≤ ∑ b ∈ B, ∑ l ∈ ((A ×ˢ A).image (fun v => (Line.of (v.1, b₁) (v.2, b₂) (fun eq => neq (congrArg Prod.snd eq))))), ∑ a ∈ A,
        (if (a, b) ∈ l then 1 else 0) := by
      apply sum_le_sum
      intro b hb
      apply sum_le_sum_of_subset_of_nonneg
      rw [subset_iff]
      intro l hl
      simp
      simp [L'] at hl
      have ⟨_, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hl
      exists a, b
      constructor
      exact ⟨ha.1, hb.1⟩
      apply Eq.symm
      apply line_eq_of
      exact ⟨ha.2, hb.2⟩
      intros
      simp
    _ = ∑ b ∈ B, ∑ v ∈ (A ×ˢ A), ∑ a ∈ A,
        (if (a, b) ∈ (Line.of (v.1, b₁) (v.2, b₂) (fun eq => neq (congrArg Prod.snd eq))) then 1 else 0) := by
      congr
      ext
      rw [sum_image]
      intros x hx y hy eq
      let l := Line.of (x.1, b₁) (x.2, b₂) (fun eq => neq (congrArg Prod.snd eq))
      have m1 : (x.1, b₁) ∈ l := by apply mem_line1
      have m2 : (x.2, b₂) ∈ l := by apply mem_line2
      change l = Line.of (y.1, b₁) (y.2, b₂) (fun eq => neq (congrArg Prod.snd eq)) at eq
      have m3 : (y.1, b₁) ∈ l := by rw [eq]; apply mem_line1
      have m4 : (y.2, b₂) ∈ l := by rw [eq]; apply mem_line2
      have nHoriz : ¬l.horiz := by rw [Line.of_horiz_iff]; simp [neq]
      have e1 : x.1 = y.1 := by
        by_contra! nh
        have :=
          line_eq_of (x.1, b₁) (y.1, b₁) (by aesop) l ⟨m1, m3⟩
        simp [this, Line.of_horiz_iff] at nHoriz
      have e2 : x.2 = y.2 := by
        by_contra! nh
        have : l = Line.of (x.2, b₂) (y.2, b₂) (fun eq => nh (congrArg Prod.fst eq)) := by
          apply line_eq_of
          exact ⟨m2, m4⟩
        simp [this, Line.of_horiz_iff] at nHoriz
      rw [Prod.eq_iff_fst_eq_snd_eq]
      exact ⟨e1, e2⟩
    _ = ∑ b ∈ B, ∑ v ∈ (A ×ˢ A), ∑ a ∈ A,
        (if a = (b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2 then 1 else 0) := by
      rcongr b x a
      change (a, b, (1 : α)) ∈ (Submodule.span α (M := α × α × α) {(x.1, b₁, 1), (x.2, b₂, 1)} : Set _) ↔
          a = (b₂ - b) / (b₂ - b₁) * x.1 + (b - b₁) / (b₂ - b₁) * x.2
      simp only [SetLike.mem_coe]
      rw [Submodule.mem_span_pair]
      constructor
      · intro v
        have ⟨c1, c2, eq⟩ := v
        simp at eq
        have : c1 = 1 - c2 := by linear_combination eq.2.2
        simp [this] at eq
        have : c2 * (b₂ - b₁) = b - b₁ := by linear_combination eq.2
        have : c2 = (b - b₁) / (b₂ - b₁) := by
          rw [eq_div_iff]
          exact this
          assumption
        simp [this] at eq
        have eq := eq.1.symm
        rw [one_sub_div] at eq
        rw [eq]
        congr 3
        ring
        assumption
      · intro v
        exists (b₂ - b) / (b₂ - b₁), (b - b₁) / (b₂ - b₁)
        simp
        constructor
        exact v.symm
        constructor
        field_simp
        ring
        field_simp
    _ = ∑ b ∈ B, ∑ v ∈ (A ×ˢ A), (if (b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2 ∈ A then 1 else 0) := by
      rcongr b v
      split
      rw [sum_eq_single_of_mem ((b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2)]
      simp
      assumption
      intros
      simp
      assumption
      apply sum_eq_zero
      intros
      aesop
    _ = ∑ b ∈ JSS,
        ∑ v ∈ (A ×ˢ A), (if (b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2 ∈ A then 1 else 0) +
        ∑ b ∈ JSS',
        ∑ v ∈ (A ×ˢ A), (if (b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2 ∈ A then 1 else 0) := by
      rw [sum_filter_add_sum_filter_not]
    _ ≤ ∑ b ∈ JSS, (n^(1 - SG_eps₃ β) : ℝ) +
        ∑ b ∈ JSS', ∑ v ∈ (A ×ˢ A), 1 := by
      gcongr
      simp_all only [JSS, mem_filter]
      split <;> simp only [le_refl, zero_le_one]
    _ = JSS.card * (n^(1 - SG_eps₃ β) : ℝ) +
        JSS'.card * (A.card * A.card) := by simp only [sum_const, nsmul_eq_mul, card_product,
          Nat.cast_mul, mul_one]
    _ ≤ B.card * (n^(1 - SG_eps₃ β) : ℝ) +
        JSS'.card * (A.card * A.card) := by gcongr; simp only [filter_subset, JSS]
    _ ≤ 4*n^(1/2 + 2*ST_prime_field_eps₂ β) * n^(1 - SG_eps₃ β) +
        JSS'.card * ((4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) * (4 * n^(1/2 + 2*ST_prime_field_eps₂ β))) := by
      gcongr
    _ = 4 * (n^(1/2 + 2*ST_prime_field_eps₂ β) * n^(1 - SG_eps₃ β)) +
        16 * JSS'.card * (n^(1/2 + 2*ST_prime_field_eps₂ β) * n^(1/2 + 2*ST_prime_field_eps₂ β)) := by ring
    _ = 4 * (n^(1/2 + 2*ST_prime_field_eps₂ β + (1 - SG_eps₃ β))) +
        16 * JSS'.card * n^(1/2 + 2*ST_prime_field_eps₂ β + (1/2 + 2*ST_prime_field_eps₂ β)) := by
      simp [←rpow_add]
    _ = 4 * (n^(3/2 + 2*ST_prime_field_eps₂ β - SG_eps₃ β)) +
        16 * JSS'.card * n^(1 + 4*ST_prime_field_eps₂ β) := by ring_nf
  have eq : 3/2 + 2*ST_prime_field_eps₂ β - SG_eps₃ β = 3/2 - SG_eps₂ β - SG_eps β := by
    simp [ST_prime_field_eps₂, ST_prime_field_eps₃, ST_prime_field_eps₄, SG_eps, SG_eps₂]
    ring
  rw [eq] at this
  let JSS'' := JSS' \ {b₁, b₂}
  have := calc (((SG_C₄ - 4) / 16 - 2) * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β) : ℝ)
    _ = (SG_C₄ - 4) / 16 * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β) - 2 *
        n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β) := by ring
    _ ≤ (SG_C₄ - 4) / 16 * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β) - 2 * 1 := by
      gcongr
      apply one_le_rpow
      norm_cast
      simp
      apply lemma8
      assumption
    _ = ((SG_C₄ - 4) * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β)) / 16 - 2 := by field_simp
    _ = ((SG_C₄ - 4) * (n^(3/2 - SG_eps₂ β - SG_eps β) / n ^ (1 + 4 * ST_prime_field_eps₂ β))) / 16 - 2 := by
      congr
      rw [←rpow_sub]
      ring_nf
      simp
    _ = (SG_C₄ * n^(3/2 - SG_eps₂ β - SG_eps β) - 4 * n^(3/2 - SG_eps₂ β - SG_eps β)) / (16 * n^(1 + 4 * ST_prime_field_eps₂ β)) - 2 := by
      field_simp
      ring_nf
    _ ≤ ((4 * n^(3/2 - SG_eps₂ β - SG_eps β) + 16 * JSS'.card * n^(1 + 4 * ST_prime_field_eps₂ β)) -
        4 * n^(3/2 - SG_eps₂ β - SG_eps β)) / (16 * n^(1 + 4 * ST_prime_field_eps₂ β)) - 2 := by
      gcongr
    _ = JSS'.card * ((16 * n^(1 + 4 * ST_prime_field_eps₂ β)) / (16 * n^(1 + 4 * ST_prime_field_eps₂ β))) - 2 := by
      ring_nf
    _ = JSS'.card - 2 := by
      rw [div_self]
      rw [mul_one]
      apply ne_of_gt
      apply mul_pos
      norm_num
      apply rpow_pos_of_pos
      simp
    _ = JSS'.card - ({b₁, b₂} : Finset _).card := by congr; simp only [mem_singleton, neq,
      not_false_eq_true, card_insert_of_not_mem, card_singleton, Nat.reduceAdd, Nat.cast_ofNat]
    _ ≤ JSS''.card := by rw [sub_le_iff_le_add]; norm_cast; apply card_le_card_sdiff_add_card
  suffices JSS''.card < (((SG_C₄ - 4) / 16 - 2) * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β) : ℝ) by
    linarith
  apply ST_grid_final β h A JSS'' n nhₗ nhᵤ hA _ b₁ _ b₂ _ _
  intros b hb
  simp only [filter_congr_decidable, not_le, mem_sdiff, mem_filter, mem_insert,
    mem_singleton, JSS'', JSS'] at hb
  exact hb.1.2
  calc
    (JSS''.card : ℝ) ≤ JSS'.card := by gcongr; simp only [sdiff_subset, JSS'']
    _ ≤ B.card := by gcongr; simp only [filter_subset, JSS']
    _ ≤ _ := by assumption
  simp only [mem_sdiff, mem_insert, mem_singleton, true_or, not_true_eq_false, and_false,
    not_false_eq_true, JSS'']
  simp only [mem_sdiff, mem_insert, mem_singleton, or_true, not_true_eq_false, and_false,
    not_false_eq_true, JSS'']
  exact neq







theorem ST_grid_aux (β : ℝ) (h : 0 < β) (A B : Finset α) (L : Finset (Line α)) (n : ℕ+) (nhₗ : (p^β : ℝ) ≤ n)
  (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
  (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)) (h₂ : L.card ≤ n)
  (hC : ∀ l ∈ L, (n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card)
  :
  (Intersections (A ×ˢ B) L).card ≤ (SG_C₂ * n ^ (3/2 - SG_eps β) : ℝ) := by
  calc ((Intersections (A ×ˢ B) L).card : ℝ)
    _ = ∑ l ∈ L, (IntersectionsP (A ×ˢ B) l).card := by norm_cast; apply IntersectionsP_sum
    _ = ∑ l ∈ L.filter (fun l => l.horiz), (IntersectionsP (A ×ˢ B) l).card +
        ∑ l ∈ L.filter (fun l => ¬l.horiz), (IntersectionsP (A ×ˢ B) l).card := by
      norm_cast
      rw [sum_filter_add_sum_filter_not]
    _ = ∑ l ∈ L.filter (fun l => l.horiz), ∑ p ∈ IntersectionsP (A ×ˢ B) l, 1 +
      ∑ l ∈ L.filter (fun l => ¬l.horiz), (IntersectionsP (A ×ˢ B) l).card := by
      simp
    _ = ∑ __ ∈ (Finset.biUnion (L.filter (fun l => l.horiz)) (fun l => IntersectionsP (A ×ˢ B) l)), 1 +
      ∑ l ∈ L.filter (fun l => ¬l.horiz), (IntersectionsP (A ×ˢ B) l).card := by
      rw [sum_biUnion]
      intro p₁ hp₁ p₂ hp₂ neq
      intro s h₁ h₂
      simp_all
      simp only [Line.horiz] at hp₁
      simp only [Line.horiz] at hp₂
      rw [subset_iff]
      intro x hx
      simp
      suffices 1 < (univ.filter (fun (x : α × α) => x ∈ p₁ ∧ x ∈ p₂)).card by
        have this₂ := line_intersect p₁ p₂ neq
        linarith
      rw [one_lt_card]
      have h₁ := subset_iff.mp h₁ hx
      have h₂ := subset_iff.mp h₂ hx
      have h₁ := (mem_filter.mp h₁).2
      have h₂ := (mem_filter.mp h₂).2
      have h₁' := Submodule.add_mem p₁.val h₁ hp₁.2
      have h₂' := Submodule.add_mem p₂.val h₂ hp₂.2
      simp_all only [SetLike.mem_coe, Prod.mk_add_mk, add_zero, mem_filter, mem_univ, true_and,
        ne_eq, not_and]
      change (x.1+1, x.2) ∈ p₁ at h₁'
      change (x.1+1, x.2) ∈ p₂ at h₂'
      exists x
      constructor
      exact ⟨h₁, h₂⟩
      exists (x.1 + 1, x.2)
      constructor
      exact ⟨h₁', h₂'⟩
      aesop
    _ ≤ ∑ __ ∈ (A ×ˢ B), 1 +
      (Intersections (A ×ˢ B) (L.filter (fun l => ¬l.horiz))).card := by
      simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_sum, Nat.cast_mul]
      gcongr
      simp
      intros
      apply filter_subset
      apply le_of_eq
      simp [IntersectionsP_sum]
    _ ≤ A.card * B.card + SG_C₃ * n ^ (3/2 - SG_eps β) := by
      gcongr
      simp
      apply ST_grid_aux₂ <;> try assumption
      calc
        (L.filter (fun l => ¬l.horiz)).card ≤ L.card := by gcongr; simp
        _ ≤ n := by assumption
      intros
      apply hC
      simp_all
      intros
      simp_all
    _ ≤ (4 * n^(1/2 + 2 * ST_prime_field_eps₂ β))^2 + SG_C₃ * n ^ (3/2 - SG_eps β) := by
      simp only [sq]
      gcongr
    _ = 16 * n^(1 + 4 * ST_prime_field_eps₂ β) + SG_C₃ * n ^ (3/2 - SG_eps β) := by
      congr
      simp [mul_pow]
      congr 1
      norm_num
      rw [←rpow_nat_cast, ←rpow_mul]
      congr 1
      ring
      simp
    _ ≤ 16 * n^(3/2 - SG_eps β) + SG_C₃ * n ^ (3/2 - SG_eps β) := by
      gcongr
      norm_cast
      simp
      apply lemma6
      assumption
    _ = SG_C₂ * n ^ (3/2 - SG_eps β) := by simp [SG_C₂]; ring_nf

theorem ST_grid (β : ℝ) (h : 0 < β) (A B : Finset α) (L : Finset (Line α)) (n : ℕ+) (nhₗ : (p^β : ℝ) ≤ n)
  (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
  (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)) (h₂ : L.card ≤ n) :
  (Intersections (A ×ˢ B) L).card ≤ (SG_C * n ^ (3/2 - SG_eps β) : ℝ) := by
  calc ((Intersections (A ×ˢ B) L).card : ℝ)
    _ = ∑ l ∈ L, (IntersectionsP (A ×ˢ B) l).card := by norm_cast; apply IntersectionsP_sum
    _ = ∑ l ∈ L.filter (fun l => (n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card), (IntersectionsP (A ×ˢ B) l).card +
        ∑ l ∈ L.filter (fun l => ¬(n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card), (IntersectionsP (A ×ˢ B) l).card := by
      norm_cast
      rw [sum_filter_add_sum_filter_not]
    _ ≤ (Intersections (A ×ˢ B) (L.filter (fun l => (n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card))).card +
        ∑ __ ∈ L.filter (fun l => ¬(n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card), (n ^ (1/2 - SG_eps β) : ℝ) := by
      gcongr
      rw [IntersectionsP_sum]
      simp only [one_div, not_lt, Nat.cast_sum]
      apply sum_le_sum
      intros
      simp_all
    _ ≤ SG_C₂ * n^(3/2 - SG_eps β) + n * n^(1/2 - SG_eps β) := by
      gcongr
      apply ST_grid_aux <;> try assumption
      calc (L.filter (fun l => (n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card)).card
        _ ≤ L.card := by gcongr; simp
        _ ≤ n := by assumption
      intros
      simp_all
      simp
      gcongr
      calc (L.filter (fun l => (IntersectionsP (A ×ˢ B) l).card ≤ (n ^ (2⁻¹ - SG_eps β) : ℝ))).card
        _ ≤ L.card := by gcongr; simp
        _ ≤ n := by assumption
    _ = SG_C * n ^ (3/2 - SG_eps β) := by
      simp [SG_C]
      rw [←rpow_one_add']
      ring_nf
      simp
      apply lemma5
      assumption
