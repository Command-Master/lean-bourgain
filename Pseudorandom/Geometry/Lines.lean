import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.SetLike.Fintype
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

variable {α : Type*} [Field α] [Fintype α] [DecidableEq α]

open BigOperators Finset

def Line (α : Type*) [Ring α] := {x : Submodule α (α × α × α) // FiniteDimensional.finrank α x = 2}

instance instSetLike : SetLike (Line α) (α × α × α) where
  coe x := x.val
  coe_injective' x1 x2 h := by
    apply Subtype.ext
    simp_all

theorem set_like_val {x : α × α × α} {l : Line α} : x ∈ l ↔ x ∈ l.val := by aesop

@[simp]
lemma Line_finrank {l : Line α} : FiniteDimensional.finrank α l.val = 2 := by
  cases l
  simp_all

instance mem2 : Membership (α × α) (Line α) where
  mem x l := ⟨x.1, x.2, 1⟩ ∈ l


noncomputable instance instDecidableMem2 (x : α × α) (y : Line α) : Decidable (x ∈ y) := by
  classical apply inferInstance

noncomputable instance instDecidableEqLine : DecidableEq (Line α) := by
  classical apply inferInstance

def Line.apply (l : Line α) (p : (α × α × α) ≃ₗ[α] (α × α × α)) : Line α := ⟨Submodule.map (p : (α × α × α) →ₗ[α] (α × α × α)) l.val, by
  rw [LinearEquiv.finrank_map_eq]
  simp⟩

def apply_injective (l₁ l₂ : Line α) (p : (α × α × α) ≃ₗ[α] (α × α × α)) (h : l₁.apply p = l₂.apply p) : l₁ = l₂ := by
  simp [Line.apply] at h
  apply congrArg (fun x => x.val) at h
  simp at h
  apply Submodule.map_injective_of_injective at h
  apply Subtype.ext
  exact h
  simp
  apply LinearEquiv.injective

instance mem3 : Membership (α × α) (Submodule α (α × α × α)) where
  mem x l := ⟨x.1, x.2, 1⟩ ∈ l

lemma mem_iff_mem_val (x : α × α) (l : Line α) : x ∈ l ↔ x ∈ l.val := by aesop

def Submodule.pair (i j : α × α) := Submodule.span α (M := α × α × α) {⟨i.1, i.2, 1⟩, ⟨j.1, j.2, 1⟩}

lemma mem_span1 (i j : α × α) : i ∈ Submodule.pair i j := Submodule.subset_span <| (by simp)

lemma mem_span2 (i j : α × α) : j ∈ Submodule.pair i j := Submodule.subset_span <| (by simp)

noncomputable def Submodule.pair_basis (i j : α × α) (h : i ≠ j) : Basis (Fin 2) α (Submodule.pair i j) := by
  have := Basis.span
    (R := α)
    (M := α × α × α)
    (v := ![⟨i.1,i.2,1⟩, ⟨j.1,j.2,1⟩]) (by
      rw [linearIndependent_fin2]
      aesop
    )
  apply this.map (LinearEquiv.ofEq ..)
  simp [pair]
  congr 1
  aesop

lemma repr_pair_basis_first' (i j : α × α) (h : i ≠ j) : (Submodule.pair_basis i j h) 0 = ⟨⟨i.1,i.2,1⟩, mem_span1 i j⟩ := by
  simp [Submodule.pair_basis]
  apply Subtype.ext
  simp
  rw [Basis.span_apply]
  rfl

lemma repr_pair_basis_first (i j : α × α) (h : i ≠ j) : (Submodule.pair_basis i j h).repr ⟨⟨i.1,i.2,1⟩, mem_span1 i j⟩ = Finsupp.single 0 1 := by
  rw [←repr_pair_basis_first' i j h]
  rw [Basis.repr_self]

lemma repr_pair_basis_second' (i j : α × α) (h : i ≠ j) : (Submodule.pair_basis i j h) 1 = ⟨⟨j.1,j.2,1⟩, mem_span2 i j⟩ := by
  simp [Submodule.pair_basis]
  apply Subtype.ext
  simp
  rw [Basis.span_apply]
  rfl

lemma repr_pair_basis_second (i j : α × α) (h : i ≠ j) : (Submodule.pair_basis i j h).repr ⟨⟨j.1,j.2,1⟩, mem_span2 i j⟩ = Finsupp.single 1 1 := by
  rw [←repr_pair_basis_second' i j h]
  rw [Basis.repr_self]

def Line.of (i j : α × α) (h : i ≠ j) : Line α := ⟨Submodule.pair i j, by
    rw [finrank_eq_nat_card_basis <| Submodule.pair_basis i j h]
    simp
  ⟩

def Submodule.infinity (α : Type*) [Field α] := Submodule.span α (M := α × α × α) {⟨1, 0, 0⟩, ⟨0, 1, 0⟩}

noncomputable def Submodule.infinity_basis (α : Type*) [Field α] : Basis (Fin 2) α (Submodule.infinity α) := by
  have := Basis.span
    (R := α)
    (M := α × α × α)
    (v := ![⟨1,0,0⟩, ⟨0,1,0⟩]) (by
      rw [linearIndependent_fin2]
      aesop
    )
  apply this.map (LinearEquiv.ofEq ..)
  simp [infinity]
  congr 1
  aesop

lemma infinity_mem (x : α × α × α) : x ∈ (Submodule.infinity α : Set _) ↔ x.2.2 = 0 := by
  constructor
  intro v
  rw [Submodule.infinity] at v
  simp only [SetLike.mem_coe, Submodule.mem_span_pair] at v
  have ⟨a, b, s⟩ := v
  rw [←s]
  simp
  intro v
  rw [Submodule.infinity]
  simp only [SetLike.mem_coe, Submodule.mem_span_pair]
  exists x.1, x.2.1
  simp
  aesop

lemma infinity_mem_first : ((1, 0, 0) : α × α × α) ∈ (Submodule.infinity α : Set _) := by
  rw [infinity_mem]

lemma infinity_first : Submodule.infinity_basis α 0 = ⟨⟨1, 0, 0⟩, infinity_mem_first⟩ := by
  simp [Submodule.infinity_basis]
  apply Subtype.ext
  simp
  rw [Basis.span_apply]
  rfl

lemma infinity_mem_second : ((0, 1, 0) : α × α × α) ∈ (Submodule.infinity α : Set _) := by
  rw [infinity_mem]

lemma infinity_second : Submodule.infinity_basis α 1 = ⟨⟨0, 1, 0⟩, infinity_mem_second⟩ := by
  simp [Submodule.infinity_basis]
  apply Subtype.ext
  simp
  rw [Basis.span_apply]
  rfl

def Line.infinity (α) [Field α] : Line α := ⟨Submodule.infinity α, by
    rw [finrank_eq_nat_card_basis <| Submodule.infinity_basis α]
    simp
  ⟩

def Vnorm (x : α × α × α) := (x.1 / x.2.2, x.2.1 / x.2.2)

lemma norm_mem (l : Line α) (x : α × α × α) (h₂ : x.2.2 ≠ 0) : x ∈ (l : Set _) ↔ Vnorm x ∈ l := by
  simp [Vnorm, mem2]
  have : 1 = x.2.2 / x.2.2 := by simp [h₂]
  rw [this]
  have : (x.1 / x.2.2, x.2.1 / x.2.2, x.2.2 / x.2.2) = (1 / x.2.2) • x := by
    cases x
    rename_i x1 x2
    cases x2
    rename_i x21 x22
    simp
    constructor
    apply div_eq_inv_mul
    constructor
    apply div_eq_inv_mul
    apply div_eq_inv_mul
  rw [this]
  apply Iff.symm
  apply Submodule.smul_mem_iff
  simp_all

lemma vnorm_eq_vnorm (x y : α × α × α) (h : Vnorm x = Vnorm y) (h₂ : x.2.2 ≠ 0) (h₃ : y.2.2 ≠ 0) : ∃ r : α, r • x = y := by
  exists y.2.2/x.2.2
  simp [Vnorm] at h
  field_simp at *
  ext
  repeat field_simp [h.1, h.2, mul_comm]


lemma mem_line1 (i j : α × α) (h : i ≠ j) : i ∈ (Line.of i j h) := by
  have : ({⟨i.1, i.2, 1⟩, ⟨j.1, j.2, 1⟩} : Set (α × α × α)) ⊆ (Line.of i j h).val := by
    simp [Line.of, Submodule.pair]
    apply Submodule.subset_span
  aesop

lemma mem_line2 (i j : α × α) (h : i ≠ j) : j ∈ (Line.of i j h) := by
  have : ({⟨i.1, i.2, 1⟩, ⟨j.1, j.2, 1⟩} : Set (α × α × α)) ⊆ (Line.of i j h).val := by
    simp [Line.of, Submodule.pair]
    apply Submodule.subset_span
  aesop

theorem line_eq_of (i j : α × α) (oh : i ≠ j) (l₂ : Line α)
  (h : i ∈ l₂ ∧ j ∈ l₂) : l₂ = Line.of i j oh := by
  have : (Line.of i j oh).val ≤ l₂.val := by
    simp [Line.of, Submodule.pair, Submodule.span_le, Set.subset_def]
    constructor <;> aesop
  apply Eq.symm
  apply Subtype.ext
  apply FiniteDimensional.eq_of_le_of_finrank_eq
  assumption
  simp

def Line.horiz (l : Line α) : Prop := ((1, 0, 0) : α × α × α) ∈ (l : Set _)

theorem Line.of_horiz_iff (x y : α × α) (h : x ≠ y) : (Line.of x y h).horiz ↔ x.2 = y.2 := by
  constructor
  intro v
  simp [horiz, of] at v
  apply Submodule.mem_span_pair.mp at v
  have ⟨a, b, v⟩ := v
  simp at v
  have ⟨__, v2, v3⟩ := v
  have : a = -b := by linear_combination v3
  simp [this] at v2
  have : b * (y.2 - x.2) = 0 := by linear_combination v2
  simp at this
  cases this
  simp_all
  rename_i h
  linear_combination -h
  intro v
  simp [horiz, of]
  apply Submodule.mem_span_pair.mpr
  exists (x.1-y.1)⁻¹, -(x.1-y.1)⁻¹
  simp_all
  ring_nf
  suffices (x.1 - y.1) * (x.1 - y.1)⁻¹ = 1 by ring_nf at this; exact this
  apply mul_inv_cancel
  intro v2
  suffices x = y by contradiction
  apply eq_of_sub_eq_zero at v2
  aesop

theorem Line.horiz_constant (l : Line α) (x y : α × α) (h : x ∈ l) (h₂ : y ∈ l) (hor : l.horiz) : x.2 = y.2 := by
  by_cases x = y
  simp_all
  rename_i neq
  apply (Line.of_horiz_iff x y neq).mp
  rw [←line_eq_of x y neq l]
  assumption
  constructor <;> assumption


def Line.vert (l : Line α) : Prop := ((0, 1, 0) : α × α × α) ∈ (l : Set _)

theorem Line.of_vert_iff (x y : α × α) (h : x ≠ y) : (Line.of x y h).vert ↔ x.1 = y.1 := by
  constructor
  intro v
  simp [vert, of] at v
  apply Submodule.mem_span_pair.mp at v
  have ⟨a, b, v⟩ := v
  simp at v
  have ⟨v1, __, v3⟩ := v
  have : a = -b := by linear_combination v3
  simp [this] at v1
  have : b * (y.1 - x.1) = 0 := by linear_combination v1
  simp at this
  cases this
  simp_all
  rename_i h
  linear_combination -h
  intro v
  simp [horiz, of]
  apply Submodule.mem_span_pair.mpr
  exists (x.2-y.2)⁻¹, -(x.2-y.2)⁻¹
  simp_all
  ring_nf
  suffices (x.2 - y.2) * (x.2 - y.2)⁻¹ = 1 by ring_nf at this; exact this
  apply mul_inv_cancel
  intro v2
  suffices x = y by contradiction
  apply eq_of_sub_eq_zero at v2
  aesop

theorem Line.vert_constant (l : Line α) (x y : α × α) (h : x ∈ l) (h₂ : y ∈ l) (hor : l.vert) : x.1 = y.1 := by
  by_cases x = y
  simp_all
  rename_i neq
  apply (Line.of_vert_iff x y neq).mp
  rw [←line_eq_of x y neq l]
  assumption
  constructor <;> assumption

theorem point_intersect (i j : α × α) (oh : i ≠ j) :
  (univ.filter (fun (x : Line α) => i ∈ x ∧ j ∈ x)).card = 1 := by
  rw [card_eq_one]
  exists Line.of i j oh
  rw [eq_singleton_iff_unique_mem]
  constructor
  simp
  constructor
  apply mem_line1
  apply mem_line2
  intro l₂ h
  simp at h
  apply line_eq_of
  exact h

theorem line_intersect (i j : Line α) (h : i ≠ j) :
  (univ.filter (fun (x : α × α) => x ∈ i ∧ x ∈ j)).card ≤ 1 := by
  by_contra! nh
  rw [Finset.one_lt_card] at nh
  have ⟨a, ha, b, hb, neq⟩ := nh
  simp_all
  let S := (univ.filter (fun (x : Line α) => a ∈ x ∧ b ∈ x))
  have : S.card = 1 := point_intersect a b neq
  have m1 : i ∈ S := by simp_all [S]
  have m2 : j ∈ S := by simp_all [S]
  have := one_lt_card.mpr ⟨i, m1, j, m2, h⟩
  linarith

noncomputable def Intersections (P : Finset (α × α)) (L : Finset (Line α)) :=
  (P ×ˢ L).filter (fun x => x.1 ∈ x.2)

noncomputable def IntersectionsP (P : Finset (α × α)) (L : Line α) :=
  P.filter (fun x => x ∈ L)

noncomputable def IntersectionsL (P : α × α) (L : Finset (Line α)) :=
  L.filter (fun x => P ∈ x)

lemma IntP_subset_of_subset {P₁ P₂ : Finset (α × α)} {l : Line α} (h : P₁ ⊆ P₂) : IntersectionsP P₁ l ⊆ IntersectionsP P₂ l := by
  apply filter_subset_filter
  assumption

@[simp]
lemma Int_empty {L : Finset (Line α)} :
  Intersections ∅ L = ∅ := by
  simp [Intersections]

@[simp]
lemma Int2_empty {P : Finset (α × α)} :
  Intersections P ∅ = ∅ := by
  simp [Intersections]

lemma IntersectionsP_sum (P : Finset (α × α)) (L : Finset (Line α)) :
  (Intersections P L).card = ∑ y in L, (IntersectionsP P y).card := by
  calc
    (Intersections P L).card = ((P ×ˢ L).filter (fun x => x.1 ∈ x.2)).card := rfl
    _ = ∑ x in (P ×ˢ L).filter (fun x => x.1 ∈ x.2), 1 := by simp
    _ = ∑ x in (P ×ˢ L), if x.1 ∈ x.2 then 1 else 0 := by rw [sum_filter]
    _ = ∑ y in L, ∑ x in P, if x ∈ y then 1 else 0 := by rw [sum_product_right]
    _ = ∑ y in L, (P.filter (fun x => x ∈ y)).card := by simp
    _ = ∑ y in L, (IntersectionsP P y).card := rfl

lemma IntersectionsL_sum (P : Finset (α × α)) (L : Finset (Line α)) :
  (Intersections P L).card = ∑ y in P, (IntersectionsL y L).card := by
  calc
    (Intersections P L).card = ((P ×ˢ L).filter (fun x => x.1 ∈ x.2)).card := rfl
    _ = ∑ x in (P ×ˢ L).filter (fun x => x.1 ∈ x.2), 1 := by simp
    _ = ∑ x in (P ×ˢ L), if x.1 ∈ x.2 then 1 else 0 := by rw [sum_filter]
    _ = ∑ x in P, ∑ y in L, if x ∈ y then 1 else 0 := by rw [sum_product]
    _ = ∑ x in P, (L.filter (fun y => x ∈ y)).card := by simp
    _ = ∑ y in P, (IntersectionsL y L).card := rfl

lemma lin_ST (P : Finset (α × α)) (L : Finset (Line α)):
  (Intersections P L).card ≤ P.card * L.card := by
  calc
    (Intersections P L).card ≤ (P ×ˢ L).card := Finset.card_filter_le _ _
    _ = P.card * L.card := by simp

lemma CS_UB (P : Finset <| α × α) (L : Finset <| Line α):
  (Intersections P L).card^2 ≤ L.card * P.card * (L.card + P.card) := by
  calc
    (Intersections P L).card^2 = (∑ x in P, (IntersectionsL x L).card)^2 := by rw [IntersectionsL_sum]
    _ ≤ P.card * ∑ x in P, (IntersectionsL x L).card^2 := by
      rw [←Nat.cast_le (α := ℝ)]
      simp
      apply sq_sum_le_card_mul_sum_sq
    _ = P.card * ∑ x in P, ∑ y in L, ∑ z in L, (if x ∈ y then 1 else 0) * (if x ∈ z then 1 else 0) := by
      congr
      ext x
      rw [←mul_one (a := (IntersectionsL x L).card), ←smul_eq_mul, ←sum_const, IntersectionsL, sum_filter, sq, sum_mul_sum]
    _ = P.card * ∑ y in L, ∑ z in L, ∑ x in P, (if x ∈ y then 1 else 0) * (if x ∈ z then 1 else 0) := by
      rw [sum_comm]
      congr; ext
      rw [sum_comm]
    _ ≤ P.card * ∑ y in L, (∑ x in P, (if x ∈ y then 1 else 0) + ∑ z in L, 1) := by
      apply mul_le_mul_of_nonneg_left
      apply sum_le_sum
      intro i h
      rw [sum_eq_add_sum_diff_singleton (i := i)]
      apply add_le_add
      apply le_of_eq
      apply sum_congr <;> aesop
      rw [sum_eq_add_sum_diff_singleton (s := L) (i := i)]
      apply le_add_left
      apply sum_le_sum
      intro j h₂
      have neq : i ≠ j := by aesop
      calc ∑ x in P, (if x ∈ i then 1 else 0) * (if x ∈ j then 1 else 0)
        _ = ∑ x in P, if x ∈ i ∧ x ∈ j then 1 else 0 := by apply sum_congr; rfl; aesop
        _ = (P.filter (fun x => x ∈ i ∧ x ∈ j)).card := by simp
        _ ≤ (univ.filter (fun (x : α × α) => x ∈ i ∧ x ∈ j)).card := by
          apply card_le_card
          apply filter_subset_filter
          apply subset_univ
        _ ≤ 1 := line_intersect i j neq
      exact h
      exact h
      simp
    _ = P.card * (∑ y in L, ∑ x in P, if x ∈ y then 1 else 0) + P.card * L.card * L.card := by simp [sum_add_distrib]; ring
    _ = P.card * (∑ x in (P ×ˢ L), if x.1 ∈ x.2 then 1 else 0) + P.card * L.card * L.card := by rw [sum_product_right]
    _ = P.card * (∑ x in (P ×ˢ L).filter (fun x => x.1 ∈ x.2), 1) + P.card * L.card * L.card := by rw [sum_filter]
    _ = P.card * ((P ×ˢ L).filter (fun x => x.1 ∈ x.2)).card + P.card * L.card * L.card := by simp
    _ = P.card * (Intersections P L).card + P.card * L.card * L.card := rfl
    _ ≤ P.card * (P.card * L.card) + P.card * L.card * L.card := by gcongr; apply lin_ST
    _ = L.card * P.card * (L.card + P.card) := by ring
