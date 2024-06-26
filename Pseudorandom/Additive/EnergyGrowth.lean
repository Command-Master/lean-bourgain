import Pseudorandom.Additive.Stab
import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Extras.BSG

open Finset Pointwise

variable (K : ℝ) (hK : 1 ≤ K) (p : ℕ) [inst : Fact (p.Prime)] (A : Finset (ZMod p)) (T : Finset (ZMod p)) (h' : 0 ∉ T)

section general


open BigOperators

variable {α β : Type*} [DecidableEq α]

lemma claim336 (K : Finset β) (hK : K.Nonempty) (f : β → Finset α) (S : Finset α) (hS : S.Nonempty) (δ : ℝ) (hδ : 0 ≤ δ)
  (h : ∀ v ∈ K, (f v) ⊆ S ∧ δ * S.card ≤ (f v).card) :
  ∃ i ∈ K, δ^2/2 * K.card ≤ (K.filter (fun x => δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)).card := by
  have : S.card ≠ 0 := by positivity
  suffices ∃ i ∈ K, δ^2 * K.card * S.card ≤ ∑ j ∈ K, ((f j) ∩ (f i)).card by
    have ⟨i, hi, h'⟩ := this
    exists i, hi
    by_contra! nh
    absurd h'
    simp only [Nat.cast_sum, not_le]
    calc (∑ j ∈ K, ((f j) ∩ (f i)).card : ℝ)
      _ = ∑ j ∈ (K.filter (fun x => δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)), ((f j) ∩ (f i)).card +
          ∑ j ∈ (K.filter (fun x => ¬δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)), ((f j) ∩ (f i)).card := by
        simp only [Nat.cast_sum, sum_filter_add_sum_filter_not]
      _ ≤ ∑ __ ∈ (K.filter (fun x => δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)), S.card +
          ∑ j ∈ (K.filter (fun x => ¬δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)), δ^2/2 * S.card := by
        push_cast
        gcongr
        have := (h i hi).1
        rw [subset_iff] at this
        rw [subset_iff]
        intro x hx
        rw [mem_inter] at hx
        exact this hx.2
        simp_all [le_of_lt]
      _ = (K.filter (fun x => δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)).card * S.card +
          (K.filter (fun x => ¬δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)).card * (δ^2/2 * S.card) := by simp
      _ ≤ (K.filter (fun x => δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)).card * S.card +
          K.card * (δ^2/2 * S.card) := by gcongr; simp
      _ < (δ^2/2 * K.card) * S.card +
        K.card * (δ^2/2 * S.card) := by gcongr
      _ = δ^2 * K.card * S.card := by ring
  suffices δ^2 * K.card^2 * S.card ≤ ∑ i ∈ K, ∑ j ∈ K, ((f j) ∩ (f i)).card by
    by_contra! nh
    absurd this
    simp only [Nat.cast_sum, not_le]
    convert_to _ < ∑ i ∈ K, δ^2 * K.card * S.card
    simp; ring
    apply sum_lt_sum
    intro i hi
    convert le_of_lt (nh i hi)
    norm_cast
    have ⟨i, hi⟩ := hK.bex
    exists i, hi
    convert nh i hi
    norm_cast
  rw [← ge_iff_le]
  calc (↑(∑ i ∈ K, ∑ j ∈ K, ((f j) ∩ (f i)).card) : ℝ)
    _ = ∑ i ∈ K, ∑ j ∈ K, (S.filter fun x => x ∈ f i ∧ x ∈ f j).card := by
      norm_cast
      apply sum_congr
      rfl
      intro x hx
      have : f x ⊆ S := (h x hx).1
      rw [subset_iff] at this
      rcongr
      aesop
    _ = ∑ i ∈ K, ∑ j ∈ K, ∑ x ∈ S, (if x ∈ f i ∧ x ∈ f j then 1 else 0) := by simp
    _ = ∑ i ∈ K, ∑ j ∈ K, ∑ x ∈ S, (if x ∈ f i then 1 else 0) * (if x ∈ f j then 1 else 0) := by simp only [ite_zero_mul_ite_zero, mul_one]
    _ = ∑ i ∈ K, ∑ x ∈ S, ∑ j ∈ K, (if x ∈ f i then 1 else 0) * (if x ∈ f j then 1 else 0) := by rcongr; rw [sum_comm]
    _ = ∑ x ∈ S, ∑ i ∈ K, ∑ j ∈ K, (if x ∈ f i then 1 else 0) * (if x ∈ f j then 1 else 0) := by rw [sum_comm]
    _ = ∑ x ∈ S, (∑ i ∈ K, (if x ∈ f i then 1 else 0)) * (∑ j ∈ K, (if x ∈ f j then 1 else 0)) := by rcongr; simp only [sum_mul_sum]
    _ = ∑ x ∈ S, (∑ i ∈ K, (if x ∈ f i then 1 else 0))^2 := by simp [sq]
    _ = (S.card : ℝ)⁻¹ * (S.card * ∑ x ∈ S, (∑ i ∈ K, (if x ∈ f i then 1 else 0))^2) := by field_simp
    _ ≥ (S.card : ℝ)⁻¹ * (∑ x ∈ S, ∑ i ∈ K, (if x ∈ f i then 1 else 0))^2 := by
      gcongr
      apply sq_sum_le_card_mul_sum_sq
    _ = (S.card : ℝ)⁻¹ * (∑ i ∈ K, ∑ x ∈ S, (if x ∈ f i then 1 else 0))^2 := by rw [sum_comm]
    _ = (S.card : ℝ)⁻¹ * (∑ i ∈ K, (f i).card)^2 := by
      congr
      norm_cast
      apply sum_congr
      rfl
      intro i hi
      simp only [sum_ite_mem, sum_const, smul_eq_mul, mul_one]
      congr
      simpa using (h i hi).1
    _ ≥ (S.card : ℝ)⁻¹ * (∑ __ ∈ K, δ * S.card)^2 := by
      push_cast
      gcongr with i hi
      exact (h i hi).2
    _ = (S.card : ℝ)⁻¹ * (K.card * (δ * S.card))^2 := by simp
    _ = δ^2 * K.card^2 * S.card := by field_simp; ring_nf

end general

-- set_option trace.profiler true
set_option maxHeartbeats 2000000

theorem Theorem335 (h : ∀ x ∈ T, K⁻¹ * A.card^3 ≤ E[A, x • A]) :
    ∃ A' ⊆ A,
    ∃ x : ZMod p,
    ∃ T' ⊆ (x • T),
    (2^4)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
    (2^17)⁻¹ * (K^4 : ℝ)⁻¹ * T.card ≤ T'.card ∧
    T' ⊆ Stab (2^110 * K^42) A' := by
  by_cases ane : A.Nonempty
  by_cases tne : T.Nonempty
  have t1 : ∀ x ∈ T, ∃ A' ⊆ A, ∃ B' ⊆ (x • A),
    (2 ^ 4)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
    (2 ^ 4)⁻¹ * K⁻¹ * A.card ≤ B'.card ∧
    (A' - B').card ≤ 2^10 * K^5 * (x • A).card^4 / A.card^3 := by
    intro x hx
    apply BSG₂
    linarith
    simp [ane]
    convert h x hx
    rw [card_of_inv]
    ring
    intro v
    rw [v] at hx
    contradiction
  have t2 : ∀ x ∈ T, ∃ A' ⊆ A, ∃ B' ⊆ A,
    (2 ^ 4)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
    (2 ^ 4)⁻¹ * K⁻¹ * A.card ≤ B'.card ∧
    (A' - x • B').card ≤ 2^10 * K^5 * A.card := by
    intro x hx
    have ⟨A', ha, B', hb, h⟩ := t1 x hx
    have : x ≠ 0 := fun v => h' (v ▸ hx)
    exists A', ha, x⁻¹ • B'
    simp only [← smul_assoc, smul_eq_mul, ne_eq, this, not_false_eq_true, mul_inv_cancel, one_smul]
    constructor
    · convert smul_finset_subset_smul_finset hb (a := x⁻¹)
      simp [← smul_assoc, this]
    · rw [card_of_inv] at h
      rw [card_of_inv]
      convert h using 3
      field_simp; ring
      simp [this]
      exact this
  clear t1
  let f (x : ZMod p) := if h : x ∈ T then (t2 x h).choose ×ˢ (t2 x h).choose_spec.2.choose else ∅
  have ⟨s, hs, hs₂⟩ := claim336 T tne f (A ×ˢ A) (by simp [ane]) (((2^4)⁻¹ * K⁻¹)^2) (by positivity) (fun v hv => by
    simp only [f, hv, dite_true]
    constructor
    · apply product_subset_product
      exact (t2 v hv).choose_spec.1
      exact (t2 v hv).choose_spec.2.choose_spec.1
    · simp
      convert_to ((2 ^ 4)⁻¹ * K⁻¹ * A.card) * ((2 ^ 4)⁻¹ * K⁻¹ * A.card) ≤ _
      ring
      gcongr
      exact (t2 v hv).choose_spec.2.choose_spec.2.1
      exact (t2 v hv).choose_spec.2.choose_spec.2.2.1
  )
  have : s ≠ 0 := fun v => h' (v ▸ hs)
  let A' := (t2 s hs).choose_spec.2.choose
  let T' := (filter (fun x => (((2 ^ 4)⁻¹ * K⁻¹) ^ 2) ^ 2 / 2 * ↑(A ×ˢ A).card ≤ ↑(f x ∩ f s).card) T)
  exists A', (t2 s hs).choose_spec.2.choose_spec.1, s⁻¹, s⁻¹ • T', smul_finset_subset_smul_finset <| filter_subset ..
  constructor
  · exact (t2 s hs).choose_spec.2.choose_spec.2.2.1
  constructor
  · convert hs₂ using 2
    ring
    change (s⁻¹ • T').card = T'.card
    apply card_of_inv
    simp [this]
  · rw [subset_iff]
    intro v' hv'
    rw [mem_smul_finset] at hv'
    have ⟨v, hv', h'''⟩ := hv'
    simp only [filter_congr_decidable, card_product, Nat.cast_mul, mem_filter, T'] at hv'
    have ⟨hv, h''⟩ := hv'
    rw [← h''']
    simp only [Stab, filter_congr_decidable, mem_filter, mem_univ, true_and]

    have vne : v ≠ 0 := fun nh => h' (nh ▸ hv)

    let X₁ := (t2 s hs).choose
    let Y₁ := (t2 s hs).choose_spec.2.choose

    have largeX₁ : (2^4)⁻¹ * K⁻¹ * A.card ≤ X₁.card := (t2 s hs).choose_spec.2.choose_spec.2.1
    have largeY₁ : (2^4)⁻¹ * K⁻¹ * A.card ≤ Y₁.card := (t2 s hs).choose_spec.2.choose_spec.2.2.1
    have small_diff₁ : (X₁ - s • Y₁).card ≤ 2^10 * K^5 * A.card := (t2 s hs).choose_spec.2.choose_spec.2.2.2

    let X₂ := (t2 v hv).choose
    let Y₂ := (t2 v hv).choose_spec.2.choose

    have largeX₂ : (2^4)⁻¹ * K⁻¹ * A.card ≤ X₂.card := (t2 v hv).choose_spec.2.choose_spec.2.1
    have largeY₂ : (2^4)⁻¹ * K⁻¹ * A.card ≤ Y₂.card := (t2 v hv).choose_spec.2.choose_spec.2.2.1
    have small_diff₂ : (X₂ - v • Y₂).card ≤ 2^10 * K^5 * A.card := (t2 v hv).choose_spec.2.choose_spec.2.2.2

    have X₁ss : X₁ ⊆ A := (t2 s hs).choose_spec.1
    have Y₁ss : Y₁ ⊆ A := (t2 s hs).choose_spec.2.choose_spec.1

    change (Y₁ + (s⁻¹ • v) • Y₁).card ≤ (2^110 * K^42) * Y₁.card

    unfold_let f at h''

    simp [hv, hs] at h''

    change (((2 ^ 4)⁻¹ * K⁻¹) ^ 2) ^ 2 / 2 * (A.card * A.card) ≤ (X₂ ×ˢ Y₂ ∩ X₁ ×ˢ Y₁).card at h''

    have h : (2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * (A.card * A.card) ≤ (X₂ ×ˢ Y₂ ∩ X₁ ×ˢ Y₁).card := by
      convert h'' using 2
      ring

    simp [product_inter_product] at h

    clear h'' hv' h'''
    clear v' hv' A' T' hs₂

    have iL' : (2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card ≤ (X₂ ∩ X₁).card * (Y₂ ∩ Y₁).card / A.card :=
      calc
      (2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card = ((2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * (A.card * A.card)) / A.card := by field_simp; ring
      _ ≤ (X₂ ∩ X₁).card * (Y₂ ∩ Y₁).card / A.card := by gcongr

    have i₁L : (2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card ≤ (X₂ ∩ X₁).card :=
      calc
      (2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card ≤ (X₂ ∩ X₁).card * (Y₂ ∩ Y₁).card / A.card := iL'
      _ ≤ (X₂ ∩ X₁).card * Y₁.card / A.card := by gcongr; apply inter_subset_right
      _ ≤ (X₂ ∩ X₁).card * A.card / A.card := by gcongr
      _ = (X₂ ∩ X₁).card := by field_simp

    have i₂L : (2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card ≤ (Y₂ ∩ Y₁).card :=
      calc
      (2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card ≤ (X₂ ∩ X₁).card * (Y₂ ∩ Y₁).card / A.card := iL'
      _ ≤ X₁.card * (Y₂ ∩ Y₁).card / A.card := by gcongr; apply inter_subset_right
      _ ≤ A.card * (Y₂ ∩ Y₁).card / A.card := by gcongr
      _ = (Y₂ ∩ Y₁).card := by field_simp

    calc ((Y₁ + (s⁻¹ • v) • Y₁).card : ℝ)
      _ = (s • (Y₁ + (s⁻¹ • v) • Y₁)).card := by rw [card_of_inv _ s this]
      _ = (s • Y₁ + (s • (s⁻¹ • v)) • Y₁).card := by rw [smul_add, ← smul_assoc]
      _ = (s • Y₁ + v • Y₁).card := by congr 4; simp [this]
      _ ≤ (s • Y₁ + v • Y₂).card * (v • Y₁ + v • Y₁).card / ((v • Y₂) ∩ (v • Y₁)).card := by
        have := add_of_large_intersection (v • Y₂) (s • Y₁) (v • Y₁) <| by
          rw [← card_pos, ← smul_finset_inter₀, card_of_inv]
          rify
          refine LT.lt.trans_le ?_ i₂L
          positivity
          assumption
          assumption
        rify at this
        exact this
      _ = (s • Y₁ + v • Y₂).card * ((s • v⁻¹) • (v • Y₁ + v • Y₁)).card / (Y₂ ∩ Y₁).card := by
        congr 2
        congr 1
        apply (card_of_inv ..).symm
        simp [this, vne]
        rw [← smul_finset_inter₀, card_of_inv]
        assumption
        assumption
      _ = (s • Y₁ + v • Y₂).card * (s • Y₁ + s • Y₁).card / (Y₂ ∩ Y₁).card := by
        rw [smul_add, smul_assoc]
        congr
        repeat simp [← smul_assoc, vne]
      _ ≤ (s • Y₁ + v • Y₂).card * (s • Y₁ + s • Y₁).card / ((2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card) := by
        gcongr
      _ ≤ (s • Y₁ + v • Y₂).card * ((s • Y₁ - X₁).card * (X₁ - s • Y₁).card / X₁.card) / ((2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card) := by
        gcongr
        rw [le_div_iff]
        norm_cast
        apply card_add_mul_le_card_sub_mul_card_sub
        refine LT.lt.trans_le ?_ largeX₁
        positivity
      _ = (s • Y₁ + v • Y₂).card * ((X₁ - s • Y₁).card * (X₁ - s • Y₁).card / X₁.card) / ((2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card) := by
        congr 5
        rw [← card_neg]
        simp
      _ ≤ (s • Y₁ + v • Y₂).card * ((2^10 * K^5 * A.card) * (2^10 * K^5 * A.card) / ((2^4)⁻¹ * K⁻¹ * A.card)) / ((2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card) := by
        gcongr
      _ = (s • Y₁ + v • Y₂).card * 2^41 * K^15 := by
        field_simp
        ring_nf
      _ ≤ ((s • Y₁ - X₂).card * (X₂ - v • Y₂).card / X₂.card) * 2^41 * K^15 := by
        gcongr
        rw [le_div_iff]
        norm_cast
        apply card_add_mul_le_card_sub_mul_card_sub
        refine LT.lt.trans_le ?_ largeX₂
        positivity
      _ ≤ ((s • Y₁ - X₂).card * (2^10 * K^5 * A.card) / ((2^4)⁻¹ * K⁻¹ * A.card)) * 2^41 * K^15 := by
        gcongr
      _ = (s • Y₁ + (-X₂)).card * 2^55 * K^21 := by rw [sub_eq_add_neg]; field_simp; ring_nf
      _ ≤ ((s • Y₁ + (-X₁)).card * ((-X₂) + (-X₂)).card / ((-X₁) ∩ (-X₂)).card) * 2^55 * K^21 := by
        gcongr
        have := add_of_large_intersection (-X₁) (s • Y₁) (-X₂) <| by
          rw [neg_inter_distrib, neg_nonempty_iff, ← card_pos, inter_comm]
          rify
          refine LT.lt.trans_le ?_ i₁L
          positivity
        rify at this
        exact this
      _ = ((X₁ - s • Y₁).card * (X₂ + X₂).card / (X₂ ∩ X₁).card) * 2^55 * K^21 := by
        congr 4
        rw [← card_neg]
        simp [sub_eq_add_neg]
        rw [← neg_add, card_neg]
        rw [neg_inter_distrib, card_neg, inter_comm]
      _ ≤ ((2^10 * K^5 * A.card) * (X₂ + X₂).card / ((2 ^ 17)⁻¹ * (K^4 : ℝ)⁻¹ * A.card)) * 2^55 * K^21 := by
        gcongr
      _ = (X₂ + X₂).card * 2^82 * K^30 := by field_simp; ring_nf
      _ ≤ ((X₂ - v • Y₂).card * (X₂ - v • Y₂).card / Y₂.card) * 2^82 * K^30 := by
        gcongr
        rw [le_div_iff]
        norm_cast
        convert card_add_mul_le_card_sub_mul_card_sub X₂ (v • Y₂) X₂ using 2
        · rwa [card_of_inv]
        · rw [← card_neg]
          simp
        refine LT.lt.trans_le ?_ largeY₂
        positivity
      _ ≤ ((2^10 * K^5 * A.card) * (2^10 * K^5 * A.card) / ((2^4)⁻¹ * K⁻¹ * A.card)) * 2^82 * K^30 := by
        gcongr
      _ = ((2^4)⁻¹ * K⁻¹ * A.card) * 2^110 * K^42 := by field_simp; ring_nf
      _ ≤ Y₁.card * 2^110 * K^42 := by gcongr
      _ = (2^110 * K^42) * Y₁.card := by ring
  · exists A, ?_, 1, ∅
    simp_all only [not_nonempty_iff_eq_empty, one_smul, Subset.refl, card_empty, CharP.cast_eq_zero,
      mul_zero, le_refl, empty_subset, and_self, and_true, true_and, not_mem_empty,
      not_false_eq_true, IsEmpty.forall_iff, forall_const]
    apply mul_le_of_le_one_left
    simp
    calc
      (2^4)⁻¹ * K⁻¹ ≤ (2^4)⁻¹ * 1⁻¹ := by gcongr
      _ ≤ 1 := by norm_num
  · exists ∅, ?_, 1, T
    simp
    simp_all only [not_nonempty_iff_eq_empty, one_smul, Subset.refl, card_empty, CharP.cast_eq_zero,
      mul_zero, le_refl, true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      smul_finset_empty, additiveEnergy_empty_right, implies_true, forall_const]
    constructor
    · apply mul_le_of_le_one_left
      simp
      calc
        (2^17)⁻¹ * (K^4)⁻¹ ≤ (2^17)⁻¹ * (1^4)⁻¹ := by gcongr
        _ ≤ 1 := by norm_num
    · simp only [Stab, smul_finset_empty, add_empty, card_empty, CharP.cast_eq_zero, mul_zero,
      le_refl, mem_univ, forall_true_left, forall_const, filter_true_of_mem, subset_univ]
