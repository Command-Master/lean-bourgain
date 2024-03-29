import Pseudorandom.Additive.Stab
import LeanAPAP.Extras.BSG

open Finset Pointwise

variable (K : ℝ) (hK : 1 ≤ K) (p : ℕ) [inst : Fact (p.Prime)] (A : Finset (ZMod p)) (T : Finset (ZMod p)) (h' : 0 ∉ T)

section general

open BigOps

lemma claim336 [DecidableEq α] (K : Finset β) (hK : K.Nonempty) (f : β → Finset α) (S : Finset α) (hS : S.Nonempty) (δ : ℝ) (hδ : 0 ≤ δ)
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
      _ ≤ ∑ j ∈ (K.filter (fun x => δ^2 /2 * S.card ≤ ((f x) ∩ (f i)).card)), S.card +
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
    _ = (S.card : ℝ)⁻¹ * (S.card * ∑ x ∈ S, (∑ i ∈ K, (if x ∈ f i then 1 else 0))^2) := by field_simp; ring
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
    _ ≥ (S.card : ℝ)⁻¹ * (∑ i ∈ K, δ * S.card)^2 := by
      push_cast
      gcongr with i hi
      exact (h i hi).2
    _ = (S.card : ℝ)⁻¹ * (K.card * (δ * S.card))^2 := by simp
    _ = δ^2 * K.card^2 * S.card := by field_simp; ring_nf

end general

theorem Theorem335 (h : ∀ x ∈ T, K⁻¹ * A.card^3 ≤ E[A, x • A]) :
    ∃ A' ⊆ A,
    ∃ x : ZMod p,
    ∃ T' ⊆ (x • T),
    (2^4)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
    (2^17)⁻¹ * (K^4 : ℝ)⁻¹ * T.card ≤ T'.card ∧
    T' ⊆ Stab (K ^ C3353) A' := by
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
    (A' - x • B').card ≤ 2^10 * K^5 * (x • A).card^4 / A.card^3 := by
    intro x hx
    have ⟨A', ha, B', hb, h⟩ := t1 x hx
    have : x ≠ 0 := fun v => h' (v ▸ hx)
    exists A', ha, x⁻¹ • B'
    simp only [← smul_assoc, smul_eq_mul, ne_eq, this, not_false_eq_true, mul_inv_cancel, one_smul]
    constructor
    · convert smul_finset_subset_smul_finset hb (a := x⁻¹)
      simp [← smul_assoc, this]
    · convert h using 4
      apply card_of_inv
      simp [this]
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
    intro v hv
    simp only [Stab, filter_congr_decidable, mem_filter, mem_univ, true_and]
    sorry


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
