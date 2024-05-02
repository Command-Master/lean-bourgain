import Mathlib.Tactic.Rify
import Pseudorandom.Additive.Constants
import Pseudorandom.Additive.Growth
import Mathlib.Combinatorics.SetFamily.CauchyDavenport

variable {α : Type*} [Field α] [Fintype α] [DecidableEq α]
  (A B C : Finset α) {K K₁ K₂ : ℝ} {a b : α}

open NNRat Real BigOperators Finset Pointwise

noncomputable def Stab (K : ℝ) (A : Finset α) := (univ : Finset α).filter fun a => (A + a • A).card ≤ K * A.card

lemma Stab_inv' (h : a ∈ Stab K A) : 1/a ∈ Stab K A := by
  by_cases a = 0
  · simp_all
  simp [Stab] at h
  simp [Stab]
  calc ((A + a⁻¹ • A).card : ℝ)
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
    (A.card : ℝ) ≤ (A + a • A).card := by
      norm_cast
      apply card_le_card_add_right
      simp [hA]
    _ ≤ K * A.card := by assumption
    _ < 1 * A.card := by gcongr
    _ = A.card := by simp
  linarith

lemma Stab_neg' (h : a ∈ Stab K A) : -a ∈ Stab (K^3) A := by
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
  calc ((A - a • A).card : ℝ)
    _ ≤ (A + a • A).card^3 / (A.card * (a • A).card) := by
      have := sub_le_add A (a • A)
      rify at this
      exact this
    _ ≤ (K * A.card)^3 / (A.card * (a • A).card) := by gcongr
    _ = (K * A.card)^3 / (A.card * A.card) := by rwa [card_of_inv]
    _ = K^3 * A.card := by field_simp; ring

lemma Stab_add' (h₁ : a ∈ Stab K₁ A) (h₂ : b ∈ Stab K₂ A) : a + b ∈ Stab (K₁^8 * K₂) A := by
  by_cases A.Nonempty
  have : 1 ≤ K₁ := one_le_of_mem A (by assumption) h₁
  have : 1 ≤ K₂ := one_le_of_mem A (by assumption) h₂
  by_cases a ≠ 0
  simp_all only [Stab, mem_filter, mem_univ, true_and, ne_eq, ge_iff_le]
  calc ((A + (a + b) • A).card : ℝ)
    _ ≤ (A + (a • A + b • A)).card := by
      gcongr
      apply add_subset_add_left (s := A)
      apply add_smul_subset_smul_add_smul
    _ = (A + a • A + b • A).card := by abel_nf
    _ ≤ (b • A + A).card * (A + a • A).card^8 / (A.card^6 * (a • A).card^2) := by
      have := triple_add A (a • A) (b • A)
      rify at this
      exact this
    _ = (A + b • A).card * (A + a • A).card^8 / (A.card^6 * A.card^2) := by
      congr 4
      abel
      apply card_of_inv
      assumption
    _ ≤ (K₂ * A.card) * (K₁ * A.card)^8 / (A.card^6 * A.card^2) := by gcongr
    _ = K₁^8 * K₂ * A.card := by field_simp; ring_nf
  · simp_all only [Stab, mem_filter, mem_univ, true_and, ne_eq, not_not, zero_add, ge_iff_le,
    zero_smul_finset, add_zero]
    calc
      ((A + b•A).card : ℚ) ≤ K₂ * A.card := by assumption
      _ ≤ 1^8 * K₂ * A.card := by simp
      _ ≤ K₁^8 * K₂ * A.card := by gcongr
  · simp_all [Stab]


lemma Stab_mul' (h₁ : a ∈ Stab K₁ A) (h₂ : b ∈ Stab K₂ A) : a * b ∈ Stab (K₁ * K₂) A := by
  by_cases ane : A.Nonempty
  have := one_le_of_mem A ane h₁
  have := one_le_of_mem A ane h₂
  by_cases h : a ≠ 0
  apply Stab_inv' at h₁
  simp_all [Stab]
  calc ((A + (a * b) • A).card : ℝ)
    _ = (a⁻¹ • (A + (a * b) • A)).card := by rw [card_of_inv]; simp [h]
    _ = (a⁻¹ • A + a⁻¹ • (a * b) • A).card := by simp
    _ = (a⁻¹ • A + (a⁻¹ • (a * b)) • A).card := by rw [smul_assoc]
    _ = (a⁻¹ • A + b • A).card := by congr; field_simp
    _ = ((a⁻¹ • A + b • A).card * A.card) / A.card := by field_simp
    _ ≤ ((a⁻¹ • A + A).card * (A + b • A).card) / A.card := by
      gcongr ?X / _
      norm_cast
      apply card_add_mul_card_le_card_add_mul_card_add
    _ ≤ ((A + a⁻¹ • A).card * (A + b • A).card) / A.card := by rw [add_comm]
    _ ≤ ((K₁ * A.card) * (K₂ * A.card)) / A.card := by gcongr
    _ = K₁ * K₂ * A.card := by field_simp; ring
  · simp_all [Stab]
    calc (A.card : ℝ)
      _ ≤ K₁ * A.card := by assumption
      _ = (1*K₁) * A.card := by ring
      _ ≤ (K₂*K₁) * A.card := by gcongr;
      _ = K₁ * K₂ * A.card := by ring
  · simp_all [Stab]

lemma Stab_le' (h₁ : a ∈ Stab K A) (h₂ : K ≤ K₂) : a ∈ Stab K₂ A := by
  simp_all [Stab]
  refine' h₁.trans _
  gcongr

lemma Stab_le (h₂ : K ≤ K₂) : (Stab K A) ⊆ (Stab K₂ A) := by
  rw [subset_iff]
  intro x hx
  apply Stab_le'
  exact hx
  exact h₂

lemma Stab_le₂ (h₂ : 1 ≤ K → K ≤ K₂) : (Stab K A) ⊆ (Stab K₂ A) := by
  by_cases A.Nonempty
  · rw [subset_iff]
    intro x hx
    apply Stab_le'
    exact hx
    apply h₂
    apply one_le_of_mem A
    assumption
    exact hx
  · simp_all [Stab]

lemma Stab_add : (Stab K₁ A) + (Stab K₂ A) ⊆ (Stab (K₁^8 * K₂) A) := by
  rw [subset_iff]
  intro x hx
  rw [mem_add] at hx
  have ⟨a, ha, b, hb, h⟩ := hx
  rw [← h]
  apply Stab_add' <;> assumption

lemma Stab_neg : -(Stab K A) ⊆ (Stab (K^3) A) := by
  rw [subset_iff]
  intro x hx
  rw [mem_neg] at hx
  have ⟨y, hy, h⟩ := hx
  rw [← h]
  apply Stab_neg'
  assumption

lemma Stab_sub : (Stab K₁ A) - (Stab K₂ A) ⊆ (Stab (K₁^8 * K₂^3) A) := calc
  (Stab K₁ A) - (Stab K₂ A) = (Stab K₁ A) + (-(Stab K₂ A)) := by rw [sub_eq_add_neg]
  _ ⊆ (Stab K₁ A) + (Stab (K₂^3) A) := by apply add_subset_add_left; apply Stab_neg
  _ ⊆ Stab (K₁^8 * K₂^3) A := by apply Stab_add

lemma Stab_mul : (Stab K₁ A) * (Stab K₂ A) ⊆ (Stab (K₁ * K₂) A) := by
  rw [subset_iff]
  intro x hx
  rw [mem_mul] at hx
  have ⟨a, ha, b, hb, h⟩ := hx
  rw [← h]
  apply Stab_mul' <;> assumption

lemma Stab_nsmul (n : ℕ) : (n+1) • (Stab K A) ⊆ (Stab (K ^ (8*n + 1)) A) := by
  induction n
  · simp
  · rename_i n hn
    calc
      (n.succ + 1) • (Stab K A) = n.succ • (Stab K A) + (Stab K A) := by rw [add_nsmul]; simp
      _ ⊆ (Stab (K ^ (8*n + 1)) A) + (Stab K A) := by apply add_subset_add_right; assumption
      _ = (Stab K A) + (Stab (K ^ (8*n + 1)) A) := by abel
      _ ⊆ (Stab (K^8 * (K ^ (8*n + 1))) A) := by apply Stab_add
      _ = (Stab (K ^ (8*n.succ + 1)) A) := by congr 1; rw [← pow_add]; congr 1; rw [Nat.succ_eq_add_one]; ring

lemma Stab_subset : 3 • (Stab K A)^2 - 3 • (Stab K A)^2 ⊆ Stab (K^374) A := by
  suffices 3 • (Stab K A)^2 ⊆ Stab (K^34) A by
    calc 3 • (Stab K A)^2 - 3 • (Stab K A)^2
      _ ⊆ (Stab (K^34) A) - (Stab (K^34) A) := by apply sub_subset_sub <;> exact this
      _ ⊆ Stab ((K^34)^8 * (K^34)^3) A := by apply Stab_sub
      _ = Stab (K^374) A := by simp [← pow_mul, ← pow_add]
  calc 3 • (Stab K A)^2
    _ ⊆ 3 • (Stab (K^2) A) := by
      apply nsmul_subset_nsmul
      rw [sq, sq]
      apply Stab_mul
    _ ⊆ (Stab ((K^2)^(8*2+1)) A) := Stab_nsmul ..
    _ = Stab (K^34) A := by rw [← pow_mul]

variable (K : ℝ) (p : ℕ) [inst : Fact (p.Prime)] (A : Finset (ZMod p)) (β γ : ℝ)

lemma Stab_card_inc :
    (min ((Stab K A).card^2) p / 2 : ℚ) ≤ (Stab (K^374) A).card := by
  have := Stab_subset A (K := K)
  have := card_le_card this
  suffices (min ((Stab K A).card^2) p / 2 : ℚ) ≤ (3 • (Stab K A)^2 - 3 • (Stab K A)^2).card by
    refine' this.trans _
    norm_cast
  apply GUS

lemma Stab_card_inc' (p : ℕ) [Fact (p.Prime)] (A : Finset (ZMod p)) (h : 4 ≤ (Stab K A).card) :
    (min ((Stab K A).card^(3/2 : ℝ)) (p / 2) : ℝ) ≤ (Stab (K^374) A).card := by
  have := Stab_card_inc (K := K) p A
  rify at this
  refine' LE.le.trans _ this
  rw [← min_div_div_right]
  apply min_le_min_right
  rw [← one_le_div]
  rw [div_right_comm, ← rpow_natCast, ← rpow_sub]
  norm_num
  simp
  rw [one_le_div, le_rpow_inv_iff_of_pos]
  norm_num
  assumption
  norm_num
  simp
  norm_num
  norm_num
  norm_cast
  omega
  apply rpow_pos_of_pos
  norm_cast
  omega
  norm_num


lemma Stab_card_inc_rep (h : 4 ≤ (Stab K A).card) (n : ℕ):
    (min ((Stab K A).card^((3/2 : ℝ)^n)) (p / 2) : ℝ) ≤ (Stab (K^374^n) A).card := by
  induction n
  · simp
  · rename_i n hn
    have : 4 ≤ (Stab (K^374^n) A).card := by
      refine' h.trans _
      gcongr
      apply Stab_le₂
      intro h
      apply le_self_pow h
      simp
    have := Stab_card_inc' (K := (K^374^n)) p A this
    rw [← pow_mul, ← pow_succ] at this
    refine' LE.le.trans _ this
    simp [-div_pow]
    simp [-div_pow] at hn
    rcases hn with hp | hq
    · left
      refine' LE.le.trans _ (rpow_le_rpow (z := 3/2) _ hp _)
      rw [← rpow_mul, ← pow_succ]
      simp
      apply rpow_nonneg
      simp
      norm_num
    · right
      refine' hq.trans _
      conv =>
        lhs
        apply (rpow_one _).symm
      apply rpow_le_rpow_of_exponent_le
      simp
      omega
      norm_num


lemma Stab_full' (βpos : 0 < β) (h : 4 ≤ (Stab K A).card) (h₂ : (p ^ β : ℝ) ≤ (Stab K A).card) :
    (p/2 : ℝ) ≤ (Stab (K ^ full_C₂ β) A).card := by
  let n := ⌈Real.logb (3/2 : ℝ) (1 / β)⌉₊
  simp only [full_C₂]
  change (p/2 : ℝ) ≤ (Stab (K ^ 374^n) A).card
  have := Stab_card_inc_rep (K := K) p A h n
  refine' LE.le.trans _ this
  simp only [le_min_iff, le_refl, and_true]
  have : (p / 2 : ℝ) ≤ p := by simp
  refine' this.trans _
  have h₂ : ((p ^ β) ^ (3/2: ℝ)^n : ℝ) ≤ (Stab K A).card ^ (3/2: ℝ)^n := by
    gcongr
  refine' LE.le.trans _ h₂
  conv =>
    lhs
    apply (rpow_one _).symm
  rw [← rpow_mul]
  apply rpow_le_rpow_of_exponent_le
  have := inst.out.one_le
  simp [this]
  simp only [n]
  calc
    1 = β * (3/2) ^ (Real.logb (3/2 : ℝ) (1 / β)) := by
      rw [Real.rpow_logb]
      simp
      rw [mul_inv_cancel]
      positivity
      norm_num
      norm_num
      positivity
    _ ≤ β * (3/2) ^ (n : ℝ) := by
      gcongr
      norm_num
      simp only [n]
      apply Nat.le_ceil
    _ = β * (3/2) ^ n := by simp [Real.rpow_natCast]
  simp

lemma Stab_full (βpos : 0 < β) (h : 4 ≤ (Stab K A).card) (h₂ : (p ^ β : ℝ) ≤ (Stab K A).card) :
    (Stab (K ^ full_C β) A) = univ := by
  have := Stab_full' _ p A β βpos h h₂
  rw [← Nat.ceil_le] at this
  have card_bound : (Stab K A).card ≤ univ.card := by gcongr; simp
  simp only [card_univ, ZMod.card] at card_bound
  have ⟨pd, hp⟩ : Odd p := inst.out.odd_of_ne_two (by omega)
  have t2 : ⌈(p / 2 : ℝ)⌉₊ = pd + 1 := calc
    ⌈(p / 2 : ℝ)⌉₊ = ⌈((2*pd + 1) / 2 : ℝ)⌉₊ := by rw [hp]; congr; norm_cast
    _ = ⌈pd + (1 / 2 : ℝ)⌉₊ := by congr; field_simp; ring
    _ = pd + 1 := by
      apply le_antisymm
      · norm_num
      · by_contra! nh
        rw [Nat.lt_add_one_iff] at nh
        simp only [one_div, Nat.ceil_le, add_le_iff_nonpos_right, inv_nonpos] at nh
        linarith
  rw [t2] at this
  apply eq_of_subset_of_card_le
  simp
  simp only [card_univ, ZMod.card]
  calc
     p ≤ min p ((Stab (K ^ full_C₂ β) A).card + (Stab (K ^ full_C₂ β) A).card - 1) := by
      simp only [le_min_iff, le_refl, true_and]
      omega
     _ ≤ ((Stab (K ^ full_C₂ β) A) + (Stab (K ^ full_C₂ β) A)).card := by
      apply ZMod.min_le_card_add
      exact inst.1
      repeat {
      rw [← card_pos]
      have : (Stab K A).card ≤ (Stab (K ^ full_C₂ β) A).card := by
        gcongr
        apply Stab_le₂
        intro h
        apply le_self_pow h
        simp [full_C₂]
      linarith
      }
     _ ≤ (Stab (K ^ full_C β) A).card := by
      gcongr
      convert Stab_add (K₁ := (K ^ full_C₂ β)) (K₂ := (K ^ full_C₂ β)) A
      simp [full_C, ← pow_mul, ← pow_add]
      rfl

lemma Stab_no_full (A : Finset α)
    (h : ((Fintype.card α) ^ β : ℝ) ≤ A.card) (h₂ : A.card ≤ ((Fintype.card α) ^ (1-β) : ℝ)) (h₃ : K < ((Fintype.card α)^β / 2 : ℝ)) :
    (Stab K A) ≠ univ := by
  have ⟨a, _, ha2⟩ := exists_grower A
  rify at ha2
  apply_fun (a ∈ ·)
  simp only [Stab, filter_congr_decidable, mem_filter, mem_univ, true_and, ne_eq, eq_iff_iff,
    iff_true, not_le]
  refine' LT.lt.trans_le _ ha2
  have : (K * A.card : ℝ) < (Fintype.card α^β / 2) * A.card := by
    gcongr
    calc
      (0 : ℝ) < (Fintype.card α)^β := by positivity
      _ ≤ A.card := by assumption
  refine' LT.lt.trans_le this _
  simp only [Nat.cast_min, Nat.cast_pow, ge_iff_le, Nat.ofNat_nonneg, ← min_div_div_right,
    le_min_iff]
  constructor
  · calc ((Fintype.card α^β / 2) * A.card : ℝ)
      _ ≤ (A.card / 2) * A.card := by gcongr
      _ = A.card^2/2 := by ring
  · calc ((Fintype.card α^β / 2) * A.card : ℝ)
      _ ≤ (Fintype.card α^β / 2) * (Fintype.card α) ^ (1-β) := by gcongr
      _ = Fintype.card α^(β + (1-β)) / 2 := by rw [rpow_add]; ring; positivity
      _ = Fintype.card α / 2 := by simp

lemma Stab_small (β : ℝ) (βpos : 0 < β) (h : 4 ≤ (Stab K A).card) (h₂ : (p ^ β : ℝ) ≤ (Stab K A).card)
  (γ : ℝ) (h₃ : (p ^ γ : ℝ) ≤ A.card) (h₄ : A.card ≤ (p ^ (1-γ) : ℝ)) :
  (p^γ / 2 : ℝ) ≤ (K ^ full_C β) := by
  by_contra! nh
  absurd Stab_full K p A β βpos h h₂
  apply Stab_no_full (β := γ)
  simp [h₃]
  simp [h₄]
  simp [nh]
