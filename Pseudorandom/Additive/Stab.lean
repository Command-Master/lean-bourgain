import Mathlib.Tactic.Rify
import Pseudorandom.Additive.Constants
import Pseudorandom.Additive.Growth

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

lemma mem_Stab_le (h₁ : a ∈ Stab K A) (h₂ : K ≤ K₂) : a ∈ Stab K₂ A := by
  simp_all [Stab]
  refine' h₁.trans _
  gcongr

lemma Stab_subset : 3 • (Stab K A)^2 - 3 • (Stab K A)^2 ⊆ Stab (K^4374) A := by
  by_cases A.Nonempty
  suffices 3 • (Stab K A)^2 - 3 • (Stab K A)^2 ⊆ Stab (((K^162)^3)^9) A by
    have : (((K^162)^3)^9) = (K^4374) := by simp [← pow_mul]
    rwa [← this]
  suffices ss : 3 • (Stab K A)^2 ⊆ Stab (K^162) A by
    rw [subset_iff]
    intro x hx
    simp [mem_sub] at hx
    have ⟨y, hy, z, hz, h⟩ := hx
    rw [subset_iff] at ss
    have ym : y ∈ Stab (K^162) A := ss hy
    have zm : z ∈ Stab (K^162) A := ss hz
    rw [sub_eq_add_neg] at h
    have nzm : -z ∈ Stab ((K^162)^3) A := Stab_neg A zm
    have ym : y ∈ Stab ((K^162)^3) A := mem_Stab_le A ym (by
      apply le_self_pow
      apply one_le_of_mem A (by assumption) ym
      norm_num
    )
    rw [← h]
    apply Stab_add <;> assumption
  have : 3 • (Stab K A)^2 = (Stab K A)^2 + (Stab K A)^2 + (Stab K A)^2 := by abel
  rw [this]
  have : (((K^2)^9)^9) = (K^162) := by simp [← pow_mul]
  rw [← this]
  suffices ss : (Stab K A)^2 ⊆ Stab (K^2) A by
    rw [subset_iff]
    intro x hx
    simp [mem_add] at hx
    have ⟨a, ha, b, hb, c, hc, h⟩ := hx
    rw [subset_iff] at ss
    apply ss at ha
    apply ss at hb
    apply ss at hc
    have a1m : a + b ∈ Stab ((K^2)^9) A := Stab_add A ha hb
    have m2 : c ∈ Stab ((K^2)^9) A := mem_Stab_le A hc (by
      apply le_self_pow
      apply one_le_of_mem A (by assumption) hc
      norm_num
    )
    have : (a + b) + c ∈ Stab (((K^2)^9)^9) A := Stab_add A a1m m2
    rw [← h]
    exact this
  rw [sq]
  rw [subset_iff]
  intro x hx
  simp [mem_mul] at hx
  have ⟨a, ha, b, hb, h⟩ := hx
  rw [← h]
  apply Stab_mul <;> assumption
  · simp_all [Stab]

lemma Stab_card_inc (p : ℕ) [Fact (p.Prime)] (A : Finset (ZMod p)) :
    (min ((Stab K A).card^2) p / 2 : ℚ) ≤ (Stab (K^4374) A).card := by
  have := Stab_subset A (K := K)
  have := card_le_card this
  suffices (min ((Stab K A).card^2) p / 2 : ℚ) ≤ (3 • (Stab K A)^2 - 3 • (Stab K A)^2).card by
    refine' this.trans _
    norm_cast
  apply GUS

lemma Stab_card_inc' (p : ℕ) [Fact (p.Prime)] (A : Finset (ZMod p)) (h : 4 ≤ (Stab K A).card) :
    (min ((Stab K A).card^(3/2 : ℝ)) (p / 2) : ℝ) ≤ (Stab (K^4374) A).card := by
  have := Stab_card_inc (K := K) p A
  rify at this
  refine' LE.le.trans _ this
  rw [← min_div_div_right]
  apply min_le_min_right
  rw [← one_le_div]
  rw [div_right_comm, ← rpow_nat_cast, ← rpow_sub]
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


lemma Stab_card_inc_rep (p : ℕ) [Fact (p.Prime)] (A : Finset (ZMod p)) (h : 4 ≤ (Stab K A).card) (n : ℕ):
    (min ((Stab K A).card^((3/2 : ℝ)^n)) (p / 2) : ℝ) ≤ (Stab (K^4374^n) A).card := by
  by_cases A.Nonempty
  induction n
  · simp
  · rename_i n hn
    have : 4 ≤ (Stab (K^4374^n) A).card := by
      refine' h.trans _
      gcongr
      rw [subset_iff]
      intro x hx
      apply mem_Stab_le A hx
      apply le_self_pow
      apply one_le_of_mem A
      assumption
      exact hx
      simp
    have := Stab_card_inc' (K := (K^4374^n)) p A this
    rw [← pow_mul, ← pow_succ'] at this
    refine' LE.le.trans _ this
    simp [-div_pow]
    simp [-div_pow] at hn
    rcases hn with hp | hq
    · left
      refine' LE.le.trans _ (rpow_le_rpow (z := 3/2) _ hp _)
      rw [← rpow_mul, ← pow_succ']
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
  · simp_all [Stab]
    right
    rw [card_univ]
    simp


lemma Stab_full' (p : ℕ) [inst : Fact (p.Prime)] (A : Finset (ZMod p)) (β : ℝ) (βpos : 0 < β) (h : 4 ≤ (Stab K A).card) (h₂ : (p ^ β : ℝ) ≤ (Stab K A).card) :
    (p/2 : ℝ) ≤ (Stab (K ^ full_C₂ β) A).card := by
  let n := ⌈Real.logb (3/2 : ℝ) (1 / β)⌉₊
  simp only [full_C₂]
  change (p/2 : ℝ) ≤ (Stab (K ^ 4374^n) A).card
  have := Stab_card_inc_rep (K := K) p A h n
  refine' LE.le.trans _ this
  simp only [le_min_iff, le_refl, and_true]
  have : (p / 2 : ℝ) ≤ p := by simp
  refine' this.trans _
  -- apply_fun (fun x:ℝ => x^(3/2 : ℝ)^n) at h₂
  -- TODO: replace by correct
  simp only at h₂
  refine' LE.le.trans _ h₂
  conv =>
    lhs
    apply (rpow_one _).symm
  rw [← rpow_mul]
  apply rpow_le_rpow_of_exponent_le
  have := inst.out.one_le
  simp [this]
  simp only [n]

  sorry
  sorry
