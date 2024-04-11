import Pseudorandom.Additive.EnergyGrowth
import Pseudorandom.Incidence.Claim342_grid
set_option autoImplicit false

open Real BigOps Finset Pointwise

variable {p : ℕ} [instpprime : Fact p.Prime]

local notation "α" => (ZMod p)

set_option maxHeartbeats 1000000

theorem ST_grid_final (β : ℝ) (h : 0 < β) (A B : Finset α) (n : ℕ+) (nhₗ : (p^β : ℝ) ≤ n)
  (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
  (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
  (b₁ : α) (hb₁ : ¬b₁ ∈ B) (b₂ : α)
  (hb₂ : ¬b₂ ∈ B) (neq : b₁ ≠ b₂)
  (allInt : ∀ b ∈ B, (n ^ (1 - SG_eps₃ β) : ℝ) < ∑ v ∈ A ×ˢ A, if (b₂ - b) / (b₂ - b₁) * v.1 + (b - b₁) / (b₂ - b₁) * v.2 ∈ A then 1 else 0):
  B.card < (SG_C₅ * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β) : ℝ) := by
  by_cases bne : B.Nonempty
  have nd0₃ : ¬(b₂ - b₁ = 0) := fun v => neq (eq_of_sub_eq_zero v).symm
  have aLarge' : (n^(1 - SG_eps₃ β) : ℝ) < A.card * A.card := by
    have ⟨bv, hb⟩ := bne.bex
    calc
      (n^(1 - SG_eps₃ β) : ℝ) <
          ∑ v ∈ A ×ˢ A, if (b₂ - bv) / (b₂ - b₁) * v.1 + (bv - b₁) / (b₂ - b₁) * v.2 ∈ A then 1 else 0 := allInt bv hb
      _ ≤ ∑ v ∈ A ×ˢ A, 1 := by gcongr; split <;> norm_num
      _ = A.card * A.card := by simp
  have aLarge : (n^(1/2 - 1/2 * SG_eps₃ β) : ℝ) < A.card := calc
    (n^(1/2 - 1/2 * SG_eps₃ β) : ℝ) = ((n^(1/2 - 1/2 * SG_eps₃ β) : ℝ)^2)^((2 : ℝ)⁻¹) := by
      rw [eq_rpow_inv]
      simp only [rpow_two]
      apply rpow_nonneg
      simp
      apply sq_nonneg
      norm_num
    _ = ((n^(1 - SG_eps₃ β) : ℝ))^((2 : ℝ)⁻¹) := by
      congr 1
      rw [← rpow_mul_natCast]
      ring_nf
      simp
    _ < (A.card * A.card) ^ ((2 : ℝ)⁻¹) := by gcongr
    _ = A.card := by rw [← sq, ← rpow_natCast_mul]; simp; simp
  have ane : A.Nonempty := by
    rw [← card_pos]
    rify
    refine lt_of_le_of_lt ?_ aLarge
    apply rpow_nonneg
    simp
  have : ∀ b ∈ B, (4⁻¹ * (n^(2 - 2 * SG_eps₃ β - (1/2 + 2*ST_prime_field_eps β)) : ℝ)) < additiveEnergy A (((b₂ - b) / (b -b₁)) • A) := by
    intro b hb
    have nd0 : ¬(b₂ - b = 0) := fun h => hb₂ ((eq_of_sub_eq_zero h) ▸ hb)
    have nd0₂ : ¬(b - b₁ = 0) := fun h => hb₁ ((eq_of_sub_eq_zero h) ▸ hb)
    have := allInt b hb
    -- simp at this
    calc (E[A, (((b₂ - b) / (b - b₁)) • A)] : ℝ)
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
      _ ≥ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ)⁻¹ * (n^(1 - SG_eps₃ β))^2 := by
        gcongr
      _ = (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ)⁻¹ * (n^(2 - 2 * SG_eps₃ β)) := by
        congr 1
        rw [←rpow_nat_cast, ←rpow_mul]
        ring_nf
        simp
      _ = 4⁻¹ * (n^(2 - 2 * SG_eps₃ β) / n^(1/2 + 2*ST_prime_field_eps β) : ℝ) := by
        ring
      _ = 4⁻¹ * (n^(2 - 2 * SG_eps₃ β - (1/2 + 2*ST_prime_field_eps β)) : ℝ) := by rw [←rpow_sub]; simp
  have ⟨A', hA', x, T', hT, hAsz, hTsz, hStab⟩ :=
    Theorem335 (256 * n^(8 * ST_prime_field_eps β + 2*SG_eps₃ β)) (by
        rw [(by norm_num : (1 : ℝ) = 1*1)]
        apply mul_le_mul
        norm_num
        apply one_le_rpow
        norm_cast
        simp
        apply add_nonneg
        simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
        apply lemma9 β h
        simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
        apply lemma10 β h
        norm_num
        norm_num
      ) _ A (B.image fun x => (b₂ - x) / (x - b₁))
      (by
        simp only [mem_image, div_eq_zero_iff, not_exists, not_and]
        intro x hx
        rintro (v | v)
        · exact hb₂ ((eq_of_sub_eq_zero v) ▸ hx)
        · exact hb₁ ((eq_of_sub_eq_zero v) ▸ hx))
      (by
        intro x' hx'
        simp at hx'
        have ⟨b, hb, h'⟩ := hx'
        rw [← h']
        have := le_of_lt <| this b hb
        refine LE.le.trans ?_ this
        rw [inv_mul_le_iff]
        calc (A.card ^ 3 : ℝ)
          _ ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β))^3 := by gcongr
          _ = 64 * (n^(1/2 + 2*ST_prime_field_eps β))^3 * 1 := by ring
          _ = 64 * (n^(3/2 + 6*ST_prime_field_eps β)) *
            ((n ^ (2 - 2 * SG_eps₃ β - (1 / 2 + 2 * ST_prime_field_eps β)) : ℝ)⁻¹ *
              n ^ (2 - 2 * SG_eps₃ β - (1 / 2 + 2 * ST_prime_field_eps β))) := by
            congr 2
            rw [← rpow_mul_natCast]
            ring_nf
            simp
            rw [inv_mul_cancel]
            apply ne_of_gt
            apply rpow_pos_of_pos
            simp
          _ = 256 * ((n^(3/2 + 6*ST_prime_field_eps β)) /
            (n ^ (2 - 2 * SG_eps₃ β - (1 / 2 + 2 * ST_prime_field_eps β)))) *
              4⁻¹ * n ^ (2 - 2 * SG_eps₃ β - (1 / 2 + 2 * ST_prime_field_eps β)) := by ring
          _ = 256 * (n^(3/2 + 6*ST_prime_field_eps β- (2 - 2 * SG_eps₃ β - (1 / 2 + 2 * ST_prime_field_eps β)))) *
              4⁻¹ * n ^ (2 - 2 * SG_eps₃ β - (1 / 2 + 2 * ST_prime_field_eps β)) := by
            congr
            rw [← rpow_sub]
            simp
          _ = (256 * n^(8 * ST_prime_field_eps β + 2*SG_eps₃ β)) *
              (4⁻¹ * n ^ (2 - 2 * SG_eps₃ β - (1 / 2 + 2 * ST_prime_field_eps β))) := by ring_nf
        simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
        apply rpow_pos_of_pos
        simp
        )
  -- simp only [SG_C₅, NNReal.coe_one, one_div, one_mul, gt_iff_lt]
  by_contra! nh
  -- rel [nh] at hTsz
  have bieq : (B.image fun x => (b₂ - x) / (x - b₁)).card = B.card := by
    rw [card_image_of_injOn]
    intro x₁ h₁ x₂ h₂ h
    dsimp at h
    have : x₁ - b₁ ≠ 0 := fun v => hb₁ (eq_of_sub_eq_zero v ▸ h₁)
    have : x₂ - b₁ ≠ 0 := fun v => hb₁ (eq_of_sub_eq_zero v ▸ h₂)
    field_simp at h
    ring_nf at h
    have : x₁ * (b₁ - b₂) = x₂ * (b₁ - b₂) := by linear_combination h
    rw [mul_left_inj'] at this
    exact this
    intro v
    simp only [eq_of_sub_eq_zero v, ne_eq, not_true_eq_false] at neq
  rw [bieq] at hTsz
  let K' : ℝ := (2 ^ 110 * (256 * n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) ^ 42)

  have nhTsz :
    (n ^ (1 / 2 - 439 / 45 * SG_eps₃ β) : ℝ) ≤ T'.card := calc
        (n ^ (1 / 2 - 439 / 45 * SG_eps₃ β) : ℝ)
    _ = (2 ^ 17)⁻¹ * ((256 * ↑n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) ^ 4)⁻¹ *
        (SG_C₅ * ↑↑n ^ (1 / 2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β)) := by
      unfold SG_C₅
      field_simp
      ring_nf!
      rw [← rpow_neg, ← rpow_mul_natCast, ← rpow_add]
      congr 1
      unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
      ring_nf
      simp
      simp
      simp
    _ ≤
      (2 ^ 17)⁻¹ * ((256 * ↑↑n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) ^ 4)⁻¹ *
      B.card := by gcongr
    _ ≤ T'.card := by
      exact hTsz
  clear hTsz bieq hT allInt this aLarge' hb₁ hb₂ nd0₃ neq b₁ b₂
  apply card_le_card at hStab
  rify at hStab
  apply nhTsz.trans at hStab
  clear nhTsz T' x

  have nLarge := nh.trans hB

  rw [← le_div_iff, mul_div_assoc, ← rpow_sub, ← div_le_iff'] at nLarge
  ring_nf at nLarge

  change (_ : ℝ) ≤ (Stab K' A').card at hStab

  have fourlt : 4 ≤ (Stab K' A').card := by
    rify
    calc
      (4 : ℝ) ≤ SG_C₅ * (1 / 4) := by unfold SG_C₅; norm_num
      _ ≤ n ^ (ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β) := nLarge
      _ ≤ n^(1/2 - 439/45 * SG_eps₃ β) := by gcongr; norm_cast; simp; apply lemma13
      _ ≤ (Stab K' A').card := hStab

  have hStab' :
      (p ^ (β / 2 - 439 / 45 * β * SG_eps₃ β) : ℝ) ≤ (Stab K' A').card := calc
    (p ^ (β / 2 - 439 / 45 * β * SG_eps₃ β) : ℝ) = (p ^ β) ^ (1 / 2 - 439 / 45 * SG_eps₃ β) := by
      rw [← rpow_mul]; congr 1; ring_nf; simp
    _ ≤ n ^ (1 / 2 - 439 / 45 * SG_eps₃ β) := by gcongr; apply lemma14
    _ ≤ (Stab K' A').card := hStab

  let β' : ℝ := min (β/2 - 17/15 * (2 - β) * SG_eps₃ β) (β / 2 - 113 / 30 * β * SG_eps₃ β)

  have A'small : A'.card ≤ (p^(1 - β') : ℝ) :=
    calc
      (A'.card : ℝ) ≤ A.card := by gcongr
      _ ≤ 4 * n ^ (1/2 + 2 * ST_prime_field_eps β) := hA
      _ ≤ (SG_C₅ * (1 / 4)) * n ^ (1/2 + 2 * ST_prime_field_eps β) := by
        gcongr
        unfold SG_C₅
        norm_num
      _ ≤ n^(ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β) * n ^ (1/2 + 2 * ST_prime_field_eps β) := by
        gcongr
      _ = n^(1/2 + 8 * ST_prime_field_eps β + SG_eps₂ β + SG_eps β) := by
        rw [← rpow_add]
        ring_nf
        simp
      _ ≤ (p^(2 - β))^(1/2 + 8 * ST_prime_field_eps β + SG_eps₂ β + SG_eps β) := by
        gcongr
        exact lemma15 β h
      _ = p^(1 - (β/2 - 17/15 * (2 - β) * SG_eps₃ β)) := by
        rw [← rpow_mul]
        congr 1
        unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
        ring_nf
        simp
      _ ≤ p^(1 - β') := by
        unfold_let β'
        gcongr
        simp [instpprime.out.one_le]
        simp

  have A'large : A'.card ≥ (p^β' : ℝ) :=
    calc
    (A'.card : ℝ) ≥ (2 ^ 4)⁻¹ * (256 * n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β) : ℝ)⁻¹ * A.card := hAsz
    _ ≥ (2 ^ 4)⁻¹ * (256 * n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β) : ℝ)⁻¹ * n^(1/2 - 1/2 * SG_eps₃ β) := by
      gcongr
    _ = (2 ^ 12)⁻¹ * (n^(1/2 - 1/2 * SG_eps₃ β) / n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) := by
      ring_nf
    _ = (2 ^ 12)⁻¹ * n^(1/2 - 1/2 * SG_eps₃ β - (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) := by
      rw [← rpow_sub]
      simp
    _ ≥ (SG_C₅ * (1 / 4))⁻¹ * n^(1/2 - 1/2 * SG_eps₃ β - (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) := by
      gcongr
      unfold SG_C₅
      norm_num
    _ ≥ (n^(ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β) : ℝ)⁻¹ * n^(1/2 - 1/2 * SG_eps₃ β - (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) := by
      gcongr
      push_cast
      rw [inv_le_inv]
      exact nLarge
      apply rpow_pos_of_pos
      simp
      unfold SG_C₅
      norm_num
    _ = n^(1/2 - 1/2 * SG_eps₃ β - (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) / n^(ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β) := by
      ring
    _ = n^(1/2 - 1/2 * SG_eps₃ β - (8 * ST_prime_field_eps β + 2 * SG_eps₃ β) - (ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β)) := by
      rw [← rpow_sub]
      simp
    _ = n^(1/2 - 113/30 * SG_eps₃ β) := by
      congr 1
      unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
      ring_nf
    _ ≥ (p^β)^(1/2 - 113/30 * SG_eps₃ β) := by
      gcongr
      apply lemma16
    _ = p^(β / 2 - 113 / 30 * β * SG_eps₃ β) := by
      rw [← rpow_mul]
      ring_nf
      simp
    _ ≥ p^β' := by
      gcongr
      simp [instpprime.out.one_le]
      unfold_let β'
      simp
  have := Stab_small K' p A' _ (lemma12 β h) fourlt hStab' β' A'large A'small

  absurd this
  unfold_let K' β'
  simp only [not_le]
  apply final_theorem β h n p nhᵤ nLarge

  norm_num
  simp
  apply rpow_pos_of_pos
  simp
  · unfold SG_C₅
    simp at bne
    simp [bne]
    apply rpow_pos_of_pos
    simp

theorem ST_grid_aux₂ (β : ℝ) (h : 0 < β) (A B : Finset α) (L : Finset (Line α)) (n : ℕ+) (nhₗ : (p^β : ℝ) ≤ n)
  (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
  (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ)) (h₂ : L.card ≤ n)
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
    _ ≤ 4*n^(1/2 + 2*ST_prime_field_eps β) * n^(1 - SG_eps₃ β) +
        JSS'.card * ((4 * n^(1/2 + 2*ST_prime_field_eps β)) * (4 * n^(1/2 + 2*ST_prime_field_eps β))) := by
      gcongr
    _ = 4 * (n^(1/2 + 2*ST_prime_field_eps β) * n^(1 - SG_eps₃ β)) +
        16 * JSS'.card * (n^(1/2 + 2*ST_prime_field_eps β) * n^(1/2 + 2*ST_prime_field_eps β)) := by ring
    _ = 4 * (n^(1/2 + 2*ST_prime_field_eps β + (1 - SG_eps₃ β))) +
        16 * JSS'.card * n^(1/2 + 2*ST_prime_field_eps β + (1/2 + 2*ST_prime_field_eps β)) := by
      simp [←rpow_add]
    _ = 4 * (n^(3/2 + 2*ST_prime_field_eps β - SG_eps₃ β)) +
        16 * JSS'.card * n^(1 + 4*ST_prime_field_eps β) := by ring_nf
  have eq : 3/2 + 2*ST_prime_field_eps β - SG_eps₃ β = 3/2 - SG_eps₂ β - SG_eps β := by
    simp [ST_prime_field_eps, ST_prime_field_eps₂, ST_prime_field_eps₃, SG_eps, SG_eps₂]
    ring
  rw [eq] at this
  let JSS'' := JSS' \ {b₁, b₂}
  have := calc (((SG_C₄ - 4) / 16 - 2) * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β) : ℝ)
    _ = (SG_C₄ - 4) / 16 * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β) - 2 *
        n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β) := by ring
    _ ≤ (SG_C₄ - 4) / 16 * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β) - 2 * 1 := by
      gcongr
      apply one_le_rpow
      norm_cast
      simp
      apply lemma8
    _ = ((SG_C₄ - 4) * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β)) / 16 - 2 := by field_simp
    _ = ((SG_C₄ - 4) * (n^(3/2 - SG_eps₂ β - SG_eps β) / n ^ (1 + 4 * ST_prime_field_eps β))) / 16 - 2 := by
      congr
      rw [←rpow_sub]
      ring_nf
      simp
    _ = (SG_C₄ * n^(3/2 - SG_eps₂ β - SG_eps β) - 4 * n^(3/2 - SG_eps₂ β - SG_eps β)) / (16 * n^(1 + 4 * ST_prime_field_eps β)) - 2 := by
      field_simp
      ring_nf
    _ ≤ ((4 * n^(3/2 - SG_eps₂ β - SG_eps β) + 16 * JSS'.card * n^(1 + 4 * ST_prime_field_eps β)) -
        4 * n^(3/2 - SG_eps₂ β - SG_eps β)) / (16 * n^(1 + 4 * ST_prime_field_eps β)) - 2 := by
      gcongr
    _ = JSS'.card * ((16 * n^(1 + 4 * ST_prime_field_eps β)) / (16 * n^(1 + 4 * ST_prime_field_eps β))) - 2 := by
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
  suffices JSS''.card < (((SG_C₄ - 4) / 16 - 2) * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β) : ℝ) by
    linarith
  convert_to JSS''.card < (SG_C₅ * n^(1/2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β) : ℝ)
  · simp [SG_C₄]; left
    ring_nf
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
  (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
  (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ)) (h₂ : L.card ≤ n)
  (hC : ∀ l ∈ L, (n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card)
  :
  (Intersections (A ×ˢ B) L).card ≤ (SG_C₂ * n ^ (3/2 - SG_eps β) : ℝ) := by classical
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
    _ ≤ (4 * n^(1/2 + 2 * ST_prime_field_eps β))^2 + SG_C₃ * n ^ (3/2 - SG_eps β) := by
      simp only [sq]
      gcongr
    _ = 16 * n^(1 + 4 * ST_prime_field_eps β) + SG_C₃ * n ^ (3/2 - SG_eps β) := by
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
    _ = SG_C₂ * n ^ (3/2 - SG_eps β) := by simp [SG_C₂]; ring_nf

theorem ST_grid (β : ℝ) (h : 0 < β) (A B : Finset α) (L : Finset (Line α)) (n : ℕ+) (nhₗ : (p^β : ℝ) ≤ n)
  (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
  (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ)) (h₂ : L.card ≤ n) :
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
