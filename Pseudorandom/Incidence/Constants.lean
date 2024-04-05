import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Pseudorandom.Additive.Constants

def SG_C₅ : NNReal := 2^49
noncomputable def SG_C₄ : NNReal := 4+16*(SG_C₅+2)
noncomputable def SG_C₃ : NNReal := 4 * NNReal.sqrt (SG_C₄ + 1)
noncomputable def SG_C₂ : NNReal := SG_C₃ + 16
-- noncomputable def SG_V : NNReal := ((SG_C₄ - 4) / 16 - 2)
noncomputable def SG_C :  NNReal := SG_C₂ + 1
noncomputable def ST_C₇ : NNReal := SG_C
noncomputable def ST_C₆ : NNReal := ST_C₇ + 2
noncomputable def ST_C₅ : NNReal := (ST_C₆ + 73 : NNReal)^(1/4 : ℝ)
noncomputable def ST_C₄ : NNReal := NNReal.sqrt (2*(ST_C₅ + NNReal.sqrt 2 / 4))
noncomputable def ST_C₃ : NNReal := ST_C₄ + 1
noncomputable def ST_C₂ : NNReal := NNReal.sqrt (2*(ST_C₃ + NNReal.sqrt 2 / 4))
noncomputable def ST_C  : NNReal := ST_C₂ + 1
noncomputable def SG_eps₃ (α : ℝ) : ℝ := min (min (11/439) (15 / 136 * α))
    ((α / 4) / (full_C (α / 4) * 9212 / 45))
noncomputable def SG_eps₂ (α : ℝ) : ℝ := 2/3 * (SG_eps₃ α)
noncomputable def SG_eps (α : ℝ) : ℝ := 13/30 * (SG_eps₂ α)
noncomputable def ST_prime_field_eps₄ (α : ℝ) : ℝ := 12/13 * (SG_eps α)
noncomputable def ST_prime_field_eps₃ (α : ℝ) : ℝ := (ST_prime_field_eps₄ α) / 4
noncomputable def ST_prime_field_eps₂ (α : ℝ) : ℝ := (ST_prime_field_eps₃ α) / 3
noncomputable def ST_prime_field_eps (α : ℝ) : ℝ := (ST_prime_field_eps₂ α) / 3

lemma ntlSGeps (β : ℝ) : SG_eps₃ β < 45/1756 :=
  calc SG_eps₃ β
    _ ≤ 11/439 := by unfold SG_eps₃; simp
    _ < 45/1756 := by norm_num

lemma ntlSGeps' (β : ℝ) : SG_eps₃ β ≤ 15 / 136 * β := by
  unfold SG_eps₃
  simp

theorem full_C_neq_zero (x : ℝ) : full_C x ≠ 0 := by
  unfold full_C full_C₂
  simp

lemma pos_SGeps₃ (β : ℝ) (h : 0 < β) :
    0 < SG_eps₃ β := by
  unfold SG_eps₃
  have := full_C_neq_zero (β / 4)
  field_simp

lemma pos_ST_prime_field_eps₂ (α : ℝ) (h : 0 < α) : 0 < ST_prime_field_eps₂ α := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  simp [pos_SGeps₃ α h]

lemma one_le_SG_C₃ : 1 ≤ SG_C₃ := calc
  1 = NNReal.sqrt 1 := by simp
  _ ≤ NNReal.sqrt (SG_C₄ + 1) := by simp
  _ ≤ 4 * NNReal.sqrt (SG_C₄ + 1) := by simp
  _ = SG_C₃ := rfl

lemma SG_C₃_pos : 0 < SG_C₃ := calc
  0 < 1 := zero_lt_one
  _ ≤ SG_C₃ := one_le_SG_C₃

lemma one_le_ST_C₅ : 1 ≤ ST_C₅ := calc
  1 ≤ 1^(1/4 : ℝ) := by simp
  _ ≤ (ST_C₆ + 73 : NNReal)^(1/4 : ℝ) := by
    gcongr
    have : ST_C₆ + 73 = 1 + (ST_C₆ + 72) := by ring
    rw [this]
    simp
  _ = ST_C₅ := rfl

lemma ST_C₅_pos : 0 < ST_C₅ := calc
  0 < 1 := zero_lt_one
  _ ≤ ST_C₅ := one_le_ST_C₅

lemma lemma1 (β : ℝ) :
  1 / 2 + 2 * ST_prime_field_eps₂ β ≤ 1 - 4 * ST_prime_field_eps₃ β := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma2 (β : ℝ) :
  4 * ST_prime_field_eps₃ β ≤ 1 := by
  unfold ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma3 (β : ℝ) :
  ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β ≤ 1 - 4 * ST_prime_field_eps₃ β := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma4 (β : ℝ) :
  1 ≤ 3 / 2 - 13 / 12 * ST_prime_field_eps₄ β := by
  unfold ST_prime_field_eps₄ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma5 (β : ℝ) :
  1 + (2⁻¹ - SG_eps β) ≠ 0 := by
  apply ne_of_gt
  unfold SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma6 (β : ℝ) :
  1 + 4 * ST_prime_field_eps₂ β ≤ 3 / 2 - SG_eps β := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma7 (β : ℝ) :
  1 / 2 + SG_eps β ≤ 1 + (-(SG_eps β * 2) - ST_prime_field_eps₂ β * 4) := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma8 (β : ℝ) :
  0 ≤ 1 / 2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma9 (β : ℝ) (h : 0 < β) :
  0 ≤ ST_prime_field_eps₂ β := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := pos_SGeps₃ β h
  linarith

lemma lemma10 (β : ℝ) (h : 0 < β) :
  0 ≤ SG_eps₃ β := by
  exact le_of_lt <| pos_SGeps₃ β h

lemma lemma11 (β : ℝ) (h : 0 < β) :
  β / 4 < β / 2 - 439 / 45 * β * SG_eps₃ β := by
  have := ntlSGeps β
  convert_to β * (1/4) < β * (1/2 - 439/45 * SG_eps₃ β)
  ring_nf; ring_nf
  apply mul_lt_mul_of_pos_left
  linarith
  exact h

lemma lemma12 (β : ℝ) (h : 0 < β) :
  0 < β / 2 - 439 / 45 * β * SG_eps₃ β := calc
  0 < β / 4 := by simp [h]
  _ < β / 2 - 439 / 45 * β * SG_eps₃ β := lemma11 β h

lemma lemma13 (β : ℝ) :
  ST_prime_field_eps₂ β * 6 + SG_eps₂ β + SG_eps β ≤ 1 / 2 - 439 / 45 * SG_eps₃ β := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma14 (β : ℝ) :
  0 ≤ 1 / 2 - 439 / 45 * SG_eps₃ β := by
  have := ntlSGeps β
  linarith

lemma lemma15 (β : ℝ) (h : 0 < β) :
  0 ≤ 1 / 2 + 8 * ST_prime_field_eps₂ β + SG_eps₂ β + SG_eps β := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
  have := pos_SGeps₃ β h
  linarith

lemma lemma16 (β : ℝ) :
  0 ≤ 1/2 - 113/30 * SG_eps₃ β := by
  have := ntlSGeps β
  linarith

theorem final_theorem (β : ℝ) (h : 0 < β) (n : ℕ+) (p : ℕ) [instpprime : Fact p.Prime]
  (h₁ : n ≤ (p ^ (2 - β) : ℝ)) (h₂ : SG_C₅ * (1/4) ≤ n ^ (ST_prime_field_eps₂ β * 6 + SG_eps₂ β + SG_eps β)):
  (2 ^ 110 * (256 * n ^ (8 * ST_prime_field_eps₂ β + 2 * SG_eps₃ β)) ^ 42) ^
    full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) <
  (p ^ min (β / 2 - 17 / 15 * (2 - β) * SG_eps₃ β) (β / 2 - 113 / 30 * β * SG_eps₃ β) : ℝ) / 2 :=
  calc
    ((2 ^ 110 * (256 * n ^ (8 * ST_prime_field_eps₂ β + 2 * SG_eps₃ β)) ^ 42) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) : ℝ) =
        (2 ^ 446 * (n ^ (8 * ST_prime_field_eps₂ β + 2 * SG_eps₃ β)) ^ 42) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) := by
      ring_nf
    _ = (2 ^ 446 * n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) := by
      congr 2
      rw [← Real.rpow_mul_natCast]
      congr 1
      unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
      ring_nf
      simp
    _ = (2 ^ 447 * n ^ (1372 / 15 * SG_eps₃ β) / 2) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) := by
      ring_nf
    _ = (2 ^ 447 * n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 ^ full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) := by
      simp
    _ ≤ (2 ^ 447 * n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 := by
      gcongr
      apply le_self_pow
      norm_num
      apply full_C_neq_zero
    _ ≤ ((SG_C₅ * (1/4))^10 * n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 := by
      gcongr
      unfold SG_C₅
      norm_num
    _ ≤ ((n ^ (ST_prime_field_eps₂ β * 6 + SG_eps₂ β + SG_eps β))^10 * n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 := by
      gcongr
      exact h₂
    _ = (n ^ (4606 / 45 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 := by
      rw [← Real.rpow_mul_natCast, ← Real.rpow_add]
      unfold ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
      ring_nf
      simp
      simp
    _ ≤ (n ^ (4606 / 45 * SG_eps₃ β)) ^
        full_C (β / 4) / 2 := by
      unfold full_C full_C₂
      gcongr
      apply Real.one_le_rpow
      norm_cast; simp
      simp [lemma10 β h]
      norm_num
      norm_num
      rw [one_div, inv_pos]
      exact lemma12 β h
      exact le_of_lt <| lemma11 β h
    _ ≤ ((p ^ (2 - β)) ^ (4606 / 45 * SG_eps₃ β)) ^
        full_C (β / 4) / 2 := by
      gcongr
      simp [lemma10 β h]
    _ ≤ ((p ^ 2) ^ (4606 / 45 * SG_eps₃ β)) ^
        full_C (β / 4) / 2 := by
      conv =>
        rhs
        lhs
        lhs
        rw [← Real.rpow_nat_cast]
      gcongr
      simp [lemma10 β h]
      simp [instpprime.out.one_le]
      simp
      exact le_of_lt h
    _ = p^(full_C (β / 4) * 9212 / 45 * SG_eps₃ β) / 2 := by
      rw [← Real.rpow_natCast_mul, ← Real.rpow_mul_natCast]
      ring_nf
      simp
      simp
    _ ≤ p^(full_C (β / 4) * 9212 / 45 * (β * 45 / (4 * (full_C (β / 4) * 9212)))) / 2 := by
      gcongr
      simp [instpprime.out.one_le]
      unfold SG_eps₃
      simp
      right
      ring_nf
      rfl
    _ = p^(β / 4) / 2 := by
      congr 2
      unfold full_C full_C₂
      field_simp
      ring_nf
    _ < (p ^ min (β / 2 - 17 / 15 * (2 - β) * SG_eps₃ β) (β / 2 - 113 / 30 * β * SG_eps₃ β) : ℝ) / 2 := by
      gcongr
      apply Real.rpow_lt_rpow_of_exponent_lt
      have := instpprime.out.two_le
      norm_cast
      simp only [lt_min_iff]
      constructor
      · suffices 17/15 * (2 - β) * SG_eps₃ β < β / 4 by linarith
        calc
          17/15 * (2 - β) * SG_eps₃ β < 17/15 * (2 - 0) * SG_eps₃ β := by gcongr; exact pos_SGeps₃ β h
          _ = 34 / 15 * SG_eps₃ β := by ring_nf
          _ ≤ 34 / 15 * (15 / 136 * β) := by gcongr; exact ntlSGeps' β
          _ = β / 4 := by ring
      · have := lemma11 β h
        apply this.trans_le
        gcongr _ - ?_ * _ * _
        exact lemma10 β h
        norm_num
