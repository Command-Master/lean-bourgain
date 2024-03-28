import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

def SG_C₄ : NNReal := 1
noncomputable def SG_C₃ : NNReal := 4 * NNReal.sqrt (SG_C₄ + 1)
noncomputable def SG_C₂ : NNReal := SG_C₃ + 16
noncomputable def SG_V : NNReal := ((SG_C₄ - 4) / 16 - 2)
noncomputable def SG_C :  NNReal := SG_C₂ + 1
noncomputable def ST_C₇ : NNReal := SG_C
noncomputable def ST_C₆ : NNReal := ST_C₇ + 2
noncomputable def ST_C₅ : NNReal := (ST_C₆ + 73 : NNReal)^(1/4 : ℝ)
noncomputable def ST_C₄ : NNReal := NNReal.sqrt (2*(ST_C₅ + NNReal.sqrt 2 / 4))
noncomputable def ST_C₃ : NNReal := ST_C₄ + 1
noncomputable def ST_C₂ : NNReal := NNReal.sqrt (2*(ST_C₃ + NNReal.sqrt 2 / 4))
noncomputable def ST_C  : NNReal := ST_C₂ + 1
def SG_eps₃ (α : ℝ) : ℝ := α^10
noncomputable def SG_eps₂ (α : ℝ) : ℝ := 2/3 * (SG_eps₃ α)
noncomputable def SG_eps (α : ℝ) : ℝ := 13/30 * (SG_eps₂ α)
noncomputable def ST_prime_field_eps₄ (α : ℝ) : ℝ := 12/13 * (SG_eps α)
noncomputable def ST_prime_field_eps₃ (α : ℝ) : ℝ := (ST_prime_field_eps₄ α) / 4
noncomputable def ST_prime_field_eps₂ (α : ℝ) : ℝ := (ST_prime_field_eps₃ α) / 3
noncomputable def ST_prime_field_eps (α : ℝ) : ℝ := (ST_prime_field_eps₂ α) / 3
-- noncomputable def SG_epsᵥ (α : ℝ) : ℝ := SG_eps₂ α + SG_eps α + 4 * ST_prime_field_eps₂ α

lemma pos_ST_prime_field_eps₂ (α : ℝ) (h : 0 < α) : 0 < ST_prime_field_eps₂ α := sorry

lemma one_le_SG_C₃ : 1 ≤ SG_C₃ := calc
  1 = NNReal.sqrt 1 := by simp
  _ ≤ NNReal.sqrt (SG_C₄ + 1) := by simp
  _ ≤ 4 * NNReal.sqrt (SG_C₄ + 1) := by simp
  _ = SG_C₃ := rfl

lemma SG_C₃_pos : 0 < SG_C₃ := calc
  0 < 1 := zero_lt_one
  1 ≤ SG_C₃ := one_le_SG_C₃

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


lemma lemma1 (β : ℝ) (h : 0 < β) :
  1 / 2 + 2 * ST_prime_field_eps₂ β ≤ 1 - 4 * ST_prime_field_eps₃ β := sorry

lemma lemma2 (β : ℝ) (h : 0 < β) :
  4 * ST_prime_field_eps₃ β ≤ 1 := sorry

lemma lemma3 (β : ℝ) (h : 0 < β) :
  ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β ≤ 1 - 4 * ST_prime_field_eps₃ β := sorry

lemma lemma4 (β : ℝ) (h : 0 < β) :
  1 ≤ 3 / 2 - 13 / 12 * ST_prime_field_eps₄ β := sorry

lemma lemma5 (β : ℝ) (h : 0 < β) :
  1 + (2⁻¹ - SG_eps β) ≠ 0 := sorry

lemma lemma6 (β : ℝ) (h : 0 < β) :
  1 + 4 * ST_prime_field_eps₂ β ≤ 3 / 2 - SG_eps β := sorry

lemma lemma7 (β : ℝ) (h : 0 < β) :
  1 / 2 + SG_eps β ≤ 1 + (-(SG_eps β * 2) - ST_prime_field_eps₂ β * 4) := sorry

lemma lemma8 (β : ℝ) (h : 0 < β) :
  0 ≤ 1 / 2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps₂ β := sorry
