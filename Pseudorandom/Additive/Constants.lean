import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base


noncomputable def full_C₂ (β : ℝ) : ℕ := 374 ^ ⌈Real.logb (3/2 : ℝ) (1 / β)⌉₊

noncomputable def full_C (β : ℝ) : ℕ := (full_C₂ β) * 9
