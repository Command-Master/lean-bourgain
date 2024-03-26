import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base


noncomputable def full_C₂ (β : ℝ) : ℕ := 4374 ^ ⌈Real.logb (3/2 : ℝ) (1 / β)⌉₊
