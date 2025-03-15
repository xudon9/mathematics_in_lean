import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h (x y : ℝ): max x y ≤ max y x := by
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    -- show min (min a b) c ≤ a
    apply le_trans
    repeat
      apply min_le_left
    -- show min (min a b) c ≤ min b c
    apply le_min
    apply le_trans
    apply min_le_left
    apply min_le_right
    apply min_le_right
  · apply le_min
    -- show min a (min b c) ≤ min a b
    apply le_min
    apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
    -- show min a (min b c) ≤ c
    apply le_trans
    apply min_le_right
    apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · nth_rw 2 [← add_neg_cancel_right a c, ← add_neg_cancel_right b c]
    apply add_neg_le_iff_le_add.mp
    apply aux

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  rw [sub_eq_add_neg]
  apply add_neg_le_iff_le_add.mpr
  nth_rw 1 [←  sub_add_cancel a b]
  apply abs_add
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  · apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  · apply dvd_mul_left
  · apply dvd_mul_of_dvd_right
    assumption
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  have h (a b : ℕ): Nat.gcd a b ∣ Nat.gcd b a := by
    apply dvd_gcd
    exact gcd_dvd_right a b
    exact gcd_dvd_left a b
  apply dvd_antisymm
  apply h
  apply h
end
