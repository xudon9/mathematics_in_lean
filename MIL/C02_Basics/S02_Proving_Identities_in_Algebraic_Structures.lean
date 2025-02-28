import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  -- Excercise
  rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
  -- Excercise
  calc
    b = b + a + -a := by nth_rw 1 [← add_neg_cancel_right b a]
    _ = a + b + -a := by rw [add_comm a b]
    _ = a + c + -a := by rw [h]
    _ = a + -a + c := by rw [add_assoc, add_assoc, add_comm c (-a)]
    _ = 0 + c := by rw [add_right_neg]
    _ = c := by rw [zero_add]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  -- Exercise
  rw [add_comm a b, add_comm c b] at h
  exact add_left_cancel h

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  -- Excercise
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  -- Excercise
  rw [← add_neg_cancel a] at h
  rw [add_left_cancel h]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  -- sorry
  rw [← neg_add_cancel b] at h
  rw [add_right_cancel h]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  -- sorry
  apply neg_eq_of_add_eq_zero
  apply neg_add_cancel

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  -- sorry
  rw [sub_eq_add_neg, add_neg_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  -- sorry
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

lemma left_cancel {a x y : G} (h: a * x = a * y) : x = y := by
  have m : a⁻¹ * a * x =  a⁻¹ * a * y := by
    rw [mul_assoc a⁻¹ a x, mul_assoc a⁻¹ a y, h]
  rw [inv_mul_cancel, one_mul, one_mul] at m
  exact m

theorem mul_one (a : G) : a * 1 = a := by
  have h : a⁻¹ * (a * 1) = a⁻¹ * a :=
    calc
      a⁻¹ * (a * 1) = (a⁻¹ * a) * 1 := by rw [mul_assoc]
      _ = 1 * 1           := by rw [inv_mul_cancel]
      _ = 1               := by rw [one_mul]
      _ = a⁻¹ * a         := by rw [inv_mul_cancel]
  rw [left_cancel h]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : a⁻¹ * (a * a⁻¹) = a⁻¹ * 1  := by
    rw [mul_one, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [left_cancel h]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc b, mul_inv_cancel, one_mul, mul_inv_cancel]
  rw [← mul_inv_cancel (a * b)] at h
  rw [left_cancel h]

end MyGroup

end
