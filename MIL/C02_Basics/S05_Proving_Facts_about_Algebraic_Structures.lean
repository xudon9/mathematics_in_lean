import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  sorry

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry

example : x ⊔ y = y ⊔ x := by
  sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    apply le_refl
    apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    apply le_refl
    apply inf_le_left
  · apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  calc
    a ⊔ b ⊓ c = (a ⊔ a ⊓ c) ⊔ (b ⊓ c) := by
      nth_rw 1 [← absorb2 a c]
    _ = a ⊔ ((a ⊓ c) ⊔ (b ⊓ c)) := by
      rw [sup_assoc]
    _ = a ⊔ ((a ⊔ b) ⊓ c) := by
      rw [inf_comm a c, inf_comm b c, inf_comm (a ⊔ b) c, ← h ]
    _ = ((a ⊔ b) ⊓ a) ⊔ ((a ⊔ b) ⊓ c) := by
      rw [inf_comm (a ⊔ b) a,  absorb1]
    _ = (a ⊔ b) ⊓ (a ⊔ c) := by
      rw [← h]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c :=
  calc
    a ⊓ (b ⊔ c) = a ⊓ (c ⊔ b) := by
      rw [sup_comm b c]
    _ = a ⊓ (c ⊔ a)  ⊓  (c ⊔ b) := by
      nth_rw 1 [← absorb1 a c, sup_comm a c]
    _ = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) := by
      rw [inf_assoc]
    _ = a ⊓ (c ⊔ a ⊓ b) := by
      rw [← h]
    _ = a ⊓ (a ⊓ b ⊔ c) := by
      rw [sup_comm c (a ⊓ b)]
    _ = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by
      nth_rw 1 [← absorb2 a b, sup_comm a]
    _ = a ⊓ b ⊔ a ⊓ c := by
      rw [← h]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← neg_add_cancel a, sub_eq_add_neg, add_comm b]
  apply add_le_add_left
  apply h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← zero_add a, add_comm, ← add_neg_cancel_right b a,
    add_comm b a, add_assoc, ← sub_eq_add_neg]
  apply add_le_add_left
  apply h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  /- Essentially prove a*c + 0 ≤ a*c + (b-a)*c -/
  rw [← zero_add (a * c), add_comm, ← add_neg_cancel_right b a,
    add_comm b a, add_assoc, ← sub_eq_add_neg, add_mul]
  apply add_le_add_left
  apply mul_nonneg
  · /- To prove 0 ≤ b - a, the same as Example above -/
    rw [← neg_add_cancel a, sub_eq_add_neg, add_comm b]
    apply add_le_add_left
    apply h
  · apply h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y + dist x y := by
    nth_rw 2 [dist_comm]
    apply le_trans (b := dist x x)
    · rw [dist_self]
    · apply dist_triangle
  linarith

end

