/- ### Hello Steve -/

import Mathlib.Tactic


variable (G H : Type)[Group G][Group H]
variable {x : G}
variable (G * X → X)

/-# Cosets-/

def lcoset.one_mem : (1 : G) ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h} := by sorry

def lcoset.inv_mem (h : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h}) : (y⁻¹ ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h}) := by
  sorry

def lcoset.mul_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h}) (hz : z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h}) :
(y * z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h}) := by sorry

def lcoset (H : Subgroup G)  (x : G) : Subgroup G
  where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h}
  one_mem' := lcoset.one_mem
  inv_mem' := lcoset.inv_mem
  mul_mem' := lcoset.mul_mem

/-# Stabiliser -/

def stab () : (S : Subgroup G) := by sorry

def index : Prop := 1=1

def dis_union (X : Set) : (X dis union) :=by sorry

/-# Final Theorem-/
theorem orbit_stab () : (|X| = ∑ G.orbit(x.i)) (|X|= ∑[G : x.i.stab]) := by sorry
