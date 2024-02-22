import Mathlib.Tactic





namespace set

lemma countable_coe_iff {s : set α} : countable s ↔ s.countable :=
encodable.nonempty_encodable.symm

variable (X: Type α)(S: Set X)(f: function)
example :  countable S ↔ ∃ f : S → ℕ, injective f := by
  sorry

theorem set.countable_coe_iff {α : Type u} {s : set α} :
countable ↥s ↔ s.countable
