import Mathlib.Tactic

variable {α : Type*} {s t : Finset α}[DecidableEq α]

lemma card_of_disjoint_union (h : Disjoint s t) : Finset.card (s ∪ t) = Finset.card s + Finset.card t := by
exact Finset.card_union_eq h

variable {S : Finset (Finset α)}

open BigOperators

theorem finite_union_disjoint_card : (∀ (n : ℕ), Finset.card S = n) → (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) → (∑ s in S, Finset.card s = Finset.card (Finset.sup S id)) := by
intro hn hdisjoint
simp [Finset.sup_set_eq_biUnion S id]
simp [Finset.sup_def]
sorry

apply [Finset.card_biUnion] at hdisjoint
