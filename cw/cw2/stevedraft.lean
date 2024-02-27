import Mathlib.Tactic

variable (G : Type)[Group G](N : Subgroup G)[Subgroup.Normal N](x : X)
variable (α β : Type*)[Fintype α][Fintype β]
theorem quotient_order [Fintype G][Fintype N][Fintype (G ⧸ N)]: Fintype.card G / Fintype.card N = Fintype.card (G ⧸ N) := by
sorry

lemma bijection_imp_eq_card (f : α → β)(hf : Function.Bijective f)[Fintype (Set.range f)]:
Fintype.card α = Fintype.card β := by
have hf_copy : Function.Bijective f := by exact hf
rw [Function.Bijective] at hf
cases' hf with hInj hSur
have h_f_imag_eq_β : Set.range f = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro B
  exact hSur B
have h_f_imag_card : Fintype.card (Set.range f) = Fintype.card α := by exact Set.card_range_of_injective sorry
rw [← h_f_imag_card]
exact (set_fintype_card_eq_univ_iff (Set.range f)).mpr h_f_imag_eq_β
/- i found that from doing exact? -/
