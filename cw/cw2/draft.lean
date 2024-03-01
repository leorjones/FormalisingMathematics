/- ### Hello Steve -/

import Mathlib.Tactic

set_option autoImplicit false --stops me accidentally rewriting my variables
variable (G H : Type) {X : Type} [Group G] [MulAction G X] (x y z : X)
variable(H : Subgroup G)
variable {a b : G}


open MulAction

/- ### Orbit Stabiliser Theorem-/

/--The map from the quotient group of the stabilizer to the set X, for an element x-/
-- aka φ, before the restriction to its image
def ψ (g : G ⧸ stabilizer G x) : X :=
  Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (QuotientGroup.leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]


--showing that its image is the orbit
lemma ψ_orbit (g) : ψ G x g ∈ orbit G x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩


/--The restricted map from the quotient of the stabilizer to the orbit of the element x-/
--supplying the output and a proof that this is in our range
def φ : G ⧸ stabilizer G x → (orbit G x) := fun g => ⟨ψ G x g, ψ_orbit G x g⟩


--a lemma so that we can rewrite our range elements φ G x, directly as the group action g • x
lemma φ_mk' (g : G) : φ G x (QuotientGroup.mk g) = ⟨g • x, mem_orbit x g⟩ := rfl

set_option pp.proofs.withType false --so I can read

--lemma following directly from the real life proof, a(x) = b(x) => a⁻¹b ∈ Stab(x)
lemma eq_imp_stab :(φ G x a = φ G x b) → (a⁻¹*b ∈ stabilizer G x):= by
  intro p
  repeat rw [φ_mk'] at p
  apply Subtype.val_inj.2 at p
  dsimp at p
  have  h: (a⁻¹ * b) • x = a⁻¹ • (b • x) := by rw [mul_smul a⁻¹ b x]
  rw [← p, smul_smul a⁻¹ a x, inv_mul_self, one_smul] at h
  exact h

/--Proof of the injectivity of φ-/
theorem injective_φ : Function.Injective (φ G x) :=  by
  simp [Function.Injective]
  intros p q h
  obtain ⟨a, ha⟩ := Quot.exists_rep p
  obtain ⟨b, hb⟩ := Quot.exists_rep q
  have ha: ↑a = p := by exact ha
  have hb: ↑b = q := by exact hb
  have h2: φ G x ↑a = φ G x ↑b := by
    rw [←ha, ←hb] at h
    exact h
  apply eq_imp_stab at h2
  rw [←QuotientGroup.eq'] at h2
  rw [←ha, ←hb]
  exact h2


--like before, so we can rewrite an orbit element directly
lemma orbit_def : y ∈ orbit G x → ∃ g : G, y = g • x := by
  simp[orbit]
  intros a h
  use a
  simp [h]


/--Proof of the surjectivity of φ-/
theorem surjective_φ: Function.Surjective (φ G x) := by
  simp[Function.Surjective]
  intros y h1
  have h2 : y ∈ orbit G x → ∃ g : G, y = g • x := by apply orbit_def
  apply h2 at h1
  cases' h1 with a h3
  use a
  ext
  simp
  rw [h3, φ_mk']


/--Orbit Stabliser Theorem : proof of the bijectivity of φ-/
theorem orbit_stab_bij : Function.Bijective (φ G x) := by
  simp[Function.Bijective, injective_φ, surjective_φ]


/--Orbit Stabiliser Theorem : the equivalence between the quotient of the stabiliser and the orbits -/
noncomputable def orbit_stab_equiv : (G ⧸ stabilizer G x ≃ orbit G x) :=  by
  apply Equiv.ofBijective
  simp [Function.Bijective]
  constructor
  apply injective_φ
  apply surjective_φ


/--| X ⧸ G | : The set of orbits of X -/
local notation "Φ" => Quotient <| orbitRel G X

/- # Note #
From now on we are working with finite G and X, in order to use proofs about the cardinalities
-/

--some more variables we need, and casting all our groups/sets to Fintypes
variable (N : Subgroup G) [Subgroup.Normal N] (X)
variable (α β : Type) [Fintype α] [Fintype β] --only needed for bijection_imp_eq_card
variable[Fintype G] [Fintype X] [MulAction G X] [Fintype Φ]
variable[Fintype (G ⧸ stabilizer G x)] [∀ x : X, Fintype <| stabilizer G x] [∀ x : X, Fintype (orbit G x)] [∀ g : G, Fintype <| fixedBy X g]
variable {G} (g)

--a lemma because lean doesn't like when you divide with natural numbers
--ideally, I would rewrite this proof without the use of / altogether
lemma cant_use_ℕ  (c d : ℕ) : (d *  c / c = d) := by sorry


/--Proof that | G ⧸ N | = | G | / | N | . Follows from Lagrange's Theorem-/
theorem quotient_order [Fintype G] [Fintype N] [Fintype (G ⧸ N)][DecidablePred fun a => a ∈ N]: Fintype.card G / Fintype.card N = Fintype.card (G ⧸ N) := by
simp [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
simp [cant_use_ℕ]
-- I have no idea why rfl does not work here :(
sorry

--a proof that if we have a bijection then the cardinalities of the (finite) domain and range are equal
lemma bijection_imp_eq_card (f : α → β) (hf : Function.Bijective f) [Fintype (Set.range f)]: Fintype.card α = Fintype.card β := by
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



--casting our function φ so that Fintype likes it
lemma fin_φ [Fintype G] : Fintype (Set.range (φ G x)) := by exact Fintype.ofFinite (Set.range (φ G x))



/--Orbit Stabiliser Theorem : a proof that | G | ⧸ | Stab(x) | = | G(x) | -/
theorem orbit_eq_card : Fintype.card (G) / Fintype.card (stabilizer G x) = Fintype.card (orbit G x) := by
  have h1 : Function.Bijective (φ G x) := by apply orbit_stab_bij
  have h2 : DecidablePred fun a => (a ∈ stabilizer G x) :=  by exact g
  have h3: Fintype.card (G) / Fintype.card (stabilizer G x) = Fintype.card (G ⧸ stabilizer G x) := by apply quotient_order (stabilizer G x)
  rw [h3]
  let _ : Fintype (Set.range (φ G x)) := fin_φ _ _
  apply bijection_imp_eq_card (G ⧸ stabilizer G x) (orbit G x) (φ G x) h1



open BigOperators -- to use ∑

/-# Burnsides Lemma -/


--these are some lemmas which rearrange the orbit stabiliser theorem into Burnsides Lemma
--rearranging equations with natural numbers is very difficult
lemma fix_stab_equiv : ∑ g : G, Fintype.card (fixedBy X g) = ∑ x : X, Fintype.card (stabilizer G x) := by sorry


lemma sum_orbits [Fintype Φ] :(Fintype.card Φ) = ∑ x : X, 1 / (Fintype.card (orbit G x)) := by sorry


--this one follows pretty directly from the orbit stabiliser theorem
lemma orbit_stab [∀ x : X, Fintype <| stabilizer G x]
: ∑ x : X, 1 / Fintype.card (orbit G x) =  1 / (Fintype.card (G) /(∑ x : X ,Fintype.card (stabilizer G x))):= by sorry


--again, a lemma because I am dividing natural numbers, I should avoid using it or cast the cardinalities as reals/rationals
lemma cant_div_ℕ  (d f : ℕ ) : 1 / (d / f) = f / d := by sorry

/--Burnside's Lemma : a corollary of the Orbit Stabliser Theorem-/
theorem burnside_lemma [Fintype Φ] : (Fintype.card Φ) =  (∑ g : G, Fintype.card (fixedBy X g)) / Fintype.card G := by
 rw [sum_orbits, orbit_stab]
 simp [fix_stab_equiv, cant_div_ℕ]
