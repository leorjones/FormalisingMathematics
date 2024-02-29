/- ### Hello Steve -/

import Mathlib.Tactic

set_option autoImplicit false
variable (G H : Type) {X : Type} [Group G][MulAction G X] (x y z : X)
variable(H : Subgroup G)
variable {g : G}
/-variable {a b : G⧸ MulAction.stabilizer G x}-/
variable {a b : G}



open MulAction


def φ (g : G ⧸ stabilizer G x) : X :=
Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (QuotientGroup.leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]

theorem φ_mk (g : G) : φ G x (QuotientGroup.mk g) = g • x :=
  rfl


lemma idyay : 1 = 1 := by rfl

/- ## Part 1-/

-- lemma hi :(φ G x a = φ G x b) → (a⁻¹*b ∈ stabilizer G x):= by
-- intro p
-- repeat rw [φ_mk] at p
-- have  h: (a⁻¹ * b) • x = a⁻¹  • (b • x) := by rw [mul_smul a⁻¹ b x]
-- rw [← p, smul_smul a⁻¹ a x, inv_mul_self, one_smul] at h
-- exact h

-- example :  a • (b • x)=  (a * b) • x := by exact smul_smul a b x


-- theorem injective_φ : Function.Injective (φ G x) :=  by
--   simp [Function.Injective]
--   intros p q r
--   obtain ⟨a, ha⟩ := Quot.exists_rep p
--   obtain ⟨b, hb⟩ := Quot.exists_rep q
--   have ha: ↑a = p := by exact ha
--   have hb: ↑b = q := by exact hb
--   have r2: φ G x ↑a = φ G x ↑b := by
--     rw [←ha, ←hb] at r
--     exact r
--   apply hi at r2
--   rw [←QuotientGroup.eq'] at r2
--   rw [←ha, ←hb]
--   exact r2


example (N : Subgroup G)[Subgroup.Normal N](n : G ⧸ N) := by exact X


---lemma range_φ : (φ G x).range = orbit G x := by sorry

theorem ofQuotientStabilizer_mem_orbit2 (g) : φ G x g ∈ orbit G x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩



def f : G ⧸ stabilizer G x → (orbit G x):= fun g => ⟨φ G x g, ofQuotientStabilizer_mem_orbit2 G x g⟩

theorem f_mk (g : G) : f G x (QuotientGroup.mk g) = g • x :=
  rfl

variable {G} (g)
lemma f_mk' (g:G) : f G x (QuotientGroup.mk g) = ⟨g • x, mem_orbit x g⟩ := rfl

set_option pp.proofs.withType false
lemma hi2 :(f G x a = f G x b) → (a⁻¹*b ∈ stabilizer G x):= by
intro p
repeat rw [f_mk'] at p
apply Subtype.val_inj.2 at p
dsimp at p
have  h: (a⁻¹ * b) • x = a⁻¹  • (b • x) := by rw [mul_smul a⁻¹ b x]
rw [← p, smul_smul a⁻¹ a x, inv_mul_self, one_smul] at h
exact h

theorem injective_f : Function.Injective (f G x) :=  by
  simp [Function.Injective]
  intros p q r
  obtain ⟨a, ha⟩ := Quot.exists_rep p
  obtain ⟨b, hb⟩ := Quot.exists_rep q
  have ha: ↑a = p := by exact ha
  have hb: ↑b = q := by exact hb
  have r2: f G x ↑a = f G x ↑b := by
    rw [←ha, ←hb] at r
    exact r
  apply hi2 at r2
  rw [←QuotientGroup.eq'] at r2
  rw [←ha, ←hb]
  exact r2


variable(p : X)
lemma oks : p ∈ orbit G x → ∃ g : G, p = g • x := by apply?

lemma surjective_φ: Function.Surjective (f G x) := by
simp[Function.Surjective]
intros p q
have h : p ∈ orbit G x → ∃ g : G, p = g • x := by apply oks
apply h at q
cases' q with blob tob
use blob
ext
simp
rw [tob, f_mk]


theorem orbit_bij : Function.Bijective (f G x) := by
  simp[Function.Bijective, injective_f, surjective_φ]

noncomputable def orbit_stab_bij : ( G ⧸ stabilizer G x ≃ orbit G x) :=  by
apply Equiv.ofBijective
simp [Function.Bijective]
constructor
apply injective_f
apply surjective_φ



/- # Part 2-/

variable (N : Subgroup G)[Subgroup.Normal N](x : X)
variable (α β : Type)[Fintype α][Fintype β]
theorem quotient_order [Fintype G][Fintype N][Fintype (G ⧸ N)]: Fintype.card G / Fintype.card N = Fintype.card (G ⧸ N) := by
sorry

lemma bijection_imp_eq_card (f : α → β)(hf : Function.Bijective f) [Fintype (Set.range f)]:
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

lemma help [Fintype G][Fintype N][Fintype (G ⧸ N)][Fintype X](ψ : G⧸N → X)(h : Function.Bijective ψ): Fintype.card (G ⧸ N) = Fintype.card X := by
  apply bijection_imp_eq_card (G⧸N)  X ψ G x h
  sorry


variable (X)
local notation "Φ" => Quotient <| orbitRel G X

lemma fin_μ  [Fintype G](μ: G ⧸ stabilizer G x → orbit G x): Fintype (Set.range μ) := by sorry

lemma fin_f [Fintype G]: Fintype (Set.range (f G x)) := by sorry


lemma orbit_eq_card (x:X)[Fintype G][Fintype X][MulAction G X][Fintype (G ⧸ stabilizer G x)][∀ x : X, Fintype <| stabilizer G x][Fintype (orbit G x)]:
Fintype.card (G)/ Fintype.card (stabilizer G x) = Fintype.card ↑(orbit G x) := by
  have h1 : Function.Bijective (f G x) := by apply orbit_bij
  have h2: Fintype.card (G)/ Fintype.card (stabilizer G x) = Fintype.card (G ⧸ stabilizer G x) := by apply quotient_order
  rw [h2]
  apply bijection_imp_eq_card (G ⧸ stabilizer G x) (orbit G x) (f G x) h1
  sorry

/-lemma hello : Fintype.card (orbit G x )= |G|/|stabilizer G x| := by sorry-/

/- # Part 3 -/


---lemma plswork : Cardinal.mk ↑(⋃ i, f i) = ∑'i, Nat.card f i := by sorry
open BigOperators

/-# Burnsides Lemma -/
def bjburnside : (Σg : G, fixedBy G g) ≃ (Prod Φ G) := by
  apply Equiv.ofBijective
  simp [Function.Bijective]
  sorry
  sorry

variable(S : Type)
theorem burnside [Fintype G][Fintype S][∀ g : G , Fintype <| fixedBy G g]:
(Fintype.card S / Fintype.card G) * Fintype.card G = (∑ g : G, Fintype.card (fixedBy G g)) := by sorry
