/- ### Hello Steve -/

import Mathlib.Tactic


variable (G H : Type)[Group G][MulAction G X] (x y z : X)
variable(H : Subgroup G)
variable {g : G}
/-variable {a b : G⧸ MulAction.stabilizer G x}-/
variable {a b : G}





open QuotientGroup MulAction


def φ (g : G ⧸ MulAction.stabilizer G x) : X :=
Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]

theorem φ_mk (g : G) : φ G x (QuotientGroup.mk g) = g • x :=
  rfl


lemma idyay : 1 = 1 := by rfl

/- ## Part 1-/

lemma hi :(φ G x a = φ G x b) → (a⁻¹*b ∈ MulAction.stabilizer G x):= by
intro p
repeat rw [φ_mk] at p
have  h: (a⁻¹ * b) • x = a⁻¹  • (b • x) := by rw [mul_smul a⁻¹ b x]
rw [← p, smul_smul a⁻¹ a x, inv_mul_self, one_smul] at h
exact h

example :  a • (b • x)=  (a * b) • x := by exact smul_smul a b x



theorem injective_φ : Function.Injective (φ G x) :=  by
  simp [Function.Injective]
  intros p q r
  obtain ⟨a, ha⟩ := Quot.exists_rep p
  obtain ⟨b, hb⟩ := Quot.exists_rep q
  have ha: ↑a = p := by exact ha
  have hb: ↑b = q := by exact hb
  have r2: φ G x ↑a = φ G x ↑b := by
    rw [←ha, ←hb] at r
    exact r
  apply hi at r2
  rw [←QuotientGroup.eq'] at r2
  rw [←ha, ←hb]
  exact r2

example (N : Subgroup G)[Subgroup.Normal N](n : G ⧸ N) := by exact X


---lemma range_φ : (φ G x).range = orbit G x := by sorry

theorem ofQuotientStabilizer_mem_orbit2 (g) : φ G x g ∈ orbit G x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩





def f : G ⧸ stabilizer G x → ↑(orbit G x):= fun g => ⟨φ G x g, ofQuotientStabilizer_mem_orbit2 G x g⟩

lemma hewwo :(Function.Injective (φ G x)) →  (Function.Injective (f G x)):= by
intro p
sorry

lemma surjective_φ: Function.Surjective (f G x) := by
simp[Function.Surjective]
intros p q
use a

sorry

noncomputable def orbit_stab_bij : ( G ⧸ stabilizer G x ≃ orbit G x) :=  by
apply Equiv.ofBijective
simp [Function.Bijective]
constructor
apply hewwo
apply injective_φ
apply surjective_φ
exact g

/- # Part 2-/

/-lemma hello : Fintype.card (orbit G x )= |G|/|stabilizer G x| := by sorry-/

/- # Part 3 -/
variable(n : Set u)

---lemma plswork : Cardinal.mk ↑(⋃ i, f i) = ∑'i, Nat.card f i := by sorry
