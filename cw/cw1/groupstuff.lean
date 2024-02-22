import Mathlib.Tactic



-- ---first our homo
-- variable(φ : G →* H)

-- --then iso
-- variable(ψ : G ≃* H)

-- variable (G : Type) [Group G] (a b : G)
-- variable {G H} {x : G}

-- variable {y z : G}

-- theorem conjugate.one_mem : (1 : G) ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} :=  by
--   refine Set.mem_setOf.mpr ?_
--   use 1
--   rw[mul_one,mul_inv_self]
--   rw [propext (and_iff_left rfl)]
--   exact Subgroup.one_mem H

-- theorem conjugate.inv_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
--     y⁻¹ ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
--   cases' hy with p q
--   use p⁻¹
--   cases' q with a b
--   constructor
--   apply H.inv_mem
--   exact a
--   simp[b,mul_assoc]

-- theorem conjugate.mul_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹})
--     (hz : z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
--     y * z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
--   cases' hy with g pw
--   cases' pw with h f
--   cases' hz with k tt
--   cases' tt with b l
--   use g*k
--   constructor
--   apply H.mul_mem
--   exact h
--   exact b
--   simp[f,l]

-- def conjugate (H : Subgroup G) (x : G) : Subgroup G
--     where
--   carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
--   one_mem' := conjugate.one_mem
--   inv_mem' := conjugate.inv_mem
--   mul_mem' := conjugate.mul_mem


---fuck all that
---pls work

--- kerφ ◃ G
variable (G H: Type)[Group G][Group H]
variable {G H}
variable (φ : G →* H)



lemma mem_ker (φ: G →* H): x ∈ φ.ker ↔ φ x = 1 := by rfl

theorem normal_kernel (φ : G →* H) : Subgroup.Normal φ.ker := by
constructor
intros p q r
have h1 : φ (r * p * r⁻¹) = φ r * φ p * φ r⁻¹ := by repeat rw [φ.map_mul]
rw[mem_ker] at q
rw [q, mul_one, map_mul_eq_one φ] at h1
exact h1
apply mul_inv_self


--- G/ker subgroup

lemma issub(N : Subgroup G)[Subgroup.Normal N] : Subgroup (G⧸N) := by exact commutator (G ⧸ N)

---((a b : α) → a ≈ b → f a = f b) injectivity??

---equiv realtion
def ker_equiv {N : Subgroup G}[Subgroup.Normal N](a b : G):= a ∈ N ∧ b ∈ N
lemma ker_equiv_rel (N:Subgroup G)[Subgroup.Normal N]: equivalence (ker_equiv N):= by sorry



lemma boop (a b : G) (f : G →*H): (a ≈ b → f a = f b):= by sorry
---f.mem_ker.mp

lemma leftRel_appl  [Group G] {s : Subgroup G} {x y : G} :
  Setoid.r x y ↔ x⁻¹ * y ∈ s := by sorry


variable (N : Subgroup G)[Subgroup.Normal N]

def lift (φ : G →* H) (HN : N = φ.ker) : G⧸ N  →* H :=
  (QuotientGroup.con N).lift φ fun x y h => by
  ---simp [leftRel_apply] at h
  sorry


example (f: G →*H)(h: N = f.ker) : N ≤ f.ker := by exact Eq.le h


def qlift  [Group G] [Group H] {N : Subgroup G} [Subgroup.Normal N]
(f: G →* H)(h : N = f.ker) : G⧸N →* H :=
have h1 : N ≤ f.ker := Eq.le h
QuotientGroup.lift N f h1


def qlift2  [Group G] [Group H]
(f: G →* H) : G⧸f.ker →* H :=
---have h1 : N ≤ f.ker := Eq.le h
QuotientGroup.lift f.ker f (Eq.le rfl)

def qlift3  [Group G] [Group H] {N : Subgroup G} [Subgroup.Normal N]
(f: G →* H) (h1: ∀ x ∈ N, f x = 1): G⧸N →* H := by
 sorry



---def ψ :G/kerφ → φ(G)  := gkerφ↦φ(g)
def qgroup_lift [Group G] [Group H] {N : Subgroup G} [Subgroup.Normal N]
(f: G →* H) (h : N ≤  f.ker) (q : G ⧸ N) : H :=  QuotientGroup.lift N f h q

def qgroup_lift' [Group G] [Group H] {N : Subgroup G} [Subgroup.Normal N]
(f: G →* H) (h : ∀ n ∈ N, n ∈  f.ker) (q : G ⧸ N) : H :=  Quotient.lift f boop q

def im_lift3 (φ : G →* H)(φ': G⧸φ.ker →* H) : G⧸φ.ker →* φ.range :=  by
sorry

def im_lift (φ : G →* H)(a : G) : φ.range := by
exact Set.rangeFactorization (fun y => φ y) a

def im_lift2 (φ : G →* H)(a : G) : G→* φ.range := by
exact MonoidHom.rangeRestrict φ

theorem first_iso_thm (φ:G →* H) :  G⧸φ.ker ≃* φ.range := {
  toFun := im_lift3 φ (qlift2 φ)
  invFun := λb ↦ φ.inv b
  left_inv := sorry ---LeftInverse invFun toFun
  right_inv := sorry
  map_mul' := φ.map_mul
}


---⟨c, range_mem f c⟩

---check homo
---check inj
---check sur
 /--
 variable (φ: G→*H)
def lift (φ : G →* M) (HN : N ≤ φ.ker) : Q →* M :=
  (QuotientGroup.con N).lift φ fun x y h => by
    simp only [QuotientGroup.con, leftRel_apply, Con.rel_mk] at h
    rw [Con.ker_rel]
    calc
      φ x = φ (y * (x⁻¹ * y)⁻¹) := by rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
      _ = φ y := by rw [φ.map_mul, HN (N.inv_mem h), mul_one]


def rangeKerLift : G ⧸ φ.ker →* φ.range :=
  lift _ φ.rangeRestrict fun g hg => (mem_ker _).mp <| by rwa [ker_rangeRestrict]
#align quotient_group.range_ker_lift QuotientGroup.rangeKerLift
#align quotient_add_group.range_ker_lift QuotientAddGroup.rangeKerLift

 theorem first_iso_thm :  G⧸φ.ker ≃* φ.range :=
 MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩
#align quotient_group.quotient_ker_equiv_range QuotientGroup.quotientKerEquivRange
#align quotient_add_group.quotient_ker_equiv_range QuotientAddGroup.quotientKerEquivRange

 sorry

--/
