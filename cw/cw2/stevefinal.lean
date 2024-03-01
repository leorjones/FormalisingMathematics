import Mathlib.Tactic

namespace MyD₃

def mul : MyD₃ → MyD₃ → MyD₃
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

def one : MyD₃ := r 0

def inv : MyD₃ → MyD₃
  | r i => r (-i)
  | sr i => sr i

lemma D₃assoc (a b c : MyD₃) : mul (mul a  b)  c =  mul a  (mul b  c) := by
cases' a with a1 a2
cases' b with b1 b2
cases' c with c1 c2
simp [mul]
ring
simp [mul]
ring
cases' c with c1 c2
simp [mul]
ring
simp [mul]
ring
cases' b with b1 b2
cases' c with c1 c2
simp [mul]
ring
simp [mul]
ring
cases' c with c1 c2
simp [mul]
ring
simp [mul]
ring

lemma D₃one_mul (g : MyD₃): mul one g = g := by
cases' g with g1 g2
simp [one, mul]
simp [one, mul]

lemma D₃mul_one (g : MyD₃): mul g one  = g := by
cases' g with g1 g2
simp [one, mul]
simp [one, mul]

lemma D₃mul_left_inv (g : MyD₃) : mul (inv g) g = one := by
cases' g with g1 g2
simp [inv, mul, one]
simp [inv, mul, one]

instance : Group MyD₃ where
  mul := mul
  mul_assoc := by exact D₃assoc
  one := one
  one_mul := by exact D₃one_mul
  mul_one := by exact D₃mul_one
  inv := inv
  mul_left_inv := by exact D₃mul_left_inv

/- instance : Fintype MyD₃ where
  elems := {r 0, r 1, r 2, sr 0, sr 1, sr 2}
  complete := by
    intro x
    cases' x with a1 a2
    fin_cases a1
    simp
    simp
    simp
    right
    right
    rfl
    fin_cases a2
    simp
    simp
    aesop -/

/-Fintype.ofEquiv-/


lemma MyD₃_card : Fintype.card MyD₃ = 6 := by rfl

end MyD₃

variable (n : ℕ)

def n_set : Set ℕ := Finset.range n

variable (a1 a2 a3 b1 b2 b3 c1 : n_set n)
#check Set.pi (@Finset.univ (Fin 7) _).toSet (fun _ => n_set n)
def n7 := n_set (n) × n_set (n) × n_set (n) × n_set (n) ×  n_set (n) × n_set (n) × n_set (n)

def example_element : n7 n := (a1, a2, a3, b1, b2, b3, c1)

def rotation_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a3, a1, b2, b3, b1, c1)

def reflection_0_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a1, a3, a2, b3, b2, b1, c1)

def reflection_1_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a1, a3, b1, b3, b2, c1)

def reflection_2_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a3, a2, a1, b2, b1, b3, c1)

open MyD₃

def transform_action : MyD₃ → (n7 n → n7 n)
| r 0 => id
| r 1 => rotation_funct n
| r 2 => (rotation_funct n) ∘ (rotation_funct n)
| sr 0 => reflection_0_funct n
| sr 1 => reflection_1_funct n
| sr 2 => reflection_2_funct n

lemma identity_action (x : n7 n) : (transform_action n) (r 0) x = x := by exact rfl

lemma assoc_action (g₁ g₂ : MyD₃)(x : n7 n) :
(transform_action n) (g₁ * g₂) x = (transform_action n g₁) (transform_action n g₂ x) := by
cases' g₁ with a b
cases' g₂ with c d
sorry

instance : MulAction MyD₃ (n7 n) where
  smul := transform_action n
  one_smul := identity_action n
  mul_smul := assoc_action n

theorem trans_action_def (g : MyD₃)(x : n7 n): g • x = transform_action n g x := by rfl

local notation "Ψ" => Quotient <| orbitRel MyD₃ (n7 n)
variable (x : (n7 n))
variable[Fintype (MyD₃ ⧸ stabilizer MyD₃ x)][∀ x : (n7 n), Fintype <| stabilizer MyD₃ x][∀ x : (n7 n), Fintype (orbit MyD₃ x)][∀ g : MyD₃ , Fintype <| fixedBy (n7 n) g]
variable [Fintype Ψ][Fintype (n7 n)]

lemma r0_fixed : MulAction.fixedBy (n7 n) (r 0) = Set.univ := by
simp [MulAction.fixedBy]
have r0_id (y : n7 n) : r 0 • y = y := by rfl
simp_all

/-Issue due to n7 n being a type not a set-/
lemma r0_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 0)) = n^7 := by
rw [r0_fixed]
rw [Set.univ]
sorry

lemma r1_fix_demonstration (a1 b1 c1 : n_set n) : ((a1, a1, a1, b1, b1, b1, c1) : n7 n) ∈ MulAction.fixedBy (n7 n) (r 1) := by
simp [MulAction.fixedBy]
constructor

lemma r1_fixed : MulAction.fixedBy (n7 n) (r 1) =
{(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3}:= by
have form_imp_fix (x : n7 n) :
x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3} → x ∈ MulAction.fixedBy (n7 n) (r 1) := by
  intro hx
  refine MulAction.mem_fixedBy.mpr ?_
  sorry
have nform_imp_nfix (x : n7 n) :
 ¬ (x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3}) → ¬(x ∈ MulAction.fixedBy (n7 n) (r 1)) := by
  sorry
have form_iff_fix (x : n7 n) :
x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3} ↔ x ∈ MulAction.fixedBy (n7 n) (r 1) := by
  constructor
  exact form_imp_fix x
  contrapose
  exact nform_imp_nfix x
sorry

/-Issue due to n7 n being a type not a set-/
lemma r1_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 1)) = n^3 := by
rw [r1_fixed]
sorry

-- lemma r2_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 2)) = n^3 := by
-- sorry

-- lemma sr0_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 0)) = n^5 := by
-- sorry

-- lemma sr1_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 1)) = n^5 := by
-- sorry

-- lemma sr2_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 0)) = n^5 := by
-- sorry

lemma action_fix_sum  : ∑ g : MyD₃,  Fintype.card (MulAction.fixedBy (n7 n) g) = n^7 + 3*n^5 + 2*n^3 := by
sorry

theorem colouring_card [Fintype Ψ] : Fintype.card (Ψ) = (1/6)*(n^7 + 3*n^5 + 2*n^3) := by
rw [burnside_lemma]
rw [action_fix_sum]
/- have h: Fintype.card (MyD₃) = 6 := rfl -/
rw [MyD₃_card]
